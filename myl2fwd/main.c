/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright(c) 2010-2016 Intel Corporation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_eal.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_string_fns.h>
#include <rte_ip.h>

static volatile bool force_quit;

/* MAC updating enabled by default */
static int mac_updating = 1;

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define MAX_PKT_BURST 32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 256

/* configure timestamp */
unsigned hw_timestamping = 0;
static int hwts_dynfield_offset = -1;

static inline rte_mbuf_timestamp_t * hwts_field(struct rte_mbuf *mbuf)
{
	return RTE_MBUF_DYNFIELD(mbuf, hwts_dynfield_offset, rte_mbuf_timestamp_t *);
}

typedef uint64_t tsc_t;
//static int tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + 1;
//static int tsc_dynfield_offset = -1;
//static int tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr);

static inline tsc_t * tsc_field(struct rte_mbuf *mbuf, int tsc_dynfield_offset)
{
	//return RTE_MBUF_DYNFIELD(mbuf, tsc_dynfield_offset, tsc_t *);
	struct rte_ether_hdr *eth_hdr;
	eth_hdr = rte_pktmbuf_mtod(mbuf, struct rte_ether_hdr *);
	void *p = (struct rte_mbuf *)(eth_hdr);
	return RTE_MBUF_DYNFIELD(p, tsc_dynfield_offset, tsc_t *);
}

static struct {
	uint64_t total_cycles;
	uint64_t total_queue_cycles;
	uint64_t total_pkts;
	uint64_t latency;
} latency_numbers;

/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 1024
#define RTE_TEST_TX_DESC_DEFAULT 1024
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;

/* ethernet addresses of ports */
static struct rte_ether_addr l2fwd_ports_eth_addr[RTE_MAX_ETHPORTS];

/* mask of enabled ports */
static uint32_t l2fwd_enabled_port_mask = 0;

/* list of enabled ports */
static uint32_t l2fwd_dst_ports[RTE_MAX_ETHPORTS];

struct port_pair_params {
#define NUM_PORTS	2
	uint16_t port[NUM_PORTS];
} __rte_cache_aligned;

static struct port_pair_params port_pair_params_array[RTE_MAX_ETHPORTS / 2];
static struct port_pair_params *port_pair_params;
static uint16_t nb_port_pair_params;

static unsigned int l2fwd_rx_queue_per_lcore = 1;

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16
struct lcore_queue_conf {
	unsigned n_rx_port;
	unsigned rx_port_list[MAX_RX_QUEUE_PER_LCORE];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];

static struct rte_eth_dev_tx_buffer *tx_buffer[RTE_MAX_ETHPORTS];

static struct rte_eth_conf port_conf = {
	.rxmode = {
		.split_hdr_size = 0,
	},
	.txmode = {
		.mq_mode = ETH_MQ_TX_NONE,
	},
};

struct rte_mempool * l2fwd_pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct l2fwd_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
	uint64_t tx_bytes;
	uint64_t rx_bytes;
	uint64_t tx_error;
	uint64_t rx_error;
	uint64_t tx_burst;
	uint64_t rx_burst;
	uint16_t ether_type;
	uint16_t vlan_tag;
	uint16_t vlan_id;
	uint16_t vlan_priority;
	struct rte_ether_addr d_addr;
	struct rte_ether_addr s_addr;
	uint32_t pkt_length;
	uint16_t data_len;
	char ip_protocol[6];
	unsigned char ip_s_addr[4];
	unsigned char ip_d_addr[4];
	int64_t jitter_ns;
	double latency_us;
	uint64_t timestamp;
} __rte_cache_aligned;

struct l2fwd_port_statistics port_statistics[RTE_MAX_ETHPORTS];

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 10; /* default period is 10 seconds */


static void intercept_packets(struct rte_mbuf *m, unsigned portid);
#define VLAN_ID 10

/* set src MAC and IP address */
/* 01:02:03:04:05:07 */
static struct rte_ether_addr src_ether_addr = {{0x01, 0x02, 0x03, 0x04, 0x05, 0x07}};
static uint32_t src_ip_addr = RTE_IPV4(172,16,155,131);

/* set dst MAC and IP address */
/* 01:02:03:04:05:06 */
static struct rte_ether_addr dst_ether_addr = {{0x01, 0x02, 0x03, 0x04, 0x05, 0x06}};
static uint32_t dst_ip_addr = RTE_IPV4(172,16,155,132);

static uint16_t cfg_udp_src = 1000;
static uint16_t cfg_udp_dst = 1001;

static unsigned rx_only_flag = 0;
static unsigned tx_only_flag = 0;
static unsigned l2fwd_flag = 0;
static unsigned debug_flag = 0;
static unsigned vlan_flag = 0;
static unsigned txrx_flag = 0;

/* number of packets, default is 0 mean infinite*/
static uint64_t nb_pkts = 32;

static void drop_packet(struct rte_mbuf *m, unsigned portid, unsigned nb_rx);
static inline uint16_t ip_sum(const unaligned_uint16_t *hdr, int hdr_len);
static void hex_dumps(struct rte_mbuf *m, unsigned portid);
uint64_t bytes_to_uint64_t(unsigned char *byte, unsigned offset);
static void calculate_latency(struct rte_mbuf *m, unsigned portid, unsigned nb_pkts);

#define TICKS_PER_CYCLE_SHIFT 16
static uint64_t ticks_per_cycle_mult;

static uint16_t add_timestamps_tx_cycle(uint16_t portid, uint16_t qidx __rte_unused,
                struct rte_mbuf **pkts, uint16_t nb_pkts, void *_ __rte_unused)
{
	unsigned i;
	uint64_t now = rte_rdtsc();
	int tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr);

	for (i = 0; i < nb_pkts; i++) {
		*tsc_field(pkts[i], tsc_dynfield_offset) = now;
		port_statistics[portid].timestamp = now;
	}
	return nb_pkts;
}

static uint16_t add_timestamps_tx(uint16_t portid, uint16_t qidx __rte_unused,
                struct rte_mbuf **pkts, uint16_t nb_pkts, void *_ __rte_unused)
{
        struct timespec t_tx;
	clock_gettime(CLOCK_MONOTONIC_RAW, &t_tx);
	uint64_t now = t_tx.tv_nsec;
	unsigned i;
	int tsc_dynfield_offset;

	if (vlan_flag)
		tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr) + 4;
	else
		tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr);

        for (i = 0; i < nb_pkts; i++) {
                *tsc_field(pkts[i], tsc_dynfield_offset) = now;
                port_statistics[portid].timestamp = now;
        }
        return nb_pkts;
}

static uint16_t add_timestamps(uint16_t portid __rte_unused, uint16_t qidx __rte_unused,
		struct rte_mbuf **pkts, uint16_t nb_pkts,
		uint16_t max_pkts __rte_unused, void *_ __rte_unused)
{
	unsigned i;
	uint64_t now = rte_rdtsc();
	int tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr) + 8;

	for (i = 0; i < nb_pkts; i++) {
		*tsc_field(pkts[i], tsc_dynfield_offset) = now;
		port_statistics[portid].timestamp = now;
	}
	return nb_pkts;
}

/*
static uint16_t calc_latency(uint16_t portid, uint16_t qidx __rte_unused,
		struct rte_mbuf **pkts, uint16_t nb_pkts, void *_ __rte_unused)
{
	uint64_t cycles = 0;
	uint64_t queue_ticks = 0;
	uint64_t now = rte_rdtsc();
	uint64_t ticks;
	unsigned i;

	if (hw_timestamping)
		rte_eth_read_clock(portid, &ticks);

	for (i = 0; i < nb_pkts; i++) {
		cycles += now - *tsc_field(pkts[i]);
		if (hw_timestamping)
			queue_ticks += ticks - *hwts_field(pkts[i]);
	}

	latency_numbers.total_cycles += cycles;
	if (hw_timestamping)
		latency_numbers.total_queue_cycles += (queue_ticks
			* ticks_per_cycle_mult) >> TICKS_PER_CYCLE_SHIFT;

	latency_numbers.total_pkts += nb_pkts;

	if (latency_numbers.total_pkts > (100 * 1000 * 1000ULL)) {
		port_statistics[portid].latency = latency_numbers.total_cycles / latency_numbers.total_pkts;
		if (hw_timestamping) {
			port_statistics[portid].timestamp = latency_numbers.total_queue_cycles / latency_numbers.total_pkts;
		}
		latency_numbers.total_cycles = 0;
		latency_numbers.total_queue_cycles = 0;
		latency_numbers.total_pkts = 0;
	}
	return nb_pkts;
}
*/

static uint16_t calc_latency_cycle(uint16_t portid __rte_unused, uint16_t qidx __rte_unused,
                struct rte_mbuf **pkts, uint16_t nb_pkts,
                uint16_t max_pkts __rte_unused, void *_ __rte_unused)
{
	/* not valid to use cycle time i.e. rte_rdtsc() if the tx and rx have different frequency.
	 * timestamp should get from gettimeofday?
	 */
        uint64_t cycles = 0;
        uint64_t queue_ticks = 0;
        uint64_t now = rte_rdtsc();
        uint64_t latency_cycles;
        unsigned i;
	int tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr);

        for (i = 0; i < nb_pkts; i++) {
                cycles += now - *tsc_field(pkts[i], tsc_dynfield_offset);
        }

        latency_numbers.total_cycles += cycles;
        latency_numbers.total_pkts += nb_pkts;
	/* latency in cycles */
	latency_cycles = latency_numbers.total_cycles / latency_numbers.total_pkts;
	/* convert latency to microseconds, us */
	port_statistics[portid].latency_us = ((double)latency_cycles / (double)rte_get_timer_hz()) * 1000000;

	if (latency_numbers.total_pkts > (100 * 1000 * 1000ULL)) {
		latency_numbers.total_cycles = 0;
                latency_numbers.total_queue_cycles = 0;
                latency_numbers.total_pkts = 0;
	}

        return nb_pkts;
}

static uint16_t calc_latency1(uint16_t portid __rte_unused, uint16_t qidx __rte_unused,
                struct rte_mbuf **pkts, uint16_t nb_pkts,
                uint16_t max_pkts __rte_unused, void *_ __rte_unused)
{
        /* not valid to use cycle time i.e. rte_rdtsc() if the tx and rx have different frequency.
         * timestamp should get from gettimeofday?
         */
        struct timespec t_rx;
	uint64_t now = 0;
	uint64_t cycles = 0;
        uint64_t latency_cycles = 0;
        unsigned i;
	double latency_us = 0;
	int64_t jitter;
        int tsc_dynfield_offset;

	if (vlan_flag)
		tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr) + 4;
	else
		tsc_dynfield_offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr);

	if (likely(nb_pkts == 0))
		return 0;

        for (i = 0; i < nb_pkts; i++) {
		clock_gettime(CLOCK_MONOTONIC_RAW, &t_rx);
		now = t_rx.tv_nsec;
		/* rx timestamp might overflow and reset to 0. This cause the diff spike to huge.
		 * skip calculate latency */
		if (unlikely(*tsc_field(pkts[i], tsc_dynfield_offset) > now))
			return 0;

                cycles += now - *tsc_field(pkts[i], tsc_dynfield_offset);
		port_statistics[portid].timestamp = now;
        }

        latency_numbers.total_cycles += cycles;
        latency_numbers.total_pkts += nb_pkts;

        /* latency in nanoseconds */
        latency_cycles = latency_numbers.total_cycles / latency_numbers.total_pkts;

        /* convert latency to microseconds, us */
	latency_us = (double)latency_cycles / 1000;
	port_statistics[portid].latency_us = latency_us;

	/* calculate jitter. jitter is difference in latency */
	//jitter = ((double)latency_numbers.latency - (double)latency_cycles);
	jitter = latency_numbers.latency - latency_cycles;
	if (jitter != 0)
		port_statistics[portid].jitter_ns = abs(jitter);

	latency_numbers.latency = latency_cycles;

        if (latency_numbers.total_pkts > (100 * 1000 * 1000ULL)) {
                latency_numbers.total_cycles = 0;
                latency_numbers.total_pkts = 0;
        }

        return nb_pkts;
}


static void print_stats(void)
{
	uint64_t total_packets_dropped, total_packets_tx, total_packets_rx;
        unsigned portid;

        total_packets_dropped = 0;
        total_packets_tx = 0;
        total_packets_rx = 0;

        const char clr[] = { 27, '[', '2', 'J', '\0' };
        const char topLeft[] = { 27, '[', '1', ';', '1', 'H','\0' };

                /* Clear screen and move to top left */
        printf("%s%s", clr, topLeft);

	printf("\nPort statistics ====================================");

	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++) {
                /* skip disabled ports */
                if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
                        continue;

                printf("\nStatistics for port %u ------------------------------", portid);
		printf("\nMAC Address: %02X:%02X:%02X:%02X:%02X:%02X",
			l2fwd_ports_eth_addr[portid].addr_bytes[0],
			l2fwd_ports_eth_addr[portid].addr_bytes[1],
			l2fwd_ports_eth_addr[portid].addr_bytes[2],
			l2fwd_ports_eth_addr[portid].addr_bytes[3],
			l2fwd_ports_eth_addr[portid].addr_bytes[4],
			l2fwd_ports_eth_addr[portid].addr_bytes[5]);
		printf("\nPackets Tx/Rx:       %18"PRIu64"/%"PRIu64,
			port_statistics[portid].tx, port_statistics[portid].rx);
		printf("\nPackets dropped:     %18"PRIu64,
			port_statistics[portid].dropped);
		printf("\nPackets Tx/Rx burst: %18"PRIu64"/%"PRIu64,
			port_statistics[portid].tx_burst, port_statistics[portid].rx_burst);
		printf("\nPkts Bytes Tx/Rx:    %18"PRIu64"/%"PRIu64,
			port_statistics[portid].tx_bytes, port_statistics[portid].rx_bytes);
		printf("\nPkts error Tx/Rx:    %18"PRIu64"/%"PRIu64,
			port_statistics[portid].tx_error, port_statistics[portid].rx_error);
		printf("\nSrc MAC Address: %02X:%02X:%02X:%02X:%02X:%02X",
			port_statistics[portid].s_addr.addr_bytes[0],
			port_statistics[portid].s_addr.addr_bytes[1],
			port_statistics[portid].s_addr.addr_bytes[2],
			port_statistics[portid].s_addr.addr_bytes[3],
			port_statistics[portid].s_addr.addr_bytes[4],
			port_statistics[portid].s_addr.addr_bytes[5]);
		printf("\nDst MAC Address: %02X:%02X:%02X:%02X:%02X:%02X",
			port_statistics[portid].d_addr.addr_bytes[0],
			port_statistics[portid].d_addr.addr_bytes[1],
			port_statistics[portid].d_addr.addr_bytes[2],
			port_statistics[portid].d_addr.addr_bytes[3],
			port_statistics[portid].d_addr.addr_bytes[4],
			port_statistics[portid].d_addr.addr_bytes[5]);
		printf("\nEther Type:          %18"PRIx16, port_statistics[portid].ether_type);
		printf("\nVLAN ID:             %18"PRIu16, port_statistics[portid].vlan_id);
		printf("\nVLAN Priority:       %18"PRIu16, port_statistics[portid].vlan_priority);
		printf("\nPacket Lenght:       %18"PRIu32, port_statistics[portid].pkt_length);
		printf("\nData Length:         %18"PRIu16, port_statistics[portid].data_len);
		printf("\nIP Protocol:         %18s", port_statistics[portid].ip_protocol);
		printf("\nSrc IP Address: %d.%d.%d.%d",
			port_statistics[portid].ip_s_addr[0],
			port_statistics[portid].ip_s_addr[1],
			port_statistics[portid].ip_s_addr[2],
			port_statistics[portid].ip_s_addr[3]);
		printf("\nDst IP Address: %d.%d.%d.%d",
			port_statistics[portid].ip_d_addr[0],
			port_statistics[portid].ip_d_addr[1],
			port_statistics[portid].ip_d_addr[2],
			port_statistics[portid].ip_d_addr[3]);
		printf("\nSW Jitter (ns)       %18ld", port_statistics[portid].jitter_ns);
		printf("\nSW Latency (us):     %18.2f", port_statistics[portid].latency_us);
		printf("\nSW timestamp (ns):   %18"PRIu64, port_statistics[portid].timestamp);

		total_packets_dropped += port_statistics[portid].dropped;
                total_packets_tx += port_statistics[portid].tx;
                total_packets_rx += port_statistics[portid].rx;
        }
        printf("\nAggregate statistics ==============================="
                   "\nTotal packets sent:      %14"PRIu64
                   "\nTotal packets received:  %14"PRIu64
                   "\nTotal packets dropped:   %14"PRIu64,
                   total_packets_tx,
                   total_packets_rx,
                   total_packets_dropped);
        printf("\n====================================================\n");

	fflush(stdout);
}


/* Print out statistics on packets dropped */
static void
print_stats1(void)
{
	uint64_t total_packets_dropped, total_packets_tx, total_packets_rx;
	unsigned portid;

	total_packets_dropped = 0;
	total_packets_tx = 0;
	total_packets_rx = 0;

	const char clr[] = { 27, '[', '2', 'J', '\0' };
	const char topLeft[] = { 27, '[', '1', ';', '1', 'H','\0' };

		/* Clear screen and move to top left */
	printf("%s%s", clr, topLeft);

	printf("\nPort statistics ====================================");

	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++) {
		/* skip disabled ports */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		printf("\nStatistics for port %u ------------------------------"
			"\nMAC Address: %02X:%02X:%02X:%02X:%02X:%02X"
			   "\nPackets sent: %24"PRIu64
			   "\nPackets received: %20"PRIu64
			   "\nPackets dropped: %21"PRIu64
			   "\nPackets sent burst: %18"PRIu64
			   "\nPackets received burst: %14"PRIu64
			   "\nPackets transmit error: %14"PRIu64
			   "\nPackets received error: %14"PRIu64
			   "\nPackets transmit bytes: %14"PRIu64
			   "\nPackets received bytes: %14"PRIu64
			   "\nSrc MAC Address: %02X:%02X:%02X:%02X:%02X:%02X"
			   "\nDst MAC Address: %02X:%02X:%02X:%02X:%02X:%02X"
			   "\nEther type: %26"PRIx16
			   "\nVlan tag:   %26"PRIx16
			   "\nVlan ID:    %26"PRIu16
			   "\nVlan Priority: %23"PRIu16
			   "\nPacket length: %23"PRIu32
			   "\nData length: %25"PRIu16
			   "\nIP Protocol: %25s"
			   "\nSrc IP Address: %d.%d.%d.%d"
			   "\nDst IP Address: %d.%d.%d.%d"
			   "\nSW Jitter (ns):   %20ld"
			   "\nSW Latency (us):  %20.2f"
			   "\nSW timestamp: %24"PRIu64,
			   portid,
			   l2fwd_ports_eth_addr[portid].addr_bytes[0],
                           l2fwd_ports_eth_addr[portid].addr_bytes[1],
                           l2fwd_ports_eth_addr[portid].addr_bytes[2],
                           l2fwd_ports_eth_addr[portid].addr_bytes[3],
                           l2fwd_ports_eth_addr[portid].addr_bytes[4],
                           l2fwd_ports_eth_addr[portid].addr_bytes[5],
			   port_statistics[portid].tx,
			   port_statistics[portid].rx,
			   port_statistics[portid].dropped,
			   port_statistics[portid].tx_burst,
			   port_statistics[portid].rx_burst,
			   port_statistics[portid].tx_error,
			   port_statistics[portid].rx_error,
			   port_statistics[portid].tx_bytes,
			   port_statistics[portid].rx_bytes,
			   port_statistics[portid].s_addr.addr_bytes[0],
			   port_statistics[portid].s_addr.addr_bytes[1],
			   port_statistics[portid].s_addr.addr_bytes[2],
			   port_statistics[portid].s_addr.addr_bytes[3],
			   port_statistics[portid].s_addr.addr_bytes[4],
			   port_statistics[portid].s_addr.addr_bytes[5],
			   port_statistics[portid].d_addr.addr_bytes[0],
			   port_statistics[portid].d_addr.addr_bytes[1],
			   port_statistics[portid].d_addr.addr_bytes[2],
			   port_statistics[portid].d_addr.addr_bytes[3],
			   port_statistics[portid].d_addr.addr_bytes[4],
			   port_statistics[portid].d_addr.addr_bytes[5],
			   port_statistics[portid].ether_type,
			   port_statistics[portid].vlan_tag,
			   port_statistics[portid].vlan_id,
			   port_statistics[portid].vlan_priority,
			   port_statistics[portid].pkt_length,
			   port_statistics[portid].data_len,
			   port_statistics[portid].ip_protocol,
			   port_statistics[portid].ip_s_addr[0],
			   port_statistics[portid].ip_s_addr[1],
			   port_statistics[portid].ip_s_addr[2],
			   port_statistics[portid].ip_s_addr[3],
			   port_statistics[portid].ip_d_addr[0],
                           port_statistics[portid].ip_d_addr[1],
                           port_statistics[portid].ip_d_addr[2],
                           port_statistics[portid].ip_d_addr[3],
			   port_statistics[portid].jitter_ns,
			   port_statistics[portid].latency_us,
			   port_statistics[portid].timestamp
				   );

		total_packets_dropped += port_statistics[portid].dropped;
		total_packets_tx += port_statistics[portid].tx;
		total_packets_rx += port_statistics[portid].rx;
	}
	printf("\nAggregate statistics ==============================="
		   "\nTotal packets sent: %18"PRIu64
		   "\nTotal packets received: %14"PRIu64
		   "\nTotal packets dropped: %15"PRIu64,
		   total_packets_tx,
		   total_packets_rx,
		   total_packets_dropped);
	printf("\n====================================================\n");

	fflush(stdout);
}

static void
l2fwd_mac_updating(struct rte_mbuf *m, unsigned dest_portid)
{
	struct rte_ether_hdr *eth;
	void *tmp;

	eth = rte_pktmbuf_mtod(m, struct rte_ether_hdr *);

	/* 02:00:00:00:00:xx */
	tmp = &eth->d_addr.addr_bytes[0];
	*((uint64_t *)tmp) = 0x000000000002 + ((uint64_t)dest_portid << 40);

	/* src addr */
	rte_ether_addr_copy(&l2fwd_ports_eth_addr[dest_portid], &eth->s_addr);
}

static void
l2fwd_simple_forward(struct rte_mbuf *m, unsigned portid)
{
	unsigned dst_port;
	int sent;
	struct rte_eth_dev_tx_buffer *buffer;

	dst_port = l2fwd_dst_ports[portid];

	if (mac_updating)
		l2fwd_mac_updating(m, dst_port);

	buffer = tx_buffer[dst_port];
	sent = rte_eth_tx_buffer(dst_port, 0, buffer, m);
	if (sent)
		port_statistics[dst_port].tx += sent;
}


static struct rte_mbuf *construct_packet(unsigned portid)
{
	unsigned pkt_size = 64U;
	struct rte_mbuf *pkt;
	struct rte_ether_hdr *eth_hdr;
	struct rte_ipv4_hdr *ip_hdr;
	struct rte_udp_hdr *udp_hdr;

	/* allocate a new mbuf from l2fwd_pktmbuf_pool memory pool */
	pkt = rte_pktmbuf_alloc(l2fwd_pktmbuf_pool);
	if (!pkt)
		rte_exit(EXIT_FAILURE, "failed to allocate mbuf for packet");

	pkt->data_len = pkt_size;
	pkt->next = NULL;

	/* initialize ethernet header */
	eth_hdr = rte_pktmbuf_mtod(pkt, struct rte_ether_hdr *);
	rte_ether_addr_copy(&dst_ether_addr, &eth_hdr->d_addr);
	rte_ether_addr_copy(&src_ether_addr, &eth_hdr->s_addr);

	/* get mac address as src MAC */
	//rte_eth_macaddr_get(portid, &eth_hdr->s_addr);

	/* standard ethernet type 802.3 */
	eth_hdr->ether_type = rte_cpu_to_be_16(RTE_ETHER_TYPE_IPV4);

	/* initialize IP header */
	ip_hdr = (struct rte_ipv4_hdr *)(eth_hdr + 1);
	memset(ip_hdr, 0, sizeof((struct rte_ipv4_hdr *)ip_hdr));
	ip_hdr->version_ihl = RTE_IPV4_VHL_DEF;
	ip_hdr->type_of_service = 0;
	ip_hdr->fragment_offset = 0;
	ip_hdr->time_to_live = 3;
	ip_hdr->next_proto_id = IPPROTO_UDP;
	ip_hdr->packet_id = 0;
	ip_hdr->src_addr = rte_cpu_to_be_32(src_ip_addr);
	ip_hdr->dst_addr = rte_cpu_to_be_32(dst_ip_addr);
	ip_hdr->total_length = rte_cpu_to_be_16(pkt_size - sizeof((struct rte_ether_hdr *)eth_hdr));
	/* calculate checksum on l3 using software */
	//ip_hdr->hdr_checksum = ip_sum((unaligned_uint16_t *)ip_hdr, sizeof(*ip_hdr));

	/* offload checksum on l3 using NIC */
	if (pkt->ol_flags & PKT_TX_IPV4)
	{
		ip_hdr->hdr_checksum = 0;
		pkt->ol_flags = PKT_TX_IPV4 | PKT_TX_IP_CKSUM | PKT_TX_UDP_CKSUM;
	}

	/* initialize UDP header */
	udp_hdr = (struct rte_udp_hdr *)(ip_hdr + 1);
	udp_hdr->src_port = rte_cpu_to_be_16(cfg_udp_src);
	udp_hdr->dst_port = rte_cpu_to_be_16(cfg_udp_dst);
	udp_hdr->dgram_cksum = 0; // no UDP checksum
	udp_hdr->dgram_len = rte_cpu_to_be_16(pkt_size - sizeof((struct rte_ether_hdr *)eth_hdr) - sizeof((struct rte_ipv4_hdr *)ip_hdr));

	/* fill the data in the packet */
        char priv_data[] = "abcdefghijklmnopqrstuvwxyz1234567890;:',<>/?{}[]!@#$%^&*()_+-=~`";
	void *p;
	p = (struct rte_udp_hdr *)(udp_hdr + 1);
	strcpy(p, priv_data);

	pkt->nb_segs = 1;
	pkt->pkt_len = pkt_size;
	pkt->l2_len = sizeof((struct rte_ether_hdr *)eth_hdr);
	pkt->l3_len = sizeof((struct rte_ipv4_hdr *)ip_hdr);
	pkt->l4_len = sizeof((struct rte_udp_hdr *)udp_hdr);

	if (vlan_flag) {

		/* vlan ethernet type 802.1q */
		/* we create TSN packet using Vlan tag with highest priority */

		struct rte_vlan_hdr *vh;
		/* Priority code point 7 (highest), 0 (default) */
		uint16_t vlan_priority = 7; /* 0xE */
		uint16_t vlan_id = 1000; /* 0x03E8 */
                uint16_t vlan_tag = (vlan_priority << 13) | vlan_id;
                uint16_t vlan_tag_be = rte_cpu_to_be_16(vlan_tag);
		struct rte_ether_hdr *oh, *nh;

		oh = rte_pktmbuf_mtod(pkt, struct rte_ether_hdr *);

		nh = (struct rte_ether_hdr *)rte_pktmbuf_prepend(pkt, sizeof(struct rte_vlan_hdr));
		memmove(nh, oh, 2 * RTE_ETHER_ADDR_LEN);
		nh->ether_type = rte_cpu_to_be_16(RTE_ETHER_TYPE_VLAN);

		vh = (struct rte_vlan_hdr *) (nh + 1);
		vh->vlan_tci = vlan_tag_be;

		pkt->pkt_len = pkt_size + sizeof(struct rte_vlan_hdr);
	}

	return pkt;
}

static inline uint16_t ip_sum(const unaligned_uint16_t *hdr, int hdr_len)
{
	uint32_t sum = 0;

	while (hdr_len > 1)
	{
		sum += *hdr++;
		if (sum & 0x80000000)
			sum = (sum & 0xFFFF) + (sum >> 16);
		hdr_len -= 2;
	}

	while (sum >> 16)
		sum = (sum & 0xFFFF) + (sum >> 16);
	return ~sum;
}

static void hex_dumps(struct rte_mbuf *m, unsigned portid)
{
	unsigned char *p = rte_pktmbuf_mtod(m, unsigned char *);
	unsigned i, j;

	j = 0;
	for (i = 0; i < m->pkt_len; i++) {
		if ( j == 15) {
			printf("\n");
			j = 0;
		}
		printf("%02x ", ((*p) & 0xffff));
		p++;
		j++;
	}
	printf("\n\n");
}

static void rx_only(void)
{
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
	unsigned i, j, portid, nb_rx;
	unsigned lcore_id;
	struct lcore_queue_conf *qconf;
	uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;
	struct rte_eth_stats eth_rx_stats;
	unsigned nb_rx_actual;

	lcore_id = rte_lcore_id();
	qconf = &lcore_queue_conf[lcore_id];

	portid = qconf->rx_port_list[0];

	prev_tsc = 0;
        timer_tsc = 0;

	while (!force_quit)
	{
		cur_tsc = rte_rdtsc();
                diff_tsc = cur_tsc - prev_tsc;

		for (i = 0; i < qconf->n_rx_port; i++) {
			nb_rx = rte_eth_rx_burst(portid, 0, pkts_burst, MAX_PKT_BURST);
			nb_rx_actual = rte_eth_stats_get(portid, &eth_rx_stats);

                        if (nb_rx_actual == 0) {
				port_statistics[portid].tx = eth_rx_stats.opackets;
                                port_statistics[portid].rx = eth_rx_stats.ipackets;
                                port_statistics[portid].dropped = eth_rx_stats.imissed;
                                port_statistics[portid].tx_bytes = eth_rx_stats.obytes;
                                port_statistics[portid].rx_bytes = eth_rx_stats.ibytes;
                        }
                        else {
                                port_statistics[portid].tx_error = eth_rx_stats.oerrors;
                                port_statistics[portid].rx_error = eth_rx_stats.ierrors;
                        }

			if (unlikely(nb_rx == 0))
				continue;

			for (j = 0; j < nb_rx; j++) {
				m = pkts_burst[j];

				struct rte_ether_hdr *eth_hdr;
				eth_hdr = rte_pktmbuf_mtod(m, struct rte_ether_hdr *);
				uint16_t ether_type = rte_cpu_to_be_16(eth_hdr->ether_type);

				intercept_packets(m, portid);
				if (ether_type == RTE_ETHER_TYPE_VLAN) {
					/* drop vlan packet */
					port_statistics[portid].dropped += 1;
				}
				else {
					//rte_prefetch0(rte_pktmbuf_mtod(m, void *));
					//port_statistics[portid].rx += 1;
					port_statistics[portid].rx_burst = 1;
				}
				// free up the mbuf so the it can received another packet
                                rte_pktmbuf_free(m);
			}
		}


		/* if timer is enabled */
		if (timer_period > 0) {
			/* advance the timer */
			timer_tsc += diff_tsc;

			/* if timer has reached its timeout */
			if (unlikely(timer_tsc >= timer_period)) {
				/* do this only on main core */
				if (lcore_id == rte_get_main_lcore()) {
					print_stats();
					/* reset the timer */
					timer_tsc = 0;
				}
			}
		}
		prev_tsc = cur_tsc;
	}
}

static void drop_packet(struct rte_mbuf *m, unsigned portid, unsigned nb_rx)
{
	struct rte_ether_hdr *eth_hdr;
	eth_hdr = rte_pktmbuf_mtod(m, struct rte_ether_hdr *);
	uint16_t ether_type = rte_cpu_to_be_16(eth_hdr->ether_type);

	if (ether_type == RTE_ETHER_TYPE_VLAN) {
		/* drop vlan packet */
		port_statistics[portid].dropped += nb_rx;
	}

}

static void txrx1(void)
{
	/* WIP: each port can transmit and received */

	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
        uint64_t pkt_idx = 0;

        unsigned lcore_id;
        unsigned i, j, portid, nb_tx, nb_rx;
        int nb_tx_actual;
        struct rte_eth_stats eth_stats;
        struct lcore_queue_conf *qconf;
        uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;
	const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S *
                        BURST_TX_DRAIN_US;

        lcore_id = rte_lcore_id();
        qconf = &lcore_queue_conf[lcore_id];

        prev_tsc = 0;
        timer_tsc = 0;

        if (qconf->n_rx_port == 0) {
                RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
                return;
        }

        RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

        for (i = 0; i < qconf->n_rx_port; i++) {

                portid = qconf->rx_port_list[i];
                RTE_LOG(INFO, L2FWD, " -- lcoreid=%u portid=%u\n", lcore_id,
                        portid);

        }

	m = construct_packet(portid);
	if (m == NULL)
		rte_exit(EXIT_FAILURE, "failed to construct packet");

        while (!force_quit) {
                cur_tsc = rte_rdtsc();
                diff_tsc = cur_tsc - prev_tsc;

		if (unlikely(diff_tsc > drain_tsc)) {
			for (i = 0; i < qconf->n_rx_port; i++) {
				portid = l2fwd_dst_ports[qconf->rx_port_list[i]];
			// handle to transmit packet on port 0
			//portid = 0;

			nb_tx = rte_eth_tx_burst(portid, 0, &m, 1);
			if (nb_tx) {
				port_statistics[portid].tx += nb_tx;
				port_statistics[portid].tx_burst = nb_tx;
				//hex_dumps(m, portid);
				intercept_packets(m, portid);
				// free up the mbuf so the it can transmit another packet
				rte_pktmbuf_free(m);
			}
			}
			// if timer is enabled
			if (timer_period > 0) {
				// advance the timer
				timer_tsc += diff_tsc;

				// if timer has reached its timeout
				if (unlikely(timer_tsc >= timer_period)) {
					// do this only on main core
					if (lcore_id == rte_get_main_lcore()) {
						print_stats();
						// reset the timer
						timer_tsc = 0;
					}
				}
			}
			prev_tsc = cur_tsc;
		}

		for (i = 0; i < qconf->n_rx_port; i++) {
			portid = qconf->rx_port_list[i];
		// handle for received packet on port 1
		//portid = 1;
		nb_rx = rte_eth_rx_burst(portid, 0, pkts_burst, MAX_PKT_BURST);
		if (unlikely(nb_rx == 0))
			continue;

		for (j = 0; j < nb_rx; j++) {
			m = pkts_burst[j];
			struct rte_ether_hdr *eth_hdr;
			eth_hdr = rte_pktmbuf_mtod(m, struct rte_ether_hdr *);
			uint16_t ether_type = rte_cpu_to_be_16(eth_hdr->ether_type);
			intercept_packets(m, portid);
			rte_prefetch0(rte_pktmbuf_mtod(m, void *));
			port_statistics[portid].rx += 1;
			port_statistics[portid].rx_burst = 1;
			// free up the mbuf so the it can received another packet
			rte_pktmbuf_free(m);
		}
		}

        }
}

static void txrx(void)
{
        /* WIP: port 0 tx, port 1 rx */

        struct rte_mbuf *rx_pkts_burst[MAX_PKT_BURST];
        struct rte_mbuf *tx_pkt;
	struct rte_mbuf *rx_pkt;
        uint64_t pkt_idx = 0;

        unsigned lcore_id;
        unsigned i, j, portid, nb_tx, nb_rx;
        struct lcore_queue_conf *qconf;
        uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;
        const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S *
                        BURST_TX_DRAIN_US;

	unsigned nb_tx_actual, nb_rx_actual;
        struct rte_eth_stats eth_tx_stats;
	struct rte_eth_stats eth_rx_stats;
	struct rte_eth_dev_tx_buffer *buffer;

        lcore_id = rte_lcore_id();
        qconf = &lcore_queue_conf[lcore_id];

        prev_tsc = 0;
        timer_tsc = 0;

        if (qconf->n_rx_port == 0) {
                RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
                return;
        }

        RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

        for (i = 0; i < qconf->n_rx_port; i++) {

                portid = qconf->rx_port_list[i];
                RTE_LOG(INFO, L2FWD, " -- lcoreid=%u portid=%u\n", lcore_id,
                        portid);
        }

        tx_pkt = construct_packet(portid);
        if (tx_pkt == NULL)
                rte_exit(EXIT_FAILURE, "failed to construct packet");

	tx_buffer[0]->size = MAX_PKT_BURST;
	tx_buffer[0]->length = MAX_PKT_BURST;

	while (!force_quit) {
                cur_tsc = rte_rdtsc();
                diff_tsc = cur_tsc - prev_tsc;

                if (unlikely(diff_tsc > drain_tsc)) {
                        // handle to transmit packet on port 0
                        portid = 0;

			nb_tx = rte_eth_tx_burst(portid, 0, &tx_pkt, 1);
			nb_tx_actual = rte_eth_stats_get(portid, &eth_tx_stats);

			if (nb_tx_actual == 0) {
				port_statistics[portid].tx = eth_tx_stats.opackets;
				port_statistics[portid].dropped = eth_tx_stats.imissed;
				port_statistics[portid].tx_bytes = eth_rx_stats.obytes;
				port_statistics[portid].rx_bytes = eth_rx_stats.ibytes;
			}
			else {
				port_statistics[portid].tx_error = eth_tx_stats.oerrors;
				port_statistics[portid].rx_error = eth_tx_stats.ierrors;
			}

                        if (nb_tx) {
				//rte_prefetch0(rte_pktmbuf_mtod(tx_pkt, void *));
                                //port_statistics[portid].tx += nb_tx;
				printf("tx packet dump\n");
                                port_statistics[portid].tx_burst = nb_tx;
                                hex_dumps(tx_pkt, portid);
                                intercept_packets(tx_pkt, portid);
                                // free up the mbuf so the it can transmit another packet
                                rte_pktmbuf_free(tx_pkt);
                        }

                        // if timer is enabled
                        if (timer_period > 0) {
                                // advance the timer
                                timer_tsc += diff_tsc;

                                // if timer has reached its timeout
                                if (unlikely(timer_tsc >= timer_period)) {
                                        // do this only on main core
                                        if (lcore_id == rte_get_main_lcore()) {
                                                print_stats();
                                                // reset the timer
                                                timer_tsc = 0;
                                        }
                                }
                        }
                        prev_tsc = cur_tsc;
                }

                // handle for received packet on port 1
                portid = 1;

		nb_rx = rte_eth_rx_burst(portid, 0, &rx_pkt, 1);
		nb_rx_actual = rte_eth_stats_get(portid, &eth_rx_stats);

		if (nb_rx_actual == 0) {
			port_statistics[portid].rx = eth_rx_stats.ipackets;
			port_statistics[portid].dropped = eth_rx_stats.imissed;
			port_statistics[portid].tx_bytes = eth_rx_stats.obytes;
			port_statistics[portid].rx_bytes = eth_rx_stats.ibytes;
		}
		else {
			port_statistics[portid].tx_error = eth_tx_stats.oerrors;
			port_statistics[portid].rx_error = eth_tx_stats.ierrors;
		}

                if (unlikely(nb_rx == 0))
                        continue;

		for (j = 0; j < nb_rx; j++) {
			printf("\nrx packet dump\n");
                        intercept_packets(rx_pkt, portid);
                        hex_dumps(rx_pkt, portid);

                        port_statistics[portid].rx_burst = nb_rx;

			//printf("rx_pkt = %p\n", rte_pktmbuf_mtod(rx_pkt, void *));
                        // free up the mbuf so the it can received another packet
                        rte_pktmbuf_free(rx_pkt);
                }

		// debug: send 1 packet then stop
		if (debug_flag) {
                        if (lcore_id == rte_get_main_lcore())
                                print_stats();
                        force_quit = 1;
                }
        }
}

static void txrx_burst(void)
{
        /* WIP: port 0 tx, port 1 rx */

        struct rte_mbuf *rx_pkts_burst[MAX_PKT_BURST];
        struct rte_mbuf *tx_pkt;
        struct rte_mbuf *rx_pkt;
        uint64_t pkt_idx = 0;

        unsigned lcore_id;
        unsigned i, j, portid, nb_tx, nb_rx;
        struct lcore_queue_conf *qconf;
        uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;
        const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S *
                        BURST_TX_DRAIN_US;

        unsigned nb_tx_actual, nb_rx_actual;
        struct rte_eth_stats eth_tx_stats;
        struct rte_eth_stats eth_rx_stats;
        struct rte_eth_dev_tx_buffer *buffer;
	unsigned tx_lcore_id, rx_lcore_id;

        lcore_id = rte_lcore_id();
        qconf = &lcore_queue_conf[lcore_id];

        prev_tsc = 0;
        timer_tsc = 0;

        if (qconf->n_rx_port == 0) {
                RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
                return;
        }

        RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

        for (i = 0; i < qconf->n_rx_port; i++) {
		printf("idx = %d\n", i);
                portid = qconf->rx_port_list[i];
                RTE_LOG(INFO, L2FWD, " -- lcoreid=%u portid=%u\n", lcore_id,
                        portid);
        }

        tx_pkt = construct_packet(portid);
        if (tx_pkt == NULL)
                rte_exit(EXIT_FAILURE, "failed to construct packet");

        tx_buffer[0]->size = MAX_PKT_BURST;
        tx_buffer[0]->length = MAX_PKT_BURST;

        while (!force_quit) {
                cur_tsc = rte_rdtsc();
		diff_tsc = cur_tsc - prev_tsc;

		/* TODO: let lcore x run on port 0 and lcore y run on port 1 */
		if (lcore_id == 0) {

                if (unlikely(diff_tsc > drain_tsc)) {
                        /* send packet in burst */
                        // handle to transmit packet on port 0
                        portid = 0;
                        for (j = 0; j < MAX_PKT_BURST; j++) {
                                tx_buffer[portid]->pkts[j] = tx_pkt;
                        }

                        buffer = tx_buffer[portid];
                        nb_tx = rte_eth_tx_buffer(portid, 0, buffer, tx_pkt);

                        nb_tx_actual = rte_eth_stats_get(portid, &eth_tx_stats);

			if (nb_tx_actual == 0) {
                                port_statistics[portid].tx = eth_tx_stats.opackets;
				port_statistics[portid].rx = eth_tx_stats.ipackets;
                                port_statistics[portid].dropped = eth_tx_stats.imissed;
                                port_statistics[portid].tx_bytes = eth_tx_stats.obytes;
                                port_statistics[portid].rx_bytes = eth_tx_stats.ibytes;
                        }
                        else {
                                port_statistics[portid].tx_error = eth_tx_stats.oerrors;
                                port_statistics[portid].rx_error = eth_tx_stats.ierrors;
                        }

                        for (j = 0; j < nb_tx; j++) {
                                //rte_prefetch0(rte_pktmbuf_mtod(tx_pkt, void *));
				port_statistics[portid].tx_burst = nb_tx;
                                //hex_dumps(tx_pkt, portid);
                                intercept_packets(tx_pkt, portid);
                                // free up the mbuf so the it can transmit another packet
                                rte_pktmbuf_free(tx_pkt);
                        }

                        // if timer is enabled
                        if (timer_period > 0) {
                                // advance the timer
                                timer_tsc += diff_tsc;

                                // if timer has reached its timeout
                                if (unlikely(timer_tsc >= timer_period)) {
                                        // do this only on main core
                                        if (lcore_id == rte_get_main_lcore()) {
                                                print_stats();
                                                // reset the timer
                                                timer_tsc = 0;
                                        }
                                }
                        }
                        prev_tsc = cur_tsc;
                }
		continue;
		}

		if (lcore_id == 1) {
                /* received in burst. lcore 1 handle port 1 */
                // handle for received packet on port 1
                portid = 1;
                nb_rx = rte_eth_rx_burst(portid, 0, rx_pkts_burst, MAX_PKT_BURST);
                nb_rx_actual = rte_eth_stats_get(portid, &eth_rx_stats);
                if (nb_rx_actual == 0) {
			port_statistics[portid].tx = eth_rx_stats.opackets;
                        port_statistics[portid].rx = eth_rx_stats.ipackets;
                        port_statistics[portid].dropped = eth_rx_stats.imissed;
                        port_statistics[portid].tx_bytes = eth_rx_stats.obytes;
                        port_statistics[portid].rx_bytes = eth_rx_stats.ibytes;
                }
                else {
                        port_statistics[portid].tx_error = eth_rx_stats.oerrors;
                        port_statistics[portid].rx_error = eth_rx_stats.ierrors;
                }


                if (unlikely(nb_rx == 0))
                        continue;

                for (j = 0; j < nb_rx; j++) {
                        rx_pkt = rx_pkts_burst[j];
			//port_statistics[portid].rx_burst = nb_rx;

                        intercept_packets(rx_pkt, portid);
                        //hex_dumps(rx_pkt, portid);

                        //port_statistics[portid].rx_burst = nb_rx;
			// free up the mbuf so the it can received another packet
                        rte_pktmbuf_free(rx_pkt);
                }

                // debug: send 1 packet then stop
		if (debug_flag) {
			if (lcore_id == rte_get_main_lcore())
				print_stats();
			force_quit = 1;
		}

        }
	}
}


static void tx_only(void)
{
	struct rte_mbuf *m;
	uint64_t pkt_idx = 0;

        unsigned lcore_id;
        unsigned i, j, portid, nb_tx;
	int nb_tx_actual;
	struct rte_eth_stats eth_stats;
        struct lcore_queue_conf *qconf;
	uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;

        lcore_id = rte_lcore_id();
        qconf = &lcore_queue_conf[lcore_id];

	prev_tsc = 0;
        timer_tsc = 0;

        if (qconf->n_rx_port == 0) {
                RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
                return;
        }

        RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

        for (i = 0; i < qconf->n_rx_port; i++) {

                portid = qconf->rx_port_list[i];
                RTE_LOG(INFO, L2FWD, " -- lcoreid=%u portid=%u\n", lcore_id,
                        portid);

        }

	m = construct_packet(portid);

	if (m == NULL)
		rte_exit(EXIT_FAILURE, "failed to construct packet");

	unsigned char *cp;

	while (!force_quit) {
                cur_tsc = rte_rdtsc();
                diff_tsc = cur_tsc - prev_tsc;
                for (pkt_idx = 0; pkt_idx < nb_pkts; pkt_idx++)
                {
                        portid = l2fwd_dst_ports[qconf->rx_port_list[0]];
                        nb_tx = rte_eth_tx_burst(portid, 0, &m, 1);
			//nb_tx_actual = rte_eth_stats_get(portid, &eth_stats);

                        if (nb_tx)
                        {
                                port_statistics[portid].tx += nb_tx;
				port_statistics[portid].tx_burst = nb_tx;
				//if (nb_tx_actual == 0)
                                //	port_statistics[portid].tx_burst = eth_stats.opackets;

				//hex_dumps(m, portid);
				intercept_packets(m, portid);

				// free up the mbuf so the it can received another packet
                                rte_pktmbuf_free(m);
                        }

                }
                // if timer is enabled
                if (timer_period > 0) {

                        // advance the timer
                        timer_tsc += diff_tsc;

                        // if timer has reached its timeout
                        if (unlikely(timer_tsc >= timer_period)) {

                                // do this only on main core
                                if (lcore_id == rte_get_main_lcore()) {
                                        print_stats();
                                        // reset the timer
                                        timer_tsc = 0;
                                }
                        }
                }

                prev_tsc = cur_tsc;
        }

}

/* main processing loop */
static void
l2fwd_main_loop(void)
{
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
	int sent;
	unsigned lcore_id;
	uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;
	unsigned i, j, portid, nb_rx;
	struct lcore_queue_conf *qconf;
	const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S *
			BURST_TX_DRAIN_US;
	struct rte_eth_dev_tx_buffer *buffer;

	prev_tsc = 0;
	timer_tsc = 0;

	lcore_id = rte_lcore_id();
	qconf = &lcore_queue_conf[lcore_id];

	if (qconf->n_rx_port == 0) {
		RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
		return;
	}

	RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

	for (i = 0; i < qconf->n_rx_port; i++) {

		portid = qconf->rx_port_list[i];
		RTE_LOG(INFO, L2FWD, " -- lcoreid=%u portid=%u\n", lcore_id,
			portid);

	}

	while (!force_quit) {

		cur_tsc = rte_rdtsc();

		/*
		 * TX burst queue drain
		 */
		diff_tsc = cur_tsc - prev_tsc;
		if (unlikely(diff_tsc > drain_tsc)) {


				portid = l2fwd_dst_ports[qconf->rx_port_list[i]];
				buffer = tx_buffer[portid];

				sent = rte_eth_tx_buffer_flush(portid, 0, buffer);
				if (sent)
				{
					port_statistics[portid].tx += sent;
					port_statistics[portid].tx_burst = sent;
				}


			/* if timer is enabled */
			if (timer_period > 0) {

				/* advance the timer */
				timer_tsc += diff_tsc;

				/* if timer has reached its timeout */
				if (unlikely(timer_tsc >= timer_period)) {

					/* do this only on main core */
					if (lcore_id == rte_get_main_lcore()) {
						print_stats();
						/* reset the timer */
						timer_tsc = 0;
					}
				}
			}

			prev_tsc = cur_tsc;
		}

		/*
		 * Read packet from RX queues
		 */
		for (i = 0; i < qconf->n_rx_port; i++) {

			portid = qconf->rx_port_list[i];
			nb_rx = rte_eth_rx_burst(portid, 0,
						 pkts_burst, MAX_PKT_BURST);

			port_statistics[portid].rx += nb_rx;
			port_statistics[portid].rx_burst = nb_rx;

			for (j = 0; j < nb_rx; j++) {
				m = pkts_burst[j];
				rte_prefetch0(rte_pktmbuf_mtod(m, void *));

				/* print ethernet header */
                                intercept_packets(m, portid);
				l2fwd_simple_forward(m, portid);

			}
		}
	}
}

uint64_t bytes_to_uint64_t(unsigned char *byte, unsigned offset)
{
	uint64_t output = 0;
        byte += offset;

        for (int i = 0; i < 8; i++) {
                output <<= 8;
                output |= (*byte & 0xffff);
                byte--;
        }

	return output;
}

static void calculate_latency(struct rte_mbuf *m, unsigned portid, unsigned nb_pkts)
{
	/* This function is not accurate is it too late to get rx timestamp. */
        unsigned offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr) + sizeof(struct rte_udp_hdr);
        unsigned char *tp = rte_pktmbuf_mtod_offset(m, unsigned char *, offset);
        uint64_t tx_timestampd, rx_timestampd;
	uint64_t latency = 0;
	double latency_us = 0;
	struct timespec t_rx;
	int64_t jitter = 0;

        /* get rx timestamp in nanoseconds */
	clock_gettime(CLOCK_MONOTONIC_RAW, &t_rx);
        rx_timestampd = t_rx.tv_nsec;

	/* convert tx timestamp of 8 bytes from tx packet to uint64_t */
	tx_timestampd = bytes_to_uint64_t(tp, 7);

	port_statistics[portid].timestamp = rx_timestampd;
	latency_numbers.total_pkts += nb_pkts;

	/* skip calculate latency if rx timestamp overflow and reset to 0 */
	if (likely(rx_timestampd > tx_timestampd)) {
		latency = rx_timestampd - tx_timestampd;
		latency_numbers.total_cycles += latency;
		latency_us = ((double)latency_numbers.total_cycles / (double)latency_numbers.total_pkts) / 1000;
		port_statistics[portid].latency_us = latency_us;

		jitter = latency - latency_numbers.latency;
		if (jitter != 0)
			port_statistics[portid].jitter_ns = abs(jitter);

		latency_numbers.latency = latency;
		port_statistics[portid].jitter_ns = jitter;
	}
}

static void intercept_packets(struct rte_mbuf *m, unsigned portid)
{
	struct rte_ether_hdr *eth_hdr;
	uint16_t ether_type;
	struct rte_vlan_hdr *vh;
	struct rte_ipv4_hdr *ipv4_hdr;
	int hdr_len;
	uint32_t packet_type = RTE_PTYPE_UNKNOWN;
	void *l3;
	unsigned offset;

	eth_hdr = rte_pktmbuf_mtod(m, struct rte_ether_hdr *);
	ether_type = rte_be_to_cpu_16(eth_hdr->ether_type);

	/*
	 * l3 will point to memory address of 14th after eth_hdr. This is a pointer arithmetic.
	 * sizeof(eth_hdr) = 14.
	 * if address of eth_hdr = 0x0010, then (eth_hdr + 1) = 0x001e.
	 */
	l3 = (struct rte_ipv4_hdr *)(eth_hdr + 1);

	if (eth_hdr->ether_type == rte_cpu_to_be_16(RTE_ETHER_TYPE_IPV4))
	{
		ipv4_hdr =  (struct rte_ipv4_hdr *)l3;
		hdr_len = rte_ipv4_hdr_len(ipv4_hdr);

		if (hdr_len == sizeof(struct rte_ipv4_hdr))
		{
			packet_type |= RTE_PTYPE_L3_IPV4;
			offset = sizeof(struct rte_ether_hdr);
		}
	}


	if (ether_type == RTE_ETHER_TYPE_VLAN)
	{
		vh = (struct rte_vlan_hdr *) (eth_hdr + 1);
		uint16_t vlan_tag = rte_cpu_to_be_16(vh->vlan_tci);
		port_statistics[portid].vlan_tag =  vlan_tag;
		port_statistics[portid].vlan_id = vlan_tag & 0x0FFF;
		port_statistics[portid].vlan_priority = vlan_tag >> 13;
		offset = sizeof(struct rte_ether_hdr) + sizeof(struct rte_vlan_hdr);
	}

	struct rte_ipv4_hdr *ip4h = rte_pktmbuf_mtod_offset(m, struct rte_ipv4_hdr *, offset);
        rte_be32_t ip_s = ip4h->src_addr;
        rte_be32_t ip_d = ip4h->dst_addr;

        port_statistics[portid].ip_s_addr[0] = ip_s & 0xFF;
        port_statistics[portid].ip_s_addr[1] = (ip_s >> 8) & 0xFF;
        port_statistics[portid].ip_s_addr[2] = (ip_s >> 16) & 0xFF;
        port_statistics[portid].ip_s_addr[3] = (ip_s >> 24) & 0xFF;

        port_statistics[portid].ip_d_addr[0] = ip_d & 0xFF;
        port_statistics[portid].ip_d_addr[1] = (ip_d >> 8) & 0xFF;
        port_statistics[portid].ip_d_addr[2] = (ip_d >> 16) & 0xFF;
        port_statistics[portid].ip_d_addr[3] = (ip_d >> 24) & 0xFF;

	if (ip4h->next_proto_id == IPPROTO_UDP)
        {
		packet_type |= RTE_PTYPE_L4_UDP;
		strcpy(port_statistics[portid].ip_protocol, "udp");
	}
        else if (ipv4_hdr->next_proto_id == IPPROTO_TCP)
        {
                packet_type |= RTE_PTYPE_L4_TCP;
                strcpy(port_statistics[portid].ip_protocol, "tcp");
        }

	port_statistics[portid].ether_type = ether_type;
	port_statistics[portid].d_addr = eth_hdr->d_addr;
	port_statistics[portid].s_addr = eth_hdr->s_addr;
	//port_statistics[portid].pkt_length = m->pkt_len;
	port_statistics[portid].pkt_length = rte_pktmbuf_pkt_len(m);
	port_statistics[portid].data_len = m->data_len;
}

static int
l2fwd_launch_one_lcore(__rte_unused void *dummy)
{
	if (tx_only_flag)
		tx_only();

	else if (rx_only_flag)
		rx_only();

	else if (l2fwd_flag)
		l2fwd_main_loop();

	else if (txrx_flag) {
		//txrx();
		txrx_burst();
	}

	else
		printf("Please set either rx-only or tx-only\n");

	return 0;
}

/* display usage */
static void
l2fwd_usage(const char *prgname)
{
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
	       "  -p PORTMASK: hexadecimal bitmask of ports to configure\n"
	       "  -q NQ: number of queue (=ports) per lcore (default is 1)\n"
	       "  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 default, 86400 maximum)\n"
	       "  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by default)\n"
	       "      When enabled:\n"
	       "       - The source MAC address is replaced by the TX port MAC address\n"
	       "       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID\n"
	       "  --portmap: Configure forwarding port pair mapping\n"
	       "	      Default: alternate port pairs\n\n"
	       "  --tx-only: Set mode to transmit packet only\n"
	       "  --rx-only: Set mode to receive packet only\n"
	       "  --l2fwd: Set mode to l2fwd only\n"
	       "  --vlan: Enable vlan packet\n",
	       prgname);
}

static int
l2fwd_parse_portmask(const char *portmask)
{
	char *end = NULL;
	unsigned long pm;

	/* parse hexadecimal string */
	pm = strtoul(portmask, &end, 16);
	if ((portmask[0] == '\0') || (end == NULL) || (*end != '\0'))
		return 0;

	return pm;
}

static int
l2fwd_parse_port_pair_config(const char *q_arg)
{
	enum fieldnames {
		FLD_PORT1 = 0,
		FLD_PORT2,
		_NUM_FLD
	};
	unsigned long int_fld[_NUM_FLD];
	const char *p, *p0 = q_arg;
	char *str_fld[_NUM_FLD];
	unsigned int size;
	char s[256];
	char *end;
	int i;

	nb_port_pair_params = 0;

	while ((p = strchr(p0, '(')) != NULL) {
		++p;
		p0 = strchr(p, ')');
		if (p0 == NULL)
			return -1;

		size = p0 - p;
		if (size >= sizeof(s))
			return -1;

		memcpy(s, p, size);
		s[size] = '\0';
		if (rte_strsplit(s, sizeof(s), str_fld,
				 _NUM_FLD, ',') != _NUM_FLD)
			return -1;
		for (i = 0; i < _NUM_FLD; i++) {
			errno = 0;
			int_fld[i] = strtoul(str_fld[i], &end, 0);
			if (errno != 0 || end == str_fld[i] ||
			    int_fld[i] >= RTE_MAX_ETHPORTS)
				return -1;
		}
		if (nb_port_pair_params >= RTE_MAX_ETHPORTS/2) {
			printf("exceeded max number of port pair params: %hu\n",
				nb_port_pair_params);
			return -1;
		}
		port_pair_params_array[nb_port_pair_params].port[0] =
				(uint16_t)int_fld[FLD_PORT1];
		port_pair_params_array[nb_port_pair_params].port[1] =
				(uint16_t)int_fld[FLD_PORT2];
		++nb_port_pair_params;
	}
	port_pair_params = port_pair_params_array;
	return 0;
}

static unsigned int
l2fwd_parse_nqueue(const char *q_arg)
{
	char *end = NULL;
	unsigned long n;

	/* parse hexadecimal string */
	n = strtoul(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return 0;
	if (n == 0)
		return 0;
	if (n >= MAX_RX_QUEUE_PER_LCORE)
		return 0;

	return n;
}

static int
l2fwd_parse_timer_period(const char *q_arg)
{
	char *end = NULL;
	int n;

	/* parse number string */
	n = strtol(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;
	if (n >= MAX_TIMER_PERIOD)
		return -1;

	return n;
}

static const char short_options[] =
	"p:"  /* portmask */
	"q:"  /* number of queues */
	"T:"  /* timer period */
	;

#define CMD_LINE_OPT_MAC_UPDATING "mac-updating"
#define CMD_LINE_OPT_NO_MAC_UPDATING "no-mac-updating"
#define CMD_LINE_OPT_PORTMAP_CONFIG "portmap"
#define CMD_LINE_OPT_TX_ONLY "tx-only"
#define CMD_LINE_OPT_RX_ONLY "rx-only"
#define CMD_LINE_OPT_L2FWD "l2fwd"
#define CMD_LINE_OPT_DEBUG "debug"
#define CMD_LINE_OPT_VLAN "vlan"
#define CMD_LINE_OPT_TXRX "txrx"

enum {
	/* long options mapped to a short option */

	/* first long only option value must be >= 256, so that we won't
	 * conflict with short options */
	CMD_LINE_OPT_MIN_NUM = 256,
	CMD_LINE_OPT_PORTMAP_NUM,
	CMD_LINE_OPT_TX_ONLY_NUM,
	CMD_LINE_OPT_RX_ONLY_NUM,
	CMD_LINE_OPT_L2FWD_NUM,
	CMD_LINE_OPT_DEBUG_NUM,
	CMD_LINE_OPT_VLAN_NUM,
	CMD_LINE_OPT_TXRX_NUM,
};

static const struct option lgopts[] = {
	{ CMD_LINE_OPT_MAC_UPDATING, no_argument, &mac_updating, 1},
	{ CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, &mac_updating, 0},
	{ CMD_LINE_OPT_PORTMAP_CONFIG, 1, 0, CMD_LINE_OPT_PORTMAP_NUM},
	{ CMD_LINE_OPT_TX_ONLY, 0, 0, CMD_LINE_OPT_TX_ONLY_NUM},
	{ CMD_LINE_OPT_RX_ONLY, 0, 0, CMD_LINE_OPT_RX_ONLY_NUM},
	{ CMD_LINE_OPT_L2FWD, 0, 0, CMD_LINE_OPT_L2FWD_NUM},
	{ CMD_LINE_OPT_DEBUG, 0, 0, CMD_LINE_OPT_DEBUG_NUM},
	{ CMD_LINE_OPT_VLAN, 0, 0, CMD_LINE_OPT_VLAN_NUM},
	{ CMD_LINE_OPT_TXRX, 0, 0, CMD_LINE_OPT_TXRX_NUM},
	{NULL, 0, 0, 0}
};

/* Parse the argument given in the command line of the application */
static int
l2fwd_parse_args(int argc, char **argv)
{
	int opt, ret, timer_secs;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;
	port_pair_params = NULL;

	while ((opt = getopt_long(argc, argvopt, short_options,
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			l2fwd_enabled_port_mask = l2fwd_parse_portmask(optarg);
			if (l2fwd_enabled_port_mask == 0) {
				printf("invalid portmask\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* nqueue */
		case 'q':
			l2fwd_rx_queue_per_lcore = l2fwd_parse_nqueue(optarg);
			if (l2fwd_rx_queue_per_lcore == 0) {
				printf("invalid queue number\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* timer period */
		case 'T':
			timer_secs = l2fwd_parse_timer_period(optarg);
			if (timer_secs < 0) {
				printf("invalid timer period\n");
				l2fwd_usage(prgname);
				return -1;
			}
			timer_period = timer_secs;
			break;

		/* long options */
		case CMD_LINE_OPT_PORTMAP_NUM:
			ret = l2fwd_parse_port_pair_config(optarg);
			if (ret) {
				fprintf(stderr, "Invalid config\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* tx only */
		case CMD_LINE_OPT_TX_ONLY_NUM:
			tx_only_flag = 1;
			break;

		/* rx only */
		case CMD_LINE_OPT_RX_ONLY_NUM:
			rx_only_flag = 1;
			break;

		/* l2fwd */
		case CMD_LINE_OPT_L2FWD_NUM:
			l2fwd_flag = 1;
			break;

		/* txrx */
		case CMD_LINE_OPT_TXRX_NUM:
			txrx_flag = 1;
			break;

		/* enable vlan packet */
		case CMD_LINE_OPT_VLAN_NUM:
			vlan_flag = 1;
			break;

		/* debug */
		case CMD_LINE_OPT_DEBUG_NUM:
			debug_flag = 1;
			break;

		default:
			l2fwd_usage(prgname);
			return -1;
		}
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 1; /* reset getopt lib */
	return ret;
}

/*
 * Check port pair config with enabled port mask,
 * and for valid port pair combinations.
 */
static int
check_port_pair_config(void)
{
	uint32_t port_pair_config_mask = 0;
	uint32_t port_pair_mask = 0;
	uint16_t index, i, portid;

	for (index = 0; index < nb_port_pair_params; index++) {
		port_pair_mask = 0;

		for (i = 0; i < NUM_PORTS; i++)  {
			portid = port_pair_params[index].port[i];
			if ((l2fwd_enabled_port_mask & (1 << portid)) == 0) {
				printf("port %u is not enabled in port mask\n",
				       portid);
				return -1;
			}
			if (!rte_eth_dev_is_valid_port(portid)) {
				printf("port %u is not present on the board\n",
				       portid);
				return -1;
			}

			port_pair_mask |= 1 << portid;
		}

		if (port_pair_config_mask & port_pair_mask) {
			printf("port %u is used in other port pairs\n", portid);
			return -1;
		}
		port_pair_config_mask |= port_pair_mask;
	}

	l2fwd_enabled_port_mask &= port_pair_config_mask;

	return 0;
}

/* Check the link status of all ports in up to 9s, and print them finally */
static void
check_all_ports_link_status(uint32_t port_mask)
{
#define CHECK_INTERVAL 100 /* 100ms */
#define MAX_CHECK_TIME 90 /* 9s (90 * 100ms) in total */
	uint16_t portid;
	uint8_t count, all_ports_up, print_flag = 0;
	struct rte_eth_link link;
	int ret;
	char link_status_text[RTE_ETH_LINK_MAX_STR_LEN];

	printf("\nChecking link status");
	fflush(stdout);
	for (count = 0; count <= MAX_CHECK_TIME; count++) {
		if (force_quit)
			return;
		all_ports_up = 1;
		RTE_ETH_FOREACH_DEV(portid) {
			if (force_quit)
				return;
			if ((port_mask & (1 << portid)) == 0)
				continue;
			memset(&link, 0, sizeof(link));
			ret = rte_eth_link_get_nowait(portid, &link);
			if (ret < 0) {
				all_ports_up = 0;
				if (print_flag == 1)
					printf("Port %u link get failed: %s\n",
						portid, rte_strerror(-ret));
				continue;
			}
			/* print link status if flag set */
			if (print_flag == 1) {
				rte_eth_link_to_str(link_status_text,
					sizeof(link_status_text), &link);
				printf("Port %d %s\n", portid,
				       link_status_text);
				continue;
			}
			/* clear all_ports_up flag if any link down */
			if (link.link_status == ETH_LINK_DOWN) {
				all_ports_up = 0;
				break;
			}
		}
		/* after finally printing all link status, get out */
		if (print_flag == 1)
			break;

		if (all_ports_up == 0) {
			printf(".");
			fflush(stdout);
			rte_delay_ms(CHECK_INTERVAL);
		}

		/* set the print_flag if all ports up or timeout */
		if (all_ports_up == 1 || count == (MAX_CHECK_TIME - 1)) {
			print_flag = 1;
			printf("done\n");
		}
	}
}

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}

int
main(int argc, char **argv)
{
	struct lcore_queue_conf *qconf;
	int ret;
	uint16_t nb_ports;
	uint16_t nb_ports_available = 0;
	uint16_t portid, last_port;
	unsigned lcore_id, rx_lcore_id;
	unsigned nb_ports_in_mask = 0;
	unsigned int nb_lcores = 0;
	unsigned int nb_mbufs;

	/* init EAL */
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid EAL arguments\n");
	argc -= ret;
	argv += ret;

	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);

	/* parse application arguments (after the EAL ones) */
	ret = l2fwd_parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");

	printf("MAC updating %s\n", mac_updating ? "enabled" : "disabled");

	/* convert to number of cycles */
	printf("timer_period = %ld\n", timer_period);
	timer_period *= rte_get_timer_hz();
	printf("timer_period hz = %ld\n", timer_period);

	nb_ports = rte_eth_dev_count_avail();
	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No Ethernet ports - bye\n");

	if (port_pair_params != NULL) {
		if (check_port_pair_config() < 0)
			rte_exit(EXIT_FAILURE, "Invalid port pair config\n");
	}

	/* check port mask to possible port mask */
	if (l2fwd_enabled_port_mask & ~((1 << nb_ports) - 1))
		rte_exit(EXIT_FAILURE, "Invalid portmask; possible (0x%x)\n",
			(1 << nb_ports) - 1);

	/* reset l2fwd_dst_ports */
	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++)
		l2fwd_dst_ports[portid] = 0;
	last_port = 0;

	/* populate destination port details */
	if (port_pair_params != NULL) {
		uint16_t idx, p;

		for (idx = 0; idx < (nb_port_pair_params << 1); idx++) {
			p = idx & 1;
			portid = port_pair_params[idx >> 1].port[p];
			l2fwd_dst_ports[portid] =
				port_pair_params[idx >> 1].port[p ^ 1];
		}
	} else {
		RTE_ETH_FOREACH_DEV(portid) {
			/* skip ports that are not enabled */
			if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
				continue;

			if (nb_ports_in_mask % 2) {
				l2fwd_dst_ports[portid] = last_port;
				l2fwd_dst_ports[last_port] = portid;
			} else {
				last_port = portid;
			}

			nb_ports_in_mask++;
		}
		if (nb_ports_in_mask % 2) {
			printf("Notice: odd number of ports in portmask.\n");
			l2fwd_dst_ports[last_port] = last_port;
		}
	}

	rx_lcore_id = 0;
	qconf = NULL;

	/* Initialize the port/queue configuration of each logical core */
	RTE_ETH_FOREACH_DEV(portid) {
		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		/* get the lcore_id for this port */
		while (rte_lcore_is_enabled(rx_lcore_id) == 0 ||
		       lcore_queue_conf[rx_lcore_id].n_rx_port ==
		       l2fwd_rx_queue_per_lcore) {
			rx_lcore_id++;
			if (rx_lcore_id >= RTE_MAX_LCORE)
				rte_exit(EXIT_FAILURE, "Not enough cores\n");
		}

		if (qconf != &lcore_queue_conf[rx_lcore_id]) {
			/* Assigned a new logical core in the loop above. */
			qconf = &lcore_queue_conf[rx_lcore_id];
			nb_lcores++;
		}

		qconf->rx_port_list[qconf->n_rx_port] = portid;
		qconf->n_rx_port++;
		printf("Lcore %u: RX port %u TX port %u\n", rx_lcore_id,
		       portid, l2fwd_dst_ports[portid]);
	}


	nb_mbufs = RTE_MAX(nb_ports * (nb_rxd + nb_txd + MAX_PKT_BURST +
		nb_lcores * MEMPOOL_CACHE_SIZE), 8192U);

	printf("debug: nb_mbufs = %d\n", nb_mbufs);

	/* create the mbuf pool */
	l2fwd_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", nb_mbufs,
		MEMPOOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE,
		rte_socket_id());
	if (l2fwd_pktmbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	/* Initialise each port */
	RTE_ETH_FOREACH_DEV(portid) {
		struct rte_eth_rxconf rxq_conf;
		struct rte_eth_txconf txq_conf;
		struct rte_eth_conf local_port_conf = port_conf;
		struct rte_eth_dev_info dev_info;

		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0) {
			printf("Skipping disabled port %u\n", portid);
			continue;
		}
		nb_ports_available++;

		/* init port */
		printf("Initializing port %u... ", portid);
		fflush(stdout);

		ret = rte_eth_dev_info_get(portid, &dev_info);
		if (ret != 0)
			rte_exit(EXIT_FAILURE,
				"Error during getting device (port %u) info: %s\n",
				portid, strerror(-ret));

		if (dev_info.tx_offload_capa & DEV_TX_OFFLOAD_MBUF_FAST_FREE)
			local_port_conf.txmode.offloads |=
				DEV_TX_OFFLOAD_MBUF_FAST_FREE;

		if (dev_info.tx_offload_capa & DEV_TX_OFFLOAD_UDP_CKSUM)
			local_port_conf.txmode.offloads |=
				DEV_TX_OFFLOAD_UDP_CKSUM;
		else {
			rte_exit(EXIT_FAILURE,
				"Error: Port %u does not support UDP checksum offload\n", portid);
		}

		if (hw_timestamping) {
			if (!(dev_info.rx_offload_capa & DEV_RX_OFFLOAD_TIMESTAMP)) {
				rte_exit(EXIT_FAILURE,
					"ERROR: Port %u does not support hardware time stamping\n",
					portid);
			}
			local_port_conf.rxmode.offloads |= DEV_RX_OFFLOAD_TIMESTAMP;
			rte_mbuf_dyn_rx_timestamp_register(&hwts_dynfield_offset, NULL);
			if (hwts_dynfield_offset < 0 ) {
				rte_exit(EXIT_FAILURE,
					"ERROR: Failed to register timestamp field\n");
			}
		}

		//ret = rte_mbuf_dyn_tx_timestamp_register(&tsc_dynfield_offset, NULL);

		ret = rte_eth_dev_configure(portid, 1, 1, &local_port_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
				  ret, portid);

		ret = rte_eth_dev_adjust_nb_rx_tx_desc(portid, &nb_rxd,
						       &nb_txd);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
				 "Cannot adjust number of descriptors: err=%d, port=%u\n",
				 ret, portid);

		ret = rte_eth_macaddr_get(portid,
					  &l2fwd_ports_eth_addr[portid]);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
				 "Cannot get MAC address: err=%d, port=%u\n",
				 ret, portid);

		/* init one RX queue */
		fflush(stdout);
		rxq_conf = dev_info.default_rxconf;
		rxq_conf.offloads = local_port_conf.rxmode.offloads;
		ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
					     rte_eth_dev_socket_id(portid),
					     &rxq_conf,
					     l2fwd_pktmbuf_pool);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup:err=%d, port=%u\n",
				  ret, portid);

		/* init one TX queue on each port */
		fflush(stdout);
		txq_conf = dev_info.default_txconf;
		txq_conf.offloads = local_port_conf.txmode.offloads;
		ret = rte_eth_tx_queue_setup(portid, 0, nb_txd,
				rte_eth_dev_socket_id(portid),
				&txq_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n",
				ret, portid);

		/* Initialize TX buffers */
		tx_buffer[portid] = rte_zmalloc_socket("tx_buffer",
				RTE_ETH_TX_BUFFER_SIZE(MAX_PKT_BURST), 0,
				rte_eth_dev_socket_id(portid));
		if (tx_buffer[portid] == NULL)
			rte_exit(EXIT_FAILURE, "Cannot allocate buffer for tx on port %u\n",
					portid);

		rte_eth_tx_buffer_init(tx_buffer[portid], MAX_PKT_BURST);

		ret = rte_eth_tx_buffer_set_err_callback(tx_buffer[portid],
				rte_eth_tx_buffer_count_callback,
				&port_statistics[portid].dropped);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
			"Cannot set error callback for tx buffer on port %u\n",
				 portid);

		ret = rte_eth_dev_set_ptypes(portid, RTE_PTYPE_UNKNOWN, NULL,
					     0);
		if (ret < 0)
			printf("Port %u, Failed to disable Ptype parsing\n",
					portid);
		/* Start device */
		ret = rte_eth_dev_start(portid);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n",
				  ret, portid);

		printf("done: \n");

		if (hw_timestamping && ticks_per_cycle_mult == 0) {
			uint64_t cycles_base = rte_rdtsc();
			uint64_t ticks_base;
			ret = rte_eth_read_clock(portid, &ticks_base);
			if (ret != 0)
				rte_exit(EXIT_FAILURE, "Failed to read clock\n");
			rte_delay_ms(100);
			uint64_t cycles = rte_rdtsc();
			uint64_t ticks;
			rte_eth_read_clock(portid, &ticks);
			uint64_t c_freq = cycles - cycles_base;
			uint64_t t_freq = ticks - ticks_base;
			double freq_mult = (double)c_freq / t_freq;
			printf("TSC Freq ~= %" PRIu64
					"\nHW Freq ~= %" PRIu64
					"\nRatio: %f\n",
					c_freq * 10, t_freq * 10, freq_mult);
			/* TSC will be faster than internal ticks so freq_mult is > 0
			 * we convert the multiplicaton to an integer shift & mult
			 */
			ticks_per_cycle_mult = (1 << TICKS_PER_CYCLE_SHIFT) / freq_mult;
		}

		ret = rte_eth_promiscuous_enable(portid);
		if (ret != 0)
			rte_exit(EXIT_FAILURE,
				 "rte_eth_promiscuous_enable:err=%s, port=%u\n",
				 rte_strerror(-ret), portid);

		printf("Port %u, MAC address: %02X:%02X:%02X:%02X:%02X:%02X\n\n",
				portid,
				l2fwd_ports_eth_addr[portid].addr_bytes[0],
				l2fwd_ports_eth_addr[portid].addr_bytes[1],
				l2fwd_ports_eth_addr[portid].addr_bytes[2],
				l2fwd_ports_eth_addr[portid].addr_bytes[3],
				l2fwd_ports_eth_addr[portid].addr_bytes[4],
				l2fwd_ports_eth_addr[portid].addr_bytes[5]);

		/* initialize port stats */
		memset(&port_statistics, 0, sizeof(port_statistics));

		//rte_eth_add_rx_callback(portid, 0, add_timestamps, NULL);
		//rte_eth_add_tx_callback(portid, 0, calc_latency, NULL);

		rte_eth_add_tx_callback(portid, 0, add_timestamps_tx, NULL);
		//rte_eth_add_rx_callback(portid, 0, add_timestamps, NULL);

		/* disable calc_latency1 if using rx_only mode */
		if (!rx_only_flag)
			rte_eth_add_rx_callback(portid, 0, calc_latency1, NULL);
	}

	if (!nb_ports_available) {
		rte_exit(EXIT_FAILURE,
			"All available ports are disabled. Please set portmask.\n");
	}

	check_all_ports_link_status(l2fwd_enabled_port_mask);

	ret = 0;
	/* launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(l2fwd_launch_one_lcore, NULL, CALL_MAIN);
	RTE_LCORE_FOREACH_WORKER(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	RTE_ETH_FOREACH_DEV(portid) {
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("Closing port %d...", portid);
		ret = rte_eth_dev_stop(portid);
		if (ret != 0)
			printf("rte_eth_dev_stop: err=%d, port=%d\n",
			       ret, portid);
		rte_eth_dev_close(portid);
		printf(" Done\n");
	}
	printf("Bye...\n");

	return ret;
}

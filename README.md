## Abstract

Based on DPDK l2fwd sample application with additional features as follows
* transmit packet 802.3 or 802.1q (VLAN)
* received packet
* l2fwd packet
* hardware timestamp


## Requirement
DPDK (DPDK-stable 20.11.3)


## Compile
Require DPDK to install on host machine
See DPDK installation guide 

Need to edit dst MAC address. Change `dst_ethet_addr` based on target MAC.

```static struct rte_ether_addr dst_ether_addr = {{0x01, 0x02, 0x03, 0x04, 0x05, 0x06}};```

Then build the application

```$ make static```


## Usage
```
./myl2fwd [EAL options] -- -p PORTMASK [-q NQ]
  -p PORTMASK: hexadecimal bitmask of ports to configure
  -q NQ: number of queue (=ports) per lcore (default is 1)
  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 default, 86400 maximum)
  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by default)
      When enabled:
       - The source MAC address is replaced by the TX port MAC address
       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID
  --portmap: Configure forwarding port pair mapping
	      Default: alternate port pairs

  --tx-only: Set mode to transmit packet only
  --rx-only: Set mode to receive packet only
  --l2fwd: Set mode to l2fwd only
  --vlan: Enable vlan packet
```

tx mode

```$ ./myl2fwd -l 0-2 -n 2 -- -p 0x1 -T 1 --tx-only```

rx mode

```$ .//myl2fwd -l 0-2 -n 2 -- -p 0x1 -T 1 --rx-only```

l2fwd mode

```$ .//myl2fwd -l 0-2 -n 2 -- -p 0x1 -T 1 --l2fwd```


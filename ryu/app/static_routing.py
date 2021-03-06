# Copyright (C) 2011 Nippon Telegraph and Telephone Corporation.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
# implied.
# See the License for the specific language governing permissions and
# limitations under the License.


"""
An OpenFlow 1.0 L2 learning switch implementation.
"""


"""
--- logical_routing Component ---
This component aim to routing:
    - based on hosts IPs (no MAC taken into account
    - based on predetrmined logical routing between pairs of hosts (basically should be output of some
        algorithm on the phyical graph (e.g MM_SRLG)
    - can recover from 1 fail at most: the recovery process search for alternative path, also based
        on the predetrmined logical paths in the network.

Definitions:
    - logical paths: the paths given by the path choosing algorithm. it is predermined and
        never changed.
    - routing paths: for each logical nodes pair, the routing path is the path which they will actually connect via.

Routing Algorithm:
    - we maintain several data structures:
        * optNet holds the physical given network and logical paths (unchanged)
            assumption: there is at most 1 logical path between a given pair of logical nodes
        * logical_graph: its nodes are logical nodes, and there is an edge between 2 logical nodes iff
            there is a logical path between them in optNet.
            edges attributes:  'capacity' holds the minimum capacity of a link in the physical path between them.
                               'used'     holds the current number of routing paths traversing this logical path.
                               'path'     holds the actual nodes between the logical nodes, from the physical network.
            # this is also immutable, except the 'used' attr which can increae after link failure which not in the this path
                if a link in this path fails -> can remove the edge
        * link_to_routing_paths: mapping: physical_link=>list_of_all_pairs_of_logical_which_their_logical_path_traversing_the_link
        * forwarding_by_ids: the actual forwarding for each switch, as should be inserted to the flow tables
    - preaction process: init flow tables based on given logical paths.
        * routing paths == logical paths
    - on failure: for each pair of hosts which harmed by the failure - randomly select
        alternative path and config flow tables on the path (old ones dont care)
    - on link up: actually nothing to do. the only thing is that we need to keep the initial
        set of the logical paths, so after another failure - we could switch to alternative path
        over the link the went up.
    - in each case, anyway, we care about the pairs that harmed by the failure, and we reset all the flow entries
        in all the appropriate switches (that are on the new path) that corresponding to the host pair.

Nodes:
    - sw_id: ID of switch in the OpticalNetwork object
    - sw_dpid: datapath ID, as received by OpenFlow
    - host_id: equals sw_id which is linked to
    - port_id 0 of switch linked to host (logical router)

Pathing:
    - logical path: path between 2 logical nodes as given by the pathing algo (unchanged)
    - routing path: path between any 2 logical nodes, that moves over 1 or more logical paths
"""

import imp
import sys
import pickle as pk
import os
import copy

OPT_NET_DIR="/home/mininet/optical_network"

PICKLES_JAR=os.path.join(OPT_NET_DIR, "src", "mininet", "pickles")
PICKLED_GRAPH=os.path.join(PICKLES_JAR, "graph")
PICKLED_LOGICAL_PATHS=os.path.join(PICKLES_JAR, "logical_paths")

sys.path.append("/home/mininet/optical_network")
sys.path.append("/home/mininet/optical_network/src")

#import src.mininet.mn_interface as MNInterface
#MNInterface = imp.load_source('MNInterface', '/home/mininet/optical_network/src/mininet/mn_interface.py')

OptNet = imp.load_source('OpticalNetwork', '/home/mininet/optical_network/src/main/OpticalNetwork.py')

import logging
import struct
import networkx as nx

from ryu.base import app_manager
from ryu.controller import mac_to_port
from ryu.controller import ofp_event
from ryu.controller.handler import MAIN_DISPATCHER, CONFIG_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_0
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet
from ryu.lib.packet import ethernet
from ryu.lib.packet import ether_types

from ryu.topology.api import get_switch, get_link
from ryu.app.wsgi import ControllerBase
from ryu.topology import event, switches
from ryu.app.rest_router import ipv4_text_to_int
from ryu.lib.ip import ipv4_to_bin

class StaticRouting(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_0.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super(StaticRouting, self).__init__(*args, **kwargs)
        #self.mac_to_port = {}
        #self.topology_api_app = self

        # saves network switches by DPIDs.
        #    edges attributes: 'port_%d_to_%d'=port_num (dpids, for both directions). 'mac_%d_to_%d'=mac_of_src_dev
        #    nodes attributes: 'logical'=True/False, 'datapath'=datapath.
        # we are adding switches and links to network until it is ready - its topo equals the optNet topo
        # after that it doesnt change - not after link failure or switch down.
        # the change is only in forwarding_by_ids
        self.network=nx.Graph()
        # mapping sw_id -> ((logical_sw_src, logical_sw_dst) -> next_hop)
        # all values by optNet ids
        #self.forwarding_by_ids = {}
        self.network_is_running = False
        self.links_down = []
        self.init_topo()
        # mapping:      sw_id -> (pair_sw_id -> next_hop_id).       all IDs are of the OptNet object
        # mapping:      hostid: 'mac'=mac. 'ipv4'=ip
        #self.hostid_to_mac = {}
        self.host_mac_to_switch_dpid = {}
        self.switch_dpid_to_host_mac = {}
        self.num_of_hosts = 0


    def normalized_link(self, link):
        left  = min(link[0], link[1])
        right = max(link[0], link[1])
        return (left, right)

    '''
    gets link_state:
        (link, 'UP'/'DOWN')
    '''
    def check_and_update_network(self, switch_state = None, link_state = None):
        link  = None if link_state == None else self.normalized_link(link_state[0])
        state = None if link_state == None else link_state[1]

        if (None != link_state) and self.links_down != []:

            if   'DOWN' == link_state[1]:
                if link in self.links_down:
                    return
                self.logger.info("two_links_are_down: controller stop functioning!")

            else:  #'UP' == link_state[1]:
                self.logger.info("check_and_update_network: link (%s,%s) is up" % (link))
                self.logNet = copy.deepcopy(self.logNetInitial)
                self.optNet.l_net = self.logNet
                self.links_down = []
                self.set_routing_paths()
                self.set_flow_tables(self.optNet.get_routing_paths())

        elif (None != link_state) and ('DOWN' == link_state[1]):
            self.logger.info("check_and_update_network: link (%s,%s) removed" % (link))
            self.recover_from_link_failure(link)
            self.network_is_running = True
            self.links_down.append(self.normalized_link(link))

        else:
            if self.network_is_ready():
                self.set_flow_tables(self.optNet.get_routing_paths())
                self.network_is_running = True


    def recover_from_link_failure(self, link):
        self.logger.info("recover_from_link_failure:")
        old_routing_paths  = self.optNet.get_routing_paths()
        new_routing_paths = self.optNet.reset_after_link_failure(link)
        modified_routing_paths = self.optNet.get_modified_routing_paths(old_routing_paths, new_routing_paths)
        self.set_flow_tables(modified_routing_paths)

    def set_routing_paths(self):
        self.optNet.set_routing_paths()



    def normalize_path(self, path):
        if path[0] >= path[-1]:
            path.reverse()
        return path

    '''
        4 Parameters determine the next hop in an absolute way:
            - src mac
            - dst mac
            - port in
            - port out
    '''
    def set_flow_tables(self, routing_paths):
        self.logger.info('set_flow_tables: routing_paths = %s' % (routing_paths))
        for routing_path in routing_paths:
            routing_path = self.normalize_path(routing_path)
            l_sw_id1, l_sw_id2 = routing_path[0], routing_path[-1]
            for sw_ix in range(len(routing_path)):
                sw_id = routing_path[sw_ix]
                self.logger.info('set_flow_tables: setting flow for %d between %d to %d ' % (sw_id, l_sw_id1, l_sw_id2 ))
                next_hop_id   = routing_path[sw_ix] if sw_ix == (len(routing_path)-1) else routing_path[sw_ix+1]
                prev_hop_id   = routing_path[sw_ix] if sw_ix == 0                     else routing_path[sw_ix-1]
                sw_dpid       = self.id_to_dpid(routing_path[sw_ix])
                next_hop_dpid = self.id_to_dpid(next_hop_id)
                prev_hop_dpid = self.id_to_dpid(prev_hop_id)

                port1 = 1 if ((len(routing_path)-1) == sw_ix) else self.network[sw_dpid][next_hop_dpid]["port_%d_to_%d" % (sw_dpid, next_hop_dpid)]
                port2 = 1 if (0                     == sw_ix) else self.network[sw_dpid][prev_hop_dpid]["port_%d_to_%d" % (sw_dpid, prev_hop_dpid)]

                self.logger.info('sw_id=%s. prev_hop_id=%s. port_in=%s. next_hop_id=%s. port_out=%s' % (sw_id, prev_hop_id, port2, next_hop_id, port1))
                datapath = self.network[sw_dpid]['datapath']
                mac1  = self.switch_dpid_to_host_mac[l_sw_id1]
                mac2  = self.switch_dpid_to_host_mac[l_sw_id2]
                ip1   = self.host_mac_to_ipv4(mac1)
                ip2   = self.host_mac_to_ipv4(mac2)
                for direction in [0,1]:
                    (mac_src, mac_dst, port_in, port_out, ip_src, ip_dst) = (mac1, mac2, port2, port1, ip1, ip2) if direction == 0 else (mac2, mac1, port1, port2, ip2, ip1)
                    ofproto = self.network[sw_dpid]['datapath'].ofproto
                    port_out = ofproto.OFPP_IN_PORT if port_out == port_in else port_out
                    actions  = [datapath.ofproto_parser.OFPActionOutput(port_out)]
                    self.add_flow(dpid    = sw_dpid,
                                  in_port = port_in,
                                  mac_dst = mac_dst,
                                  mac_src = mac_src,
                                  ip_dst  = ip_dst,
                                  ip_src  = ip_src,
                                  actions = actions)


    def network_is_ready(self):
        self.logger.info('network_is_ready: ')
        self.logger.info('optNet physical links: %s ' % (self.optNet.physical_links()))
        self.logger.info('optNet logical nodes: %s. num_of_hosts=%d ' % (self.optNet.get_logical_nodes(), self.num_of_hosts))
        self.logger.info('network:  %s ' % (self.get_network_links()))
        if self.num_of_hosts != len(self.optNet.get_logical_nodes()):
            self.logger.info('network_is_ready: not enough hosts')
            return False
        for edge in self.optNet.physical_links():
            try:
                dpid1 = self.id_to_dpid(edge[0])
                dpid2 = self.id_to_dpid(edge[1])
                if (self.network[dpid1][dpid2]["port_%d_to_%d" % (dpid1, dpid2)] == None) or (self.network[dpid1][dpid2]["port_%d_to_%d" % (dpid2, dpid1)] == None):
                    return False
            except:
                return False
        for edge in self.get_network_links():
            id1 = self.dpid_to_id(edge[0])
            id2 = self.dpid_to_id(edge[1])
            if not self.optNet.is_edge(self.optNet.physical_links(), id1, id2):
                return False

        self.logger.info('network_is_ready!')
        return True

    def id_to_dpid(self, _id):
        return _id # TODO

    def dpid_to_id(self, dpid):
        return dpid # TODO


    def get_running_opt_net(self):
        with open(PICKLED_GRAPH, 'rb') as f:
            graph_file = pk.load(f)
        with open(PICKLED_LOGICAL_PATHS, 'rb') as f:
            logical_paths = pk.load(f)

        self.optNet = OptNet.OpticalNetwork(master = True)
        self.optNet.init_graph_from_file(graph_file)
        self.optNet.l_net.init_from_paths(logical_paths)
        self.logger.info("get_running_opt_net: graph_file=%s. logical_paths=%s" % (graph_file, logical_paths))

    def init_topo(self):
        self.get_running_opt_net()
        self.logNet = self.optNet.get_logical_network()
        self.logNet.print_paths()
        # we save original logical network for repro after link is up
        self.logNetInitial = copy.deepcopy(self.logNet)
        self.logger.info('init_topo: physical: %s' % self.optNet.physical_links())

        # we assume dpid = node number in the OpticalNetwork
        self.set_routing_paths()




    # Handy function that lists all attributes in the given object
    def print_attrs(self,obj):
        self.logger.info("\n".join([x for x in dir(obj) if x[0] != "_"]))

    def add_flow(self, dpid, in_port, mac_dst, mac_src, ip_dst, ip_src,  actions):
        datapath = self.network[dpid]['datapath']
        ofproto = datapath.ofproto
        self.logger.info("add_flow: in_port=%s. mac_dst=%s. mac_src=%s. ip_dst=%s. ip_src=%s" % (in_port, mac_dst, mac_src, ip_dst, ip_src))

        match = datapath.ofproto_parser.OFPMatch(
                            in_port=in_port,
                            dl_dst=haddr_to_bin(mac_dst),
                            dl_src=haddr_to_bin(mac_src),
                            #nw_src=struct.unpack('!I', ipv4_to_bin(ip_src))[0],
                            #nw_dst=struct.unpack('!I', ipv4_to_bin(ip_dst))[0],
                            dl_type=0x800)


        mod = datapath.ofproto_parser.OFPFlowMod(
            datapath=datapath, match=match, cookie=0,
            command=ofproto.OFPFC_ADD, idle_timeout=0, hard_timeout=0,
            priority=ofproto.OFP_DEFAULT_PRIORITY,
            flags=ofproto.OFPFF_SEND_FLOW_REM, actions=actions)
        datapath.send_msg(mod)


    def is_dpid(self, something):
        return isinstance(something, int)

    def get_network_links(self):
        network_edges = []
        for edge in self.network.edges():
            if (self.is_dpid(edge[0])) and (self.is_dpid(edge[1])):
                network_edges.append(edge)
        return network_edges


    def host_mac_to_ipv4(self, mac):
        self.logger.info("************* MAC = %s" % (mac) )
        return "10.0.0.%d" % (int(mac[-2:])) # TODO: fix this shit

    def host_mac_to_id(self, mac):
        return int(mac[-2:]) # TODO: fix

    def host_id_to_mac(self, _id):
        return hex(_id)[2:] #TODO

    @set_ev_cls(event.EventHostAdd, MAIN_DISPATCHER)
    def handle_host_add(self, ev):
        self.logger.info( "handle_host_add: port=%s. port_num=%d. ev.host.ipv4=%s. ev.host.mac=%s" % (ev.host.port, ev.host.port.port_no, ev.host.ipv4, ev.host.mac))
        #self.print_attrs(ev.host)
        #self.logger.info("ev attrs:")
        #self.print_attrs(ev)
        #self.logger.info("ev.host.port attrs:")
        #self.print_attrs(ev.host.port)

        self.host_mac_to_switch_dpid[ev.host.mac] = ev.host.port.dpid
        self.switch_dpid_to_host_mac[ev.host.port.dpid] = ev.host.mac
        self.num_of_hosts += 1

        self.check_and_update_network()

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def handle_link_delete(self, ev):
        self.logger.info( "handle_link_delete: src=%s. dst=%s. src.is_live=%s. dst.is_live=%s" % (ev.link.src, ev.link.dst, ev.link.src.is_live(), ev.link.src.is_live()))

        link = ev.link
        dpid1 = link.src.dpid
        dpid2 = link.dst.dpid

        #if self.network.has_edge(dpid1,dpid2):
        #    self.network.remove_edge(dpid1, dpid2)
        #del self.network[dpid1]["port_%d" % (link.src.port_no)]

        id1 = self.dpid_to_id(dpid1)
        id2 = self.dpid_to_id(dpid2)
        self.check_and_update_network(switch_state = None, link_state = ((id1, id2), 'DOWN'))

    # this called when: 'link s1 s2 down/up' , twice - one per switch
    @set_ev_cls(event.EventLinkAdd)
    def handle_link_add(self, ev):

        self.logger.info( "handle_link_add: src=%s. dst=%s. src.hw_addr=%s. dst.hw_addr=%s" % (ev.link.src, ev.link.dst, ev.link.src.hw_addr, ev.link.dst.hw_addr))
        #self.logger.info("ev attrs:")
        #self.print_attrs(ev) # link
        #self.logger.info("ev.link attrs:")
        #self.print_attrs(ev.link) #src, dst
        #self.logger.info("ev.link.src attrs:")
        #self.print_attrs(ev.link.src) #dpid, hw_addr, is_live, name, port_no
        #self.logger.info("ev.link=%s. ev.link.src=%s. ev.link.dst=%s" % (ev.link, ev.link.src, ev.link.dst))

        link = ev.link
        dpid1 = link.src.dpid
        dpid2 = link.dst.dpid

        if not self.network.has_edge(dpid1,dpid2):
            self.network.add_edge(dpid1, dpid2)
        else:
            if "port_%s_to_%s" % (dpid1, dpid2) in self.network[dpid1][dpid2]:
               assert self.network[dpid1][dpid2]["port_%s_to_%s" % (dpid1, dpid2)] == link.src.port_no, "handle_link_add: link was re-added in another port!"

        self.network[dpid1][dpid2]["port_%s_to_%s" % (dpid1, dpid2)] = link.src.port_no
        self.network[dpid1][dpid2]["mac_%s_to_%s" % (dpid1, dpid2)] = link.src.hw_addr
        self.network[dpid1]["port_%d" % (link.src.port_no)] = dpid2

        id1 = self.dpid_to_id(dpid1)
        id2 = self.dpid_to_id(dpid2)
        self.check_and_update_network(switch_state = None, link_state = ((id1,id2), 'UP'))

    @set_ev_cls(ofp_event.EventOFPPortStatus, MAIN_DISPATCHER)
    def _port_status_handler(self, ev):
        msg      = ev.msg
        reason   = msg.reason
        port_no  = msg.desc.port_no
        datapath = msg.datapath
        dpid     = datapath.id

        self.logger.info("_port_status_handler: ")
        #self.print_attrs(msg.desc) # hw_addr, index, name, peer, port_no
        #self.logger.info("ev attrs:")
        #self.print_attrs(ev)
        #self.logger.info("ev.msg attrs:")
        #self.print_attrs(msg)
        #self.logger.info("ev.msg.datapath attrs:")
        #self.print_attrs(msg.datapath)

        ofproto = msg.datapath.ofproto

        if reason == ofproto.OFPPR_ADD:
            self.logger.info("port added %s", port_no)
            #self.network[sw_dpid1][sw_dpid2]['port_%s_to_%s' % (sw_dpid1, sw_dpid2)] = port_no
            #self.network[sw_dpid1][sw_dpid2]['port_%s_to_%s' % (sw_dpid2, sw_dpid1)] = None
            #self.check_and_update_network()

        elif reason == ofproto.OFPPR_DELETE:
            self.logger.info("port deleted %s", port_no)
            #self.network[sw_dpid1][sw_dpid2]['port_%s_to_%s' % (sw_dpid1, sw_dpid2)] = None
            #self.network[sw_dpid1][sw_dpid2]['port_%s_to_%s' % (sw_dpid2, sw_dpid1)] = None
            #self.check_and_update_network(switch_state = None, link_down = link)

        elif reason == ofproto.OFPPR_MODIFY:
            self.logger.info("port modified %s", port_no)
        else:
            self.logger.info("Illeagal port state %s %s", port_no, reason)

    @set_ev_cls(event.EventSwitchEnter)
    def handle_switch_up(self, ev):

        self.logger.info("handle_switch_up: ev=%s. ev.switch=%s. ev.switch.dp=%s. ev.switch.dp.address=%s" % (ev, ev.switch, ev.switch.dp, ev.switch.dp.address))
        #self.logger.info("ev attrs:")
        #self.print_attrs(ev)
        #self.logger.info("ev.switch attrs:")
        #self.print_attrs(ev.switch)
        #self.logger.info("ev.switch.dp attrs:")
        #self.print_attrs(ev.switch.dp)

        dpid = ev.switch.dp.id
        self.network.add_node(dpid)
        self.network[dpid]['datapath'] = ev.switch.dp
        self.network[dpid]['logical'] = self.optNet.is_logical_node(self.dpid_to_id(dpid))

        self.check_and_update_network(switch_state = None, link_state = None)



        '''
            Garbage:
        '''
        #switch_list = get_switch(self.topology_api_app, None)
        #sw_dpids=[switch.dp.id for switch in switch_list]
        #self.network.add_nodes_from(sw_dpids)


        #links_list = get_link(self.topology_api_app, None)
        ##print links_list
        #links=[(link.src.dpid,link.dst.dpid,{'port':link.src.port_no}) for link in links_list]
        ##print links
        #self.network.add_edges_from(links)
        #links=[(link.dst.dpid,link.src.dpid,{'port':link.dst.port_no}) for link in links_list]
        ##print links
        #self.network.add_edges_from(links)
        #print "**********List of links"
        #print self.network.edges()
        ##for link in links_list:
	    #print link.dst
            #print link.src
            #print "Novo link"
	    #self.no_of_links += 1



    @set_ev_cls(event.EventSwitchLeave)
    def handle_switch_state(self, ev):

        self.logger.info("handle_switch_state: ev=%s. ev.switch=%s. ev.switch.dp=%s. ev.switch.dp.address=%s" % (ev, ev.switch, ev.switch.dp, ev.switch.dp.address))
        if self.optNet != None:
            self.optNet.destroy()
        self.optNet = None
        #self.logger.info("ev attrs:")
        #self.print_attrs(ev) # switch
        #self.logger.info("ev.switch attrs:")
        #self.print_attrs(ev.switch) # dp (datapath obj), ports
        #self.logger.info("ev.switch.dp attrs:")
        #self.print_attrs(ev.switch.dp)# address (always lb addr), id, is_active, ports, send, send_msg, send_packet_out, socket, state, xid


    def print_network(self):
        self.logger.info('print_network: links=%s' % (self.network.edges()))





    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocol(ethernet.ethernet)
        #ip  = pkt.get_protocol(ipv4.ipv4)

	'''
        if eth.ethertype == ether_types.ETH_TYPE_LLDP:
            # ignore lldp packet
            return
	'''
       # mac_dst = eth.dst
       # mac_src = eth.src

       # dpid = datapath.id
       # self.logger.info("_packet_in_handler:  datapath=%s. dpid=%s. mac_dst=%s. mac_src=%s. msg.in_port=%s" % (datapath, dpid, mac_dst, mac_src, msg.in_port))
       # self.mac_to_port.setdefault(dpid, {})
       # #print "nodes"
       # #print self.network.nodes()
       # #print "edges"
       # #print self.network.edges()
       # #self.logger.info("packet in %s %s %s %s", dpid, src, dst, msg.in_port)
       # if mac_src not in self.network:
       #     self.network.add_node(mac_src)
       #     self.network.add_edge(dpid,mac_src,{'port':msg.in_port})
       #     self.network.add_edge(mac_src,dpid)
       # if mac_dst in self.network:
       #     #print (src in self.network)
       #     #print nx.shortest_path(self.network,1,4)
       #     #print nx.shortest_path(self.network,4,1)
       #     #print nx.shortest_path(self.network,src,4)

       #     path=nx.shortest_path(self.network,mac_src,mac_dst)
       #     next=path[path.index(dpid)+1]
       #     out_port=self.network[dpid][next]['port']

	'''
        self.logger.info("packet in %s %s %s %s", dpid, src, dst, msg.in_port)

        # learn a mac address to avoid FLOOD next time.
        self.mac_to_port[dpid][src] = msg.in_port

        if dst in self.mac_to_port[dpid]:
            out_port = self.mac_to_port[dpid][dst]
        else:
            out_port = ofproto.OFPP_FLOOD
	'''

        #actions = [datapath.ofproto_parser.OFPActionOutput(out_port)]

        ## install a flow to avoid packet_in next time
        #if out_port != ofproto.OFPP_FLOOD:
        #    self.add_flow(datapath, msg.in_port, mac_dst, mac_src, ip_dst, ip_src, actions)

        #data = None
        #if msg.buffer_id == ofproto.OFP_NO_BUFFER:
        #    data = msg.data

        #out = datapath.ofproto_parser.OFPPacketOut(
        #    datapath=datapath, buffer_id=msg.buffer_id, in_port=msg.in_port,
        #    actions=actions, data=data)
        #datapath.send_msg(out)


    #def init_forwarding_by_ids(self, routing_paths):
    #    self.logger.info("init_forwarding_by_ids: routing_paths=%s" % (routing_paths))
    #    for sw_id in self.optNet.nodes():
    #        # mapping:
    #        self.forwarding_by_ids[sw_id] = {}

    #    closed = []
    #    for path in routing_paths:
    #        self.logger.info('***set flow for path %s' % path)
    #        sw_id_1, sw_id_2 = path[0], path[-1]
    #        for ix in range(len(path)):
    #            sw_id = path[ix]
    #            next_hop_id = sw_id if sw_id == path[-1] else path[ix+1] #TODO: find hosts ports
    #            prev_hop_id = sw_id if sw_id == path[0]  else path[ix-1]
    #            if (sw_id_1, sw_id_2) in self.forwarding_by_ids[sw_id].keys():
    #                self.forwarding_by_ids[sw_id][(sw_id_1, sw_id_2)].append(prev_hop_id, next_hop_id)
    #                self.forwarding_by_ids[sw_id][(sw_id_2, sw_id_1)].append(next_hop_id, prev_hop_id)
    #            else:
    #                self.forwarding_by_ids[sw_id][(sw_id_1, sw_id_2)] = [(prev_hop_id, next_hop_id)]
    #                self.forwarding_by_ids[sw_id][(sw_id_2, sw_id_1)] = [(next_hop_id, prev_hop_id)]
    #            self.logger.info('sw_id=%s. next=%s. prev=%s. src_id=%s. dst_id=%s' % (sw_id, next_hop_id, prev_hop_id, sw_id_1, sw_id_2))
        #self.logger.info('***Flowing for switch dpid=%s' % 1)
        #self.logger.info(self.forwarding_by_ids[1].keys() )
        #self.logger.info(forwarding_by_ids[1].keys() )




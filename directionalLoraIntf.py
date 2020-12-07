#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
 LoRaSim 0.2.1: simulate collisions in LoRa - directional nodes
 Copyright © 2016-2017 Thiemo Voigt <thiemo@sics.se> and Martin Bor <m.bor@lancaster.ac.uk>

 This work is licensed under the Creative Commons Attribution 4.0
 International License. To view a copy of this license,
 visit http://creativecommons.org/licenses/by/4.0/.

 Do LoRa Low-Power Wide-Area Networks Scale? Martin Bor, Utz Roedig, Thiemo Voigt
 and Juan Alonso, MSWiM '16, http://dx.doi.org/10.1145/2988287.2989163

 Mitigating Inter-Network Interference in LoRa Low-Power Wide-Area Networks,
 Thiemo Voigt, Martin Bor, Utz Roedig, and Juan Alonso, EWSN '17

 $Date: 2017-05-12 19:16:16 +0100 (Fri, 12 May 2017) $
 $Revision: 334 $
"""

"""
 SYNOPSIS:
   ./directionalLoraIntf.py <nodes> <avgsend> <experiment> <simtime> 
                            <collision> <directionality> <networks> <basedist>
 DESCRIPTION:
    nodes
        number of nodes to simulate
    avgsend
        average sending interval in milliseconds
    experiment
        experiment is an integer that determines with what radio settings the
        simulation is run. All nodes are configured with a fixed transmit power
        and a single transmit frequency, unless stated otherwise.
        0   use the settings with the the slowest datarate (SF12, BW125, CR4/8).
        1   similair to experiment 0, but use a random choice of 3 transmit
            frequencies.
        2   use the settings with the fastest data rate (SF6, BW500, CR4/5).
        3   optimise the setting per node based on the distance to the gateway.
        4   use the settings as defined in LoRaWAN (SF12, BW125, CR4/5).
        5   similair to experiment 3, but also optimises the transmit power.
    simtime
        total running time in milliseconds
    collision
        set to 1 to enable the full collision check, 0 to use a simplified check.
        With the simplified check, two messages collide when they arrive at the
        same time, on the same frequency and spreading factor. The full collision
        check considers the 'capture effect', whereby a collision of one or the
    directionality
        set to 1 to enable directional antennae for nodes
    networks
        number of LoRa networks
    basedist
        X-distance between two base stations
 OUTPUT
    The result of every simulation run will be appended to a file named expX.dat,
    whereby X is the experiment number. The file contains a space separated table
    of values for nodes, collisions, transmissions and total energy spent. The
    data file can be easily plotted using e.g. gnuplot.
"""

import simpy
import random
import numpy as np
import math
import sys
import matplotlib.pyplot as plt
import os
import os.path

from matplotlib.patches import Rectangle

# turn on/off graphics
graphics = 1

# do the full collision check
full_collision = False

#stat info

sfstat = [0 for x in range(6)]

#基站信道利用率统计
bsState=[]

minsensi = -200.0

downlinkPst= 5
Ptx = 14
gamma = 2.08    #路损系数
d0 = 40.0
#var = 1.28           # variance ignored for now
var = 3.05
Lpld0 = 127.41
#d0=1000
#Lpld0 = 128.95

GL = 0

# experiments:
# 0: packet with longest airtime, aloha-style experiment
# 1: one with 3 frequencies, 1 with 1 frequency
# 2: with shortest packets, still aloha-style
# 3: with shortest possible packets depending on distance


# RSSI global values for antenna
dir_30 = 4
dir_90 = 2
dir_150 = -4
dir_180 = -3
#dir_30 = 8
#dir_90 = 4
#dir_150 = -8
#dir_180 = -6


# this is an array with measured values for sensitivity
# see paper, Table 3
sf7 = np.array([7,-123.5,-124.25,-120.75])
sf8 = np.array([8,-126.25,-126.75,-124.0])
sf9 = np.array([9,-129.25,-128.25,-127.5])
sf10 = np.array([10,-132.75,-130.25,-128.75])
sf11 = np.array([11,-134.5,-132.75,-128.75])
sf12 = np.array([12,-137.25,-132.25,-132.25])

bsNode = []

def distanceSf():
    txpwr=14#dbm
    freq=470
    alpha=gamma
    sf_distance = []
    #add by zhengry 添加每个rssi所对应的距离
    rssi_list =[-123, -126,-129, -132, -134.5, -137]
    for i in range (len(rssi_list)):
        #LoRa Throughput Analysis with Imperfect Spreading Factor Orthogonality
        # ln = ((p0*fc^2*10^(-2.8))/rssi)^(1/alpha) -- alpha是路损系数 
        tmp = math.pow(10, txpwr/10) / (math.pow(freq, 2)*math.pow(10,-2.8)* math.pow(10, rssi_list[i]/10))
        sf_distance.append(math.pow(tmp, 1/alpha))
    print("SF_Distance: ", sf_distance)

#
# check for collisions at base station
# Note: called before a packet (or rather node) is inserted into the list
def checkcollision(packet):
    col = 0 # flag needed since there might be several collisions for packet
    # lost packets don't collide
    if packet.lost:
       return 0
    if packetsAtBS[packet.bs]:
        for other in packetsAtBS[packet.bs]:
            if other.id != packet.nodeid:
               # simple collision
               if frequencyCollision(packet, other.packet[packet.bs]) \
                   and sfCollision(packet, other.packet[packet.bs]):
                   if full_collision:
                       if timingCollision(packet, other.packet[packet.bs]):
                           # check who collides in the power domain
                           c = powerCollision(packet, other.packet[packet.bs])
                           # mark all the collided packets
                           # either this one, the other one, or both
                           for p in c:
                               p.collided = 1
                               if p == packet:
                                   col = 1
                       else:
                           # no timing collision, all fine
                           pass
                   else:
                       packet.collided = 1
                       other.packet[packet.bs].collided = 1  # other also got lost, if it wasn't lost already
                       col = 1
        return col
    return 0

#
# frequencyCollision, conditions
#
#        |f1-f2| <= 120 kHz if f1 or f2 has bw 500 
#        |f1-f2| <= 60 kHz if f1 or f2 has bw 250 
#        |f1-f2| <= 30 kHz if f1 or f2 has bw 125 
def frequencyCollision(p1,p2):
    if (abs(p1.freq-p2.freq)<=120 and (p1.bw==500 or p2.freq==500)):
        return True
    elif (abs(p1.freq-p2.freq)<=60 and (p1.bw==250 or p2.freq==250)):
        return True
    else:
        if (abs(p1.freq-p2.freq)<=30):
            return True
    return False

def sfCollision(p1, p2):
    if p1.sf == p2.sf:
        # p2 may have been lost too, will be marked by other checks
        return True
    return False

def powerCollision(p1, p2):
    powerThreshold = 6 # dB
    if abs(p1.rssi - p2.rssi) < powerThreshold:
        # packets are too close to each other, both collide
        # return both packets as casualties 
        return (p1, p2)
    elif p1.rssi - p2.rssi < powerThreshold:
        # p2 overpowered p1, return p1 as casualty
        return (p1,)
    # p2 was the weaker packet, return it as a casualty  
    return (p2,)

def timingCollision(p1, p2):
    # assuming p1 is the freshly arrived packet and this is the last check
    # we've already determined that p1 is a weak packet, so the only
    # way we can win is by being late enough (only the first n - 5 preamble symbols overlap)
    
    # assuming 8 preamble symbols
    Npream = 8
    
    # we can lose at most (Npream - 5) * Tsym of our preamble
    Tpreamb = 2**p1.sf/(1.0*p1.bw) * (Npream - 5)
    
    # check whether p2 ends in p1's critical section
    p2_end = p2.addTime + p2.rectime
    p1_cs = env.now + Tpreamb
    if p1_cs < p2_end:
        # p1 collided with p2 and lost
        return True
        #return False
    return False

# this function computes the airtime of a packet
# according to LoraDesignGuide_STD.pdf
#
def airtime(sf,cr,pl,bw):
    H = 0        # implicit header disabled (H=0) or not (H=1)
    DE = 0       # low data rate optimization enabled (=1) or not (=0)
    Npream = 8   # number of preamble symbol (12.25  from Utz paper)

    if bw == 125 and sf in [11, 12]:
        # low data rate optimization mandated for BW125 with SF11 and SF12
        DE = 1
    if sf == 6:
        # can only have implicit header with SF6
        H = 1

    Tsym = (2.0**sf)/bw
    Tpream = (Npream + 4.25)*Tsym
    #print "sf", sf, " cr", cr, "pl", pl, "bw", bw
    payloadSymbNB = 8 + max(math.ceil((8.0*pl-4.0*sf+28+16-20*H)/(4.0*(sf-2*DE)))*(cr+4),0)
    Tpayload = payloadSymbNB * Tsym
    return Tpream + Tpayload
#
# this function creates a BS
#
class myBS():
    def __init__(self, id):
        self.id = id
        self.x = 0
        self.y = 0

        # This is a hack for now
        global nrBS
        global maxDist
        global maxX
        global maxY
        global baseDist
        
        self.stat_util_chnl = [0 for i in range(8)]
        self.downCnt = 0

        #增加利用率统计、 

        if (nrBS == 1 and self.id == 0):
            self.x = maxDist
            self.y = maxY

        if (nrBS == 2 and self.id == 0):
            self.x = maxDist
            self.y = maxY

        if (nrBS == 2 and self.id == 1):
            self.x = maxDist + baseDist
            self.y = maxY

        if (nrBS == 3 and self.id == 0):
            self.x = maxDist + baseDist
            self.y = maxY

        if (nrBS == 3 and self.id == 1):
            self.x = maxDist 
            self.y = maxY

        if (nrBS == 3 and self.id == 2): 
            #self.x = maxDist + 2*baseDist
            self.x = maxDist + baseDist / 2
            #self.y = maxY
            self.y = maxY + baseDist

        if (nrBS == 4 and self.id == 0): 
            self.x = maxDist + baseDist
            self.y = maxY 

        if (nrBS == 4 and self.id == 1):
            self.x = maxDist 
            self.y = maxY

        if (nrBS == 4 and self.id == 2): 
            self.x = maxDist + 2*baseDist
            self.y = maxY

        if (nrBS == 4 and self.id == 3): 
            self.x = maxDist + baseDist
            self.y = maxY + baseDist 

        if (nrBS == 5 and self.id == 0): 
            self.x = maxDist + baseDist
            self.y = maxY + baseDist 

        if (nrBS == 5 and self.id == 1): 
            self.x = maxDist 
            self.y = maxY + baseDist 

        if (nrBS == 5 and self.id == 2): 
            self.x = maxDist + 2*baseDist
            self.y = maxY + baseDist 

        if (nrBS == 5 and self.id == 3): 
            self.x = maxDist + baseDist
            self.y = maxY 

        if (nrBS == 5 and self.id == 4): 
            self.x = maxDist + baseDist
            self.y = maxY + 2*baseDist 


        if (nrBS == 6): 
            if (self.id < 3):
                self.x = (self.id+1)*maxX/4.0
                self.y = maxY/3.0
            else:
                self.x = (self.id+1-3)*maxX/4.0
                self.y = 2*maxY/3.0

        if (nrBS == 8): 
            if (self.id < 4):
                self.x = (self.id+1)*maxX/5.0
                self.y = maxY/3.0
            else:
                self.x = (self.id+1-4)*maxX/5.0
                self.y = 2*maxY/3.0

        if (nrBS == 24): 
            if (self.id < 8):
                self.x = (self.id+1)*maxX/9.0
                self.y = maxY/4.0
            elif (self.id < 16):
                self.x = (self.id+1-8)*maxX/9.0
                self.y = 2*maxY/4.0
            else:
                self.x = (self.id+1-16)*maxX/9.0
                self.y = 3*maxY/4.0

        if (nrBS == 96): 
            if (self.id < 24):
                self.x = (self.id+1)*maxX/25.0
                self.y = maxY/5.0
            elif (self.id < 48):
                self.x = (self.id+1-24)*maxX/25.0
                self.y = 2*maxY/5.0
            elif (self.id < 72):
                self.x = (self.id+1-48)*maxX/25.0
                self.y = 3*maxY/5.0
            else:
                self.x = (self.id+1-72)*maxX/25.0
                self.y = 4*maxY/5.0

        
        print("BSx:", self.x, "BSy:", self.y)

#bs stat info
        self.stat_start_time = 0
        self.stat_end_time = 0
        self.last_work_time = 0
        self.work_time = 0
        self.rx_time = 0
        self.delta_work_time = 0
        self.delta_record_time = 0
        self.last_record_time = 0
        self.util = 0 #基站利用率
        self.tx_util = 0
        self.chnelUtil = [0 for i in range(8)]#信道利用率
        self.txtime = 0
        self.dropPkt = 0
        self.tx_lost =0
        
        self.sfstat_lost = [0 for x in range(6)]
        self.sfstat_collision = [0 for x in range(6)]
        self.sfstat_recv = [0 for x in range(6)]
        
#end bs stat info

        global graphics
        if (graphics):
            global ax
            # XXX should be base station position
            if (self.id == 0):
                ax.add_artist(plt.Circle((self.x, self.y), 4, fill=True, color='blue'))
                ax.add_artist(plt.Circle((self.x, self.y), maxDist, fill=False, color='blue'))
            if (self.id == 1):
                ax.add_artist(plt.Circle((self.x, self.y), 4, fill=True, color='red'))
                ax.add_artist(plt.Circle((self.x, self.y), maxDist, fill=False, color='red'))
            if (self.id == 2):
                ax.add_artist(plt.Circle((self.x, self.y), 4, fill=True, color='green'))
                ax.add_artist(plt.Circle((self.x, self.y), maxDist, fill=False, color='green'))
            if (self.id == 3):
                ax.add_artist(plt.Circle((self.x, self.y), 4, fill=True, color='brown'))
                ax.add_artist(plt.Circle((self.x, self.y), maxDist, fill=False, color='brown'))
            if (self.id == 4):
                ax.add_artist(plt.Circle((self.x, self.y), 4, fill=True, color='orange'))
                ax.add_artist(plt.Circle((self.x, self.y), maxDist, fill=False, color='orange'))

#
# this function creates a node
#
class myNode():
    def __init__(self, id, period, packetlen, myBS, fileExist, x, y):
        global bs

        self.bs = myBS
        self.id = id
        self.period = period

        self.x = 0
        self.y = 0
        #保存当前发送报文的处理状态
        self.packet = []
        self.dist = []
        # this is very complex prodecure for placing nodes
        # and ensure minimum distance between each pair of nodes
        found = 0
        rounds = 0
        global nodes
        if (fileExist == True):  
            self.x = x
            self.y = y
        else : 
            while (found == 0 and rounds < 100):
                global maxX
                global maxY
                #生成a为弧长，b为圆周长
                a = random.random()
                b = random.random()
                if b<a:
                    a,b = b,a
                #放置终端
                #print("a: ", a, ",b: ", b)
                posx = b*maxDist*math.cos(2*math.pi*a/b)+self.bs.x
                posy = b*maxDist*math.sin(2*math.pi*a/b)+self.bs.y
                #print("posx: ", posx, ", posy: ", maxDist, ". maxDist: ", maxDist, ", cosThreata:", math.cos(2*math.pi*a/b))
                if len(nodes) > 0:
                    for index, n in enumerate(nodes):
                        dist = np.sqrt(((abs(n.x-posx))**2)+((abs(n.y-posy))**2)) 
                        # we set this so nodes can be placed everywhere
                        # otherwise there is a risk that little nodes are placed
                        # between the base stations where it would be more crowded
                        if dist >= 0: 
                            found = 1
                            self.x = posx
                            self.y = posy
                        else:
                            rounds = rounds + 1
                            if rounds == 100:
                                print("could not place new node, giving up")
                                exit(-2) 
                else:
                    print("first node")
                    self.x = posx
                    self.y = posy
                    found = 1

        #给node增加sf属性
        
        mindist = 99999
        chooseBs = 0
        global nrBS
        for i in range(0,nrBS):
            d = np.sqrt((self.x-bsNode[i].x)*(self.x-bsNode[i].x)+(self.y-bsNode[i].y)*(self.y-bsNode[i].y)) 
            if (mindist > d) :
                mindist = d
                chooseBs = i       
        #根据节点到bs的距离分配sf        
        # log-shadow
        Lpl = Lpld0 + 10*gamma*math.log10(mindist/d0) #+ random.gauss(0, var)
        Prx = Ptx - GL - Lpl
        self.rssi = Prx
        self.sf = 12
        self.cr = 1
        self.bw = 125
        self.pl = 20
        self.downgw = chooseBs

            
        #使用margin补充一些余量
        rssiMargin = Prx - margin
        #根据rssi选择sf
        for i in range(0,6):
            #for j in range(1,1):
            j = 1
            #print("comp sensi[",i,",",j,"]:",sensi[i,j], ",Prx:", Prx)
            if (sensi[i,j] < rssiMargin):
                self.sf = int(sensi[i,0])
                break

        #由于报文长度固定，为每个基站创建一个报文
        # create "virtual" packet for each BS
        #global nrBS
        for i in range(0,nrBS):
            d = np.sqrt((self.x-bsNode[i].x)*(self.x-bsNode[i].x)+(self.y-bsNode[i].y)*(self.y-bsNode[i].y)) 
            self.dist.append(d) #到各个基站的距离
            self.packet.append(myPacket(self.id, packetlen, self.dist[i], i, self.sf))
        #print('node %d' %id, "x", self.x, "y", self.y, "dist: ", self.dist, "my BS:", self.bs.id,"sf: ", self.sf)

        self.sent = 0
'''
        # graphics for node
        global graphics
        if (graphics == 1):
            global ax
            if (self.bs.id == 0):
                    ax.add_artist(plt.Circle((self.x, self.y), 2, fill=True, color='blue'))
            if (self.bs.id == 1):
                    ax.add_artist(plt.Circle((self.x, self.y), 2, fill=True, color='red'))
            if (self.bs.id == 2):
                    ax.add_artist(plt.Circle((self.x, self.y), 2, fill=True, color='green'))
            if (self.bs.id == 3):
                    ax.add_artist(plt.Circle((self.x, self.y), 2, fill=True, color='brown'))
            if (self.bs.id == 4):
                    ax.add_artist(plt.Circle((self.x, self.y), 2, fill=True, color='orange'))
'''

#
#   update RSSI depending on direction
#
def updateRSSI(self):
    global bsNode

    print("+++++++++uR node", self.id, " and bs ", self.bs.id) 
    print("node x,y", self.x, self.y)
    print("main-bs x,y", bsNode[self.bs.id].x, bsNode[self.bs.id].y)
    for i in range(0,len(self.packet)):
        print("rssi before", self.packet[i].rssi)
        print("packet bs", self.packet[i].bs)
        print("packet bs x, y:", bsNode[self.packet[i].bs].x, bsNode[self.packet[i].bs].y)          
        if (self.bs.id == self.packet[i].bs):
            print("packet to main bs, increase rssi ")
            self.packet[i].rssi = self.packet[i].rssi + dir_30
        else:
            b1 = np.array([bsNode[self.bs.id].x, bsNode[self.bs.id].y])
            p = np.array([self.x, self.y])
            b2 = np.array([bsNode[self.packet[i].bs].x, bsNode[self.packet[i].bs].y])

            ba = b1 - p
            bc = b2 - p
            print(ba)
            print(bc)

            cosine_angle = np.dot(ba, bc) / (np.linalg.norm(ba) * np.linalg.norm(bc))
            angle = np.degrees(np.arccos(cosine_angle))

            print("angle: ", angle)

            if (angle <= 30):
                print("rssi increase to other BS: 4")
                self.packet[i].rssi = self.packet[i].rssi + dir_30
            elif angle <= 90:
                print("rssi increase to other BS: 2")
                self.packet[i].rssi = self.packet[i].rssi + dir_90
            elif angle <= 150:
                print("rssi increase to other BS: -4")
                self.packet[i].rssi = self.packet[i].rssi + dir_150
            else:
                print("rssi increase to other BS: -3")
                self.packet[i].rssi = self.packet[i].rssi + dir_180
        print("packet rssi after", self.packet[i].rssi)

#margin = 10
margin = 10
#
# this function creates a packet (associated with a node)
# it also sets all parameters, currently random
#
class myPacket():
    def __init__(self, nodeid, plen, distance, bs, sf):
        global experiment
        global Ptx
        global gamma
        global d0
        global var
        global Lpld0
        global GL
        global nodes

        #是否确认报文 - 默认为false
        #self.Confirmed= False

        # new: base station ID
        self.bs = bs
        self.nodeid = nodeid
        self.txpow = Ptx
        self.cr = 1
        self.bw = 125
        #Prx=Ptx
        # log-shadow
        Lpl = Lpld0 + 10*gamma*math.log10(distance/d0)# + random.gauss(0, var)
        #print("distance: ", distance)
        Prx = Ptx - GL - Lpl
        #print("Prx:",Prx, "=Lpld0:", Lpld0,"-GL:",GL,"-Lpl:",Lpl)

        sfidx = sf
        if (sfidx >= 7) :
            sfidx = sfidx - 7 
        # transmission range, needs update XXX    
        self.transRange = 150  
        self.pl = plen
        self.symTime = (2.0**sf)/self.bw
        self.arriveTime = 0
        #发送信道,rssi,toa时间都应该发送的时候重新确定吧
        self.rssi = Prx #- random.gauss(0, var)#addy by zhengry 
        self.cur_rssi = self.rssi
        # frequencies: lower bound + number of 61 Hz steps
        #self.freq = 860000000 + random.randint(0,2622950)
        self.chnl = random.randint(0,8)
        self.freq = 470000000 + self.chnl * 200000 
        self.sf = sf
        
        # for certain experiments override these and
        # choose some random frequences
        '''
        if experiment == 1:
            self.freq = random.choice([860000000, 864000000, 868000000])
        if experiment == 6:
            self.freq = 470000000 + random.randint(0,8) * 200000 
        else:
            self.freq = 860000000
        '''
        self.rectime = airtime(self.sf,self.cr,self.pl,self.bw)
        # denote if packet is collided
        self.collided = 0
        self.processed = 0
        # mark the packet as lost when it's rssi is below the sensitivity
        # don't do this for experiment 3, as it requires a bit more work
        self.lost = 0
        #不应该在此处就确认丢弃吧,需要根据发送时使用的sf确定
        if self.rssi < sensi[sfidx,1]:
            self.lost = 1            
            #print("node {} bs {} lost {}".format(self.nodeid, self.bs, self.lost))
'''
        if experiment != 3:
            self.lost = self.rssi < minsensi
            print("node {} bs {} lost {}".format(self.nodeid, self.bs, self.lost))
'''
        

'''
挑选下行基站，需要考虑的因素有:
1.基站利用率
2.报文在各基站上的rssi/snr
3.报文所使用的信道在对应基站上的利用率表现
4.速率、toa
5.报文所使用的速率在所在基站上的占比？

应该考虑的问题是：
1。 信号越差，越应该考虑信号问题,增加信号因子权重
2. 当利用率都较高时，考虑最大影响

'''
def pickGw(env, node):
    pickrssi = -9999
    pickgw = node.downgw
    bestscore=999
    for bsidx in range(0, nrBS):
        #stat gateway util
        #stat channel gateway -  base sf/channel
        #rssi /snr
        #last priority: sf/toa

        #基站接收到对应报文
        #choose gw func = 1
        if experiment == 1:
            if (node.packet[bsidx].lost == 0 & node.packet[bsidx].collided == 0):
                if pickrssi < node.packet[bsidx].cur_rssi:
                    pickrssi = node.packet[bsidx].cur_rssi
                    pickgw = bsidx

        elif experiment == 2:
            if (node.packet[bsidx].lost == 0 & node.packet[bsidx].collided == 0):
                chnl = node.packet[bsidx].chnl
                #schedule,toa, rssi,util
                rssiscore = min(node.packet[bsidx].cur_rssi * (-0.1), 10)
                #utilScore=min(gwUti*5,20)/2+min(chnlUtil*100,10)
                bsNode[bsidx].util = bsNode[bsidx].work_time / simtime
                utilscore = min(bsNode[bsidx].util *50, 20) /2           
                chnlutilscore = min(bsNode[bsidx].chnelUtil[chnl]/simtime * 200, 20) / 2
                if (bestscore > (rssiscore+utilscore + chnlutilscore)):
                    bestscore = (rssiscore+utilscore + chnlutilscore)
                    pickgw = bsidx
                    #" rssiscore: ", rssiscore,
                    #print("totScore:", bestscore, ",node[",node.id,"] pick BS:", pickgw,", rssi：", node.packet[bsidx].cur_rssi, 
                     #     ",gwuitil: ",utilscore, ",chnlUtil[", chnl, "]:", chnlutilscore)     
        elif experiment == 3:
            if (node.packet[bsidx].lost == 0 & node.packet[bsidx].collided == 0):
                chnl = node.packet[bsidx].chnl
                #schedule,toa, rssi,util
                delta_rssi = node.packet[bsidx].cur_rssi - sensi[node.sf - 7][1]
                rssiscore = 0
                weight = 1
                if delta_rssi >= 10:
                  weight = 0 #该条件对于争夺临界终端基本？争夺内环终端
                if delta_rssi < 3:#属于外环终端
                   weight = 3#该条件的意思是：临界终端倾向选择信号好的
                rssiscore = min(weight *6/ delta_rssi, 20)
                #utilScore=min(gwUti*5,20)/2+min(chnlUtil*100,10)
                if(bsNode[bsidx].delta_record_time == 0) :
                    bsNode[bsidx].util = bsNode[bsidx].work_time / simtime 
                else:
                    bsNode[bsidx].util = bsNode[bsidx].delta_work_time / bsNode[bsidx].delta_record_time

                bsNode[bsidx].util = bsNode[bsidx].work_time / simtime 
               
                utilscore = 0

                chnlutilscore = 0
                #if (bsNode[bsidx].util > 0.1) :
                utilscore = min(bsNode[bsidx].util * 40, 20) #min(bsNode[bsidx].util * 100, 100) /10 
                chnlutilscore = min(bsNode[bsidx].chnelUtil[chnl]/simtime* 100, 20)
                if (bestscore > (rssiscore+utilscore + chnlutilscore)):
                    bestscore = (rssiscore+utilscore + chnlutilscore)
                    pickgw = bsidx
                    print("totScore:", bestscore, ",node[",node.id,"] pick BS:", pickgw," rssiscore: ", rssiscore,", rssi：[",delta_rssi,"]", node.packet[bsidx].cur_rssi, 
                            ",gwuitil: ",utilscore,",chnlUtil[", chnl, "]:", chnlutilscore, ",SF: ", node.sf)     
        else:
            pickgw = node.bs.id


    return pickgw

#统计基站工作时间
#direct : 0 - uplink , 1 - downlink
def statBsWorkTime(bsidx, chnl, start_time, end_time, direct):
    toa_time = end_time - start_time
    if (start_time > bsNode[bsidx].stat_end_time) :
        bsNode[bsidx].stat_start_time = start_time
        bsNode[bsidx].work_time += toa_time
        bsNode[bsidx].stat_end_time = end_time
        if (direct == 0):
            bsNode[bsidx].rx_time += toa_time
        #print("1: Update Bsidx:", bsidx, " startTime: ", start_time/1000, ", endTime: ", end_time/1000)
    else:#if  env.now < bsNode[bsidx].stat_end_time                    
        if (bsNode[bsidx].stat_end_time < end_time):
            bsNode[bsidx].work_time += (end_time - bsNode[bsidx].stat_end_time)
            if (direct == 0):
                bsNode[bsidx].rx_time += (end_time - bsNode[bsidx].stat_end_time)
            bsNode[bsidx].stat_end_time = end_time
            
        #print("2: Update Bsidx:", bsidx, " startTime: ", start_time/1000, ", endTime: ", end_time/1000)
    #print("workTime BS[",bsidx,"]:", bsNode[bsidx].work_time)
    bsNode[bsidx].chnelUtil[chnl] += toa_time
    if (env.now - bsNode[bsidx].last_record_time) > 100000*1000:
        bsNode[bsidx].last_record_time = env.now
        bsNode[bsidx].delta_record_time = env.now - bsNode[bsidx].last_record_time
        bsNode[bsidx].delta_work_time = bsNode[bsidx].work_time - bsNode[bsidx].last_work_time
        bsNode[bsidx].last_work_time = bsNode[bsidx].work_time


'''
基于基站需要考虑的统计信息：
1. 利用率= 接收时间+发送时间 / 总时间
2. 信道利用率 = 信道的接收时间 + 信道的发送时间 / 总时间
3. 使用基站下行影响的报文个数： 
   平均接收报文个数 =  报文接收总个数/时间
'''
def processStatGw(env, bs):
    stat_period = 1*1000 #统计周期为1s
    global nrBS
    while True:
        yield env.timeout(stat_period)            
        #stat gateway util
        #stat channel gateway -  base sf/channel
        for i in range(0, nrBS):
            #利用率如何统计？
            bs[i].util_stat = (bs[i].acttime - bs[i].last_acttime)*100/stat_period
            #bs[i].

#
# main discrete event loop, runs for each node
# a global list of packet being processed at the gateway
# is maintained
#       
def transmit(env,node):
    while True:
        # time before sending anything (include prop delay)
        # send up to 2 seconds earlier or later
        yield env.timeout(random.expovariate(1.0/float(node.period)))

        # time sending and receiving
        # packet arrives -> add to base station

        node.sent = node.sent + 1

        confirmed = False

        if (node.sent % downlinkPst == 0):
            confirmed = True

        global packetSeq
        packetSeq = packetSeq + 1

        global nrBS

        #发送过程中确定使用的信道
        chnl = random.randint(0,7)
        txfreq= 470000000 + chnl * 200000 

        sfstat[node.packet[0].sf - 7] += 1

        #报文在基站的处理过程
        for bsidx in range(0, nrBS):            
            node.packet[bsidx].chnl =chnl
            node.packet[bsidx].freq = txfreq
            if (node in packetsAtBS[bsidx]):
                print("ERROR: packet already in")
            else:
                #标记该报文为确认报文
                node.packet[bsidx].confirmed = confirmed
                # adding packet if no collision
                if (checkcollision(node.packet[bsidx])==1):
                    node.packet[bsidx].collided = 1
                else:
                    node.packet[bsidx].collided = 0
                
                packetsAtBS[bsidx].append(node)

                node.packet[bsidx].addTime = env.now
                node.packet[bsidx].seqNr = packetSeq

                #时间记录 - 未丢失且未冲突，记录为有效工作时间，当前bs处于接收状态
                if (node.packet[bsidx].lost == 0 & node.packet[bsidx].collided == 0 & bsState[bsidx] == 0):              
                    toa_time = node.packet[bsidx].rectime
                    statBsWorkTime(bsidx, chnl, env.now, (env.now + toa_time), 0)   
                    #print("Nodes[",node.id,"] startTime:", env.now, ", sf:", node.sf, ", endTime: ", env.now+toa_time, ", toaTime: ", toa_time)          
 
        # take first packet rectime - yield是一个生成器，这里会return，直到下次执行会往下运行     
        yield env.timeout(node.packet[0].rectime)

        # if packet did not collide, add it in list of received packets
        # unless it is already in
        #应该在此处进行rssi啥的计算，对于lost的计算需要把当前环境下的sf的覆盖距离和路损计算结合起来
        #覆盖距离计算公式：
        for bsidx in range(0, nrBS):
            #当前bs处于发送状态，无法接收数据
            #rssi =  node.packet[bsidx].rssi - random.gauss(0, var)
            node.packet[bsidx].cur_rssi = node.packet[bsidx].rssi - random.gauss(0, var)
            if node.packet[bsidx].cur_rssi < sensi[node.packet[bsidx].sf-7, 1]:
                node.packet[bsidx].lost = 1    
            if bsState[bsidx] == 1: 
                node.packet[bsidx].lost = 1
                bsNode[bsidx].tx_lost += 1
            if node.packet[bsidx].lost:
                lostPackets.append(node.packet[bsidx].seqNr)
                bsNode[bsidx].dropPkt +=1
                bsNode[bsidx].sfstat_lost[node.packet[0].sf - 7] += 1
            else:
                if node.packet[bsidx].collided == 0:
                    if (nrNetworks == 1):
                        packetsRecBS[bsidx].append(node.packet[bsidx].seqNr)
                    else:
                        # now need to check for right BS
                        if (node.bs.id == bsidx):
                            packetsRecBS[bsidx].append(node.packet[bsidx].seqNr)
                    # recPackets is a global list of received packe ts
                    # not updated for multiple networks        
                    if (recPackets):
                        if (recPackets[-1] != node.packet[bsidx].seqNr):
                            recPackets.append(node.packet[bsidx].seqNr)
                            bsNode[bsidx].sfstat_recv[node.packet[0].sf - 7] += 1
                    else:
                        recPackets.append(node.packet[bsidx].seqNr)
                else:
                    # XXX only for debugging
                    collidedPackets.append(node.packet[bsidx].seqNr)                   
                    bsNode[bsidx].sfstat_collision[node.packet[0].sf - 7] += 1

        # complete packet has been received by base station
        # can remove it

        #pick downlink gw
        if (confirmed):
            bsidx = pickGw(env, node)
            packet = node.packet[bsidx]
            node.downgw = bsidx
            if (bsidx >= 0):               
                bsNode[bsidx].downCnt +=1
                bsState[bsidx] = 1#set to tx mode
                toa_time = airtime(packet.sf, packet.cr, packet.pl, packet.bw)
                yield env.timeout(toa_time)
                bsNode[bsidx].tx_util += toa_time
                bsState[bsidx] = 0 #reset bs stat to rx mode
                statBsWorkTime(bsidx, chnl, env.now, (env.now + toa_time), 1)
        
        #报文处理完成，重置状态
        for bsidx in range(0, nrBS):                    
            if (node in packetsAtBS[bsidx]):
                packetsAtBS[bsidx].remove(node)
                # reset the packet
                node.packet[bsidx].collided = 0
                node.packet[bsidx].processed = 0
        
#
# "main" program
#

plan = []
plan1 = [0.2,   0.30,   0.5]
plan2=  [0.30,  0.30,   0.4]
plan3=  [0.10,  0.30,   0.6]
plan.append(plan1)
plan.append(plan2)
plan.append(plan3)

# get arguments
if len(sys.argv) == 10:
    nrNodes = int(sys.argv[1])                       
    avgSendTime = int(sys.argv[2])
    experiment = int(sys.argv[3])
    simtime = int(sys.argv[4])
    nrBS = int(sys.argv[5])
    if len(sys.argv) > 6:
        full_collision = bool(int(sys.argv[6]))
    directionality = int(sys.argv[7])
    #nrNetworks = int(sys.argv[8])
    nrNetworks = 1
    planid = int(sys.argv[8])
    baseDist = float(sys.argv[9])
    print("Nodes per base station:", nrNodes)
    print("AvgSendTime (exp. distributed):",avgSendTime)
    print("Experiment: ", experiment)
    print("Simtime: ", simtime)
    print("nrBS: ", nrBS)
    print("Full Collision: ", full_collision)
    print("with directionality: ", directionality)
    #print("nrNetworks: ", nrNetworks)
    print("Plan: ", plan[planid])
    print("baseDist: ", baseDist)   # x-distance between the two base stations

else:
    print("usage: ./directionalLoraIntf.py <nodes> <avgsend> <experiment> <simtime> <nrBS> <collision> <directionality> <networks> <basedist>")
    print("experiment 0 and 1 use 1 frequency only")
    exit(-1)


# global stuff
nodes = []
packetsAtBS = []
env = simpy.Environment()


# max distance: 300m in city, 3000 m outside (5 km Utz experiment)
# also more unit-disc like according to Utz
nrCollisions = 0
nrReceived = 0
nrProcessed = 0

# global value of packet sequence numbers
packetSeq = 0

# list of received packets
recPackets=[]
collidedPackets=[]
lostPackets = []


sensi = np.array([sf7,sf8,sf9,sf10,sf11,sf12])

## figure out the minimal sensitivity for the given experiment
minsensi = sensi[5,2] 
'''
if experiment in [0,1,4]:
    minsensi = sensi[5,2]  # 5th row is SF12, 2nd column is BW125
elif experiment == 2:
    minsensi = -112.0   # no experiments, so value from datasheet
elif experiment == 3:
    minsensi = np.amin(sensi) ## Experiment 3 can use any setting, so take minimum
'''
    
Lpl = Ptx - minsensi
print("amin", minsensi, "Lpl", Lpl)
#BW125KhzSF12
#maxDist = d0*(math.e**((Lpl-Lpld0)/(10.0*gamma)))
maxDist = d0*(10**((Lpl-Lpld0)/(10.0*gamma)))
print("maxDist:", maxDist)
distanceSf()

# size of area
xmax = maxDist*(nrBS+2) + 20
ymax = maxDist*(nrBS+1) + 20

# maximum number of packets the BS can receive at the same time
maxBSReceives = 8

maxX = maxDist + baseDist*(nrBS) 
print("maxX ", maxX)
maxY = 2 * maxDist * math.sin(30*(math.pi/180)) # == maxdist
print("maxY", maxY)

# prepare graphics and add sink
if (graphics == 1):    
    plt.ion()
    plt.figure()
    ax = plt.gcf().gca()

# list of base stations
#global bsNode = []

# list of packets at each base station, init with 0 packets
packetsAtBS = []
packetsRecBS = []
for i in range(0,nrBS):
    b = myBS(i)
    bsNode.append(b)
    #这两个队列是干啥的
    packetsAtBS.append([]) #基站当前在处理的节点
    packetsRecBS.append([])#基站接收到的报文序列
    bsState.append(0)#保存基站的状态



#for i in range(0,nrNodes):
    # myNode takes period (in ms), base station id packetlen (in Bytes)
    # 1000000 = 16 min
filenode = "nodes"+str(nrNodes)+"_Plan"+str(planid)+".txt"
fileExist = False
if (os.path.isfile(filenode)):
    nodefile = open(filenode, "r")
    fileExist = True
    #print("open filename: ", filenode, ",file.close() = ", nodefile.closed)
nodeid = 0
for j in range(0,nrBS):
    for i in range(0, int(plan[planid][j] * nrNodes)):
        x = 0
        y = 0
        if fileExist == True:
            line = nodefile.readline()
            position = line.split(' ')
            #print("Get node position: ", position)
            if (len(position) == 3):
                x = float(position[0])
                y = float(position[1])
                nodeid = float(position[2])
        # create nrNodes for each base station
        #if (nodeid == -1):
         #   nodeid = j * plan[planid][j] + i
        nodeid = nodeid+ 1
        #node = myNode(i*nrBS+j, avgSendTime,20,bsNode[j])
        node = myNode(nodeid, avgSendTime,20,bsNode[j], fileExist, x, y)
        nodes.append(node)
        
        # when we add directionality, we update the RSSI here
        #定向天线
        if (directionality == 1):
            node.updateRSSI()
        #处理发送 - 添加仿真进程
        env.process(transmit(env,node))

#prepare show
if fileExist == True:
    nodefile.close()
# start simulation
env.run(until=simtime)

#根据节点所使用的下行基站划分颜色
for node in nodes:
    # graphics for node
    #global graphics
    if (graphics == 1):
        #global ax
        if (node.downgw == 0):
                ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='blue'))
                '''
                if (node.sf == 7):
                    ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='powderblue'))
                if (node.sf == 8):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='lightblue'))
                if (node.sf == 9):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='lightskyblue'))
                if (node.sf == 10):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='skyblue'))
                if (node.sf == 11):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='deepskyblue'))
                if (node.sf == 12):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='blue'))
                '''
        elif (node.downgw == 1):
                ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='red'))
                '''
                if (node.sf == 7):
                    ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='lightsalmon'))
                if (node.sf == 8):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='coral'))
                if (node.sf == 9):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='tomato'))
                if (node.sf == 10):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='red'))
                if (node.sf == 11):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='indianred'))
                if (node.sf == 12):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='brown'))
                '''
        elif (node.downgw == 2):
                ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='green'))
                '''
                if (node.sf == 7):
                    ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='palegreen'))
                if (node.sf == 8):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='olive'))
                if (node.sf == 9):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='y'))
                if (node.sf == 10):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='darkseagreen'))
                if (node.sf == 11):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='lawngreen'))
                if (node.sf == 12):
                        ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='olivedrab'))
                '''
        elif (node.downgw == 3):
                ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='brown'))
                if (node.sf == 7):
                    ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='blue'))
                if (node.sf == 8):
                        ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='red'))
                if (node.sf == 9):
                        ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='green'))
                if (node.sf == 10):
                        ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='brown'))
                if (node.sf == 11):
                        ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='orange'))
                if (node.sf == 12):
                        ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='yellow'))
        elif (node.downgw == 4):
                ax.add_artist(plt.Circle((node.x, node.y), 4, fill=True, color='orange'))
        else :
            print("node[",node.id,"] DownGw: ", node.downgw)
'''
#根据节点所使用的速率划分颜色
for node in nodes:
    # graphics for node
    #global graphics
    if (graphics == 1):
        #global ax
        if (node.sf == 7):
                ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='blue'))
        if (node.sf == 8):
                ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='red'))
        if (node.sf == 9):
                ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='green'))
        if (node.sf == 10):
                ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='brown'))
        if (node.sf == 11):
                ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='orange'))
        if (node.sf == 12):
                ax.add_artist(plt.Circle((node.x, node.y), 2, fill=True, color='yellow'))
'''
if (graphics == 1):
    plt.xlim([0, maxX+50])
    plt.ylim([0, maxX+50])
    
    plt.xlabel("Distance(m)", fontsize=12)
    plt.ylabel("Distance(m)", fontsize=12)
    plt.draw()
    plt.show()  

# print(stats and save into file
print("nr received packets (independent of right base station)", len(recPackets))
print("nr collided packets", len(collidedPackets))
print("nr lost packets (not correct)", len(lostPackets))

sum = 0
for i in range(0,nrBS):
    print("packets at BS",i, ":", len(packetsRecBS[i]))
    sum = sum + len(packetsRecBS[i])
print("sent packets: ", packetSeq)
print("overall received at right BS: ", sum)

sumSent = 0
sent = []
for i in range(0, nrBS):
    sent.append(0)

#for i in range(0,nrNodes*nrBS):

for i in range(0,nrNodes):
    sumSent = sumSent + nodes[i].sent
    #print("id for node ", nodes[i].id, "BS:", nodes[i].bs.id," SF: ", nodes[i].sf, " sent: ", nodes[i].sent)
    sent[nodes[i].bs.id] = sent[nodes[i].bs.id] + nodes[i].sent

for i in range(0, nrBS):
    print("send to BS[",i,"]:", sent[i])

print("sumSent: ", sumSent)

der = []
# data extraction rate
derALL = len(recPackets)/float(sumSent)
sumder = 0

print("SF_STAT：", sfstat)
for i in range(0, nrBS):
    if (sent[i] > 0):
        der.append(len(packetsRecBS[i])/float(sent[i]))
    print("Node BS[",i,"]: ", plan[planid][i]*nrNodes)
    print("DER BS[",i,"]:", der[i])
    sumder = sumder + der[i]
    print("Tx Drop Bs[",i,"]:", bsNode[i].tx_lost)
    print("downCnt BS[",i,"]:", bsNode[i].downCnt)
    print("channel Util BS[",i,"]:", [x/simtime for x in bsNode[i].chnelUtil])
    
'''    
    print("simutime: ", simtime)
    print("Load BS[",i,"]:", bsNode[i].work_time* 100/simtime,"%")
    print("tx Util BS[",i,"]:", bsNode[i].tx_util / simtime)
    print("dropPkt BS[",i,"]:", bsNode[i].dropPkt)
    print("sfstat_lost BS[",i,"]:", bsNode[i].sfstat_lost)
    print("sfstat_collision BS[",i,"]:", bsNode[i].sfstat_collision)
    print("sfstat_recv BS[",i,"]:", bsNode[i].sfstat_recv)
'''

avgDER = (sumder)/nrBS
print("avg DER: ", avgDER)
print("DER with 1 network:", derALL)
print("Node Num:", nrNodes,", Distribute: ", plan[planid])
authlog = ["","Signal First", "Weight-Mean","Load-Balance", "Nothting"]
print("Downlink Routing Algorithm: ", authlog[experiment])
print("----------------------------------------------------------------")
print('|{:^5s}|{:^10s}|{:^10s}|{:^10s}|{:^10s}|'.format('基站ID','上行负载(%)','下行负载 (%)','总负载(%)','DER(%)'))

#directionalLoraIntf.py 1000 1000000 2 15000000 3 2 0 0 450

for i in range(0, nrBS):
    print('|{:^7d}|{:^14.2f}|{:^14.2f}|{:^13.2f}|{:^10.2f}|'.format(i, bsNode[i].rx_time *100/simtime, bsNode[i].tx_util*100/simtime, bsNode[i].work_time/simtime*100, der[i]*100))
print("----------------------------------------------------------------")


# this can be done to keep graphics visible
if (graphics == 1):
    input('Press Enter to continue ...')

# store nodes and basestation locations
filenode = "nodes"+str(nrNodes)+"_Plan"+str(planid)+".txt"
with open(filenode, 'w') as nfile:
    for node in nodes:
        nfile.write('{x} {y} {id}\n'.format(**vars(node)))

with open('basestation.txt', 'w') as bfile:
    for basestation in bsNode:
        bfile.write('{x} {y} {id}\n'.format(**vars(basestation)))
# save experiment data into a dat file that can be read by e.g. gnuplot
# name of file would be:  exp0.dat for experiment 0
fname = "exp" + str(experiment) + "d99" + "BS" + str(nrBS) + "Intf.dat"
print(fname)
if os.path.isfile(fname):
    res = "\n" + str(nrNodes) + " " + str(der[0]) 
else:
    res = "# nrNodes DER0 AVG-DER\n" + str(nrNodes) + " " + str(der[0]) + " " + str(avgDER) 
with open(fname, "a") as myfile:
    myfile.write(res)
'''   
    for i in range(0, nrBS):
        myfile.write("===============================BS[",i,"] INFO==============================")
        if (sent[i] > 0):
            der.append(len(packetsRecBS[i])/float(sent[i]))
        myfile.write("Node BS[",i,"]: ", plan[planid][i]*nrNodes)
        myfile.write("DER BS[",i,"]:", der[i])
        #sumder = sumder + der[i]
        myfile.write("simutime: ", simtime)
        myfile.write("Load BS[",i,"]:", bsNode[i].work_time* 100/simtime,"%")
        myfile.write("tx Util BS[",i,"]:", bsNode[i].tx_util / simtime)
        myfile.write("channel Util BS[",i,"]:", [x/simtime for x in bsNode[i].chnelUtil])
        myfile.write("downCnt BS[",i,"]:", bsNode[i].downCnt)
        myfile.write("dropPkt BS[",i,"]:", bsNode[i].dropPkt)
        myfile.write("sfstat_lost BS[",i,"]:", bsNode[i].sfstat_lost)
        myfile.write("sfstat_collision BS[",i,"]:", bsNode[i].sfstat_collision)
        myfile.write("sfstat_recv BS[",i,"]:", bsNode[i].sfstat_recv)
'''
myfile.close()

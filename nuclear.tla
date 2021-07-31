------------------------------ MODULE nuclear ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC
----------------------------------------------------------------------------
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])

Max(a, b) == IF a > b THEN a ELSE b
MaxV(set) == CHOOSE s \in set: \A v \in set: s >= v
----------------------------------------------------------------------------
CONSTANTS
    Group,
    G2P,
    Msg,    \* the set of messages, ranged over by m
    Proc,   \* the set of processes, ranged over by p
    Dest,    \* Dest[m] \subseteq Proc: the set of destination processes of m \in Msg
    Cur_leader,
    Quorum
    
ASSUME
    /\ Dest \in [Msg -> SUBSET Group]   
    /\ Cur_leader  \in [Group -> SUBSET Proc]
        
    
Priority == CHOOSE f \in [Proc -> 1 .. Cardinality(Proc)] : Injective(f)

p2g(p) == CHOOSE g \in Group : p \in G2P[g]
-----------------------------------------------------------------------------
VARIABLES
    clock,      \* clock[p]: the clock at process p \in Proc
    phase,      \* phase[p][m]: the phase of the message m \in Msg at process p \in Proc
    localTS,    \* localTS[p][m]: the local ts of the message m \in Msg at process p \in Proc
    globalTS,   \* globalTS[p][m]: the global ts of the message m \in Msg at process p \in Proc
    delivered,  \* delivered[p][m]: has m \in Msg been delivered at process p \in Proc
    incoming,   \* incoming[p] \subseteq Message (defined below): the incoming channel of process p \in Proc
    cballot,
    hasmaxlts,   \* 
    max_delivered_gts,
    sent        \* sent \subseteq Msg: the set of messages that have been multicast; only for TLC
        
pvars == <<clock, phase, localTS, globalTS, delivered,cballot,hasmaxlts,max_delivered_gts>>
vars == <<clock, phase, localTS, globalTS, delivered, incoming, sent, cballot, hasmaxlts,max_delivered_gts>>
----------------------------------------------------------------------------
MaxCounter == Cardinality(Msg) * Cardinality(Proc)

TS == [c : 0 .. MaxCounter, g : Group] \* c for counter  

 
MaxTS2(vs) == CHOOSE u \in vs: \A v \in vs: u.c >= v.c


PinDestLeader(p,gset) == \E g \in gset : p \in Cur_leader[g]
PinDest(p,gset) == \E g \in gset : p \in G2P[g]

----------------------------------------------------------------------------
Message == [type : {"MULTICAST"}, m : Msg]
    \cup [type : {"ACCEPT"}, m : Msg, g : Group, b : 0 .. MaxCounter ,lts : TS]
    \cup [type : {"ACCEPT_ACK"}, m : Msg, g : Group, b : 0 .. MaxCounter, acc : Proc]
    \cup [type : {"DELIVER"}, m : Msg, b : 0 .. MaxCounter, lts : TS, gts : TS]

Send(msg) == \* Send msg \in Message to its destination processes
    incoming' = [p \in Proc |->
        IF PinDest(p, Dest[msg.m]) THEN incoming[p] \cup {msg}
                             ELSE incoming[p]]

SendAndRemove(smsg, sender, rmsg) == 
    incoming' = [p \in Proc |->
        IF p = sender THEN (incoming[sender] \cup {smsg}) \ {rmsg}
                      ELSE IF PinDest(p,Dest[smsg.m]) THEN incoming[p] \cup {smsg}
                                                 ELSE incoming[p]]
     
     
     
     
     
SendAndRemove2(smsg, sender, rmsg) == 
    incoming' = [p \in Proc |->
        IF p = sender THEN (incoming[sender] \cup smsg) \ rmsg
                      ELSE IF p \in G2P[p2g(sender)] THEN incoming[p] \cup smsg
                                                 ELSE incoming[p]]                                                 
                                                 
                                                 
Send2Leader(msg) == \* Send msg \in Message to its destination leaders
    incoming' = [p \in Proc |->
        IF PinDestLeader(p, Dest[msg.m])   THEN incoming[p] \cup {msg}
                             ELSE incoming[p]]
----------------------------------------------------------------------------
                                                 
                                                 
                                                 
TypeOK ==
    /\ clock     \in [Proc -> 0 .. MaxCounter]
    /\ phase     \in [Proc -> [Msg -> {"START", "PROPOSED",  "ACCEPTED","COMMITTED"}]]
    /\ localTS   \in [Proc -> [Msg -> TS]]
    /\ max_delivered_gts \in [Proc -> [Msg -> TS]]
    /\ globalTS  \in [Proc -> [Msg -> TS]]
    /\ delivered \in [Proc -> [Msg -> BOOLEAN]]
    /\ incoming  \in [Proc -> SUBSET Message]
    /\ sent      \subseteq Msg  \cup {"test"}
    /\ hasmaxlts \in [Proc -> [Msg -> TS]]
    /\ cballot   \in [Proc -> [Msg -> 0 .. MaxCounter]]
----------------------------------------------------------------------------
Init ==
    /\ clock     = [p \in Proc |-> 0]
    /\ phase     = [p \in Proc |-> [m \in Msg |-> "START"]]
    /\ localTS   = [p \in Proc |-> [m \in Msg |-> [c |-> 0, g |-> p2g(p)]]]
    /\ max_delivered_gts = [p \in Proc |-> [m \in Msg |-> [c |-> 0, g |-> p2g(p)]]]    
    /\ globalTS  = [p \in Proc |-> [m \in Msg |-> [c |-> 0, g |-> p2g(p)]]]
    /\ delivered = [p \in Proc |-> [m \in Msg |-> FALSE]]
    /\ incoming  = [p \in Proc |-> {}]
    /\ hasmaxlts  = [p \in Proc |-> [m \in Msg |-> [c |-> 0, g |-> p2g(p)]]]
    /\ sent      = {}
    /\ cballot   = [p \in Proc |-> [m \in Msg |-> 0]]
----------------------------------------------------------------------------
Multicast(m) == 
    /\ m \in Msg \ sent
    /\ sent' = sent \cup {m}
   \* /\ Send([type |-> "MULTICAST", m |-> m])
    /\ Send2Leader([type |-> "MULTICAST", m |-> m])
    
    /\ UNCHANGED pvars
    
    
    


    
    
    
recMulticast(p) == 
    \E msg \in incoming[p]:
        /\ msg.type = "MULTICAST"
        /\ IF phase[p][msg.m] = "START" 
           THEN (/\ clock' = [clock EXCEPT ![p] = @ + 1] 
                 /\ localTS' = [localTS EXCEPT ![p][msg.m] = [c |-> clock'[p], g |-> p2g(p)]] 
                 /\ phase' = [phase EXCEPT ![p][msg.m] = "PROPOSED"]) 
           ELSE  UNCHANGED <<clock,localTS,phase>>
        /\ SendAndRemove([type |-> "ACCEPT", m |-> msg.m, g |-> p2g(p), b |-> cballot[p][msg.m], lts |-> localTS'[p][msg.m]], p, msg)  
        /\ UNCHANGED  << globalTS, delivered, sent,cballot, hasmaxlts,max_delivered_gts>>
    
    
    
    
    
recAccept(p) == 
    \E msg \in incoming[p]:
        /\ msg.type = "ACCEPT"    
        /\ cballot[p][msg.m] = msg.b
        /\ IF phase[p][msg.m] \in {"START", "PROPOSED"} 
           THEN phase' = [phase EXCEPT ![p][msg.m] = "ACCEPTED"]
           ELSE UNCHANGED phase
        /\ localTS' = [localTS EXCEPT ![p][msg.m] = msg.lts]
        /\ clock' = [clock EXCEPT ![p] =  Max(@,   MaxV({msg1.lts.c : msg1 \in {msg2 \in incoming[p] : msg2.type = "ACCEPT" /\ msg2.m = msg.m}  } ) )  ]      \*
        /\ hasmaxlts' = [hasmaxlts EXCEPT ![p][msg.m]  =  MaxTS2( {@,  msg.lts} )  ]   
        /\ SendAndRemove([type |-> "ACCEPT_ACK", m |-> msg.m, g |-> p2g(p), b |-> cballot[p][msg.m] , acc |-> p  ], p, msg)  
        /\ UNCHANGED << globalTS, delivered, sent, cballot, max_delivered_gts>>
    
    
    
    
recAck(p,m) == 
        /\ p \in  Cur_leader[p2g(p)]
        /\ \E Q \in Quorum[p2g(p)] :    
               LET mset == {msg \in incoming[p] : /\ msg.type = "ACCEPT_ACK"
                                                  /\ msg.m = m
                                                  /\ msg.g = p2g(p)
                                                  /\ msg.b = cballot[p][msg.m] 
                                                  /\ msg.acc  \in Q}
                                                  
               IN /\ \A ac \in Q : \E msg \in mset : msg.acc = ac
               
                  /\ globalTS' = [globalTS EXCEPT ![p][m] = hasmaxlts[p][m]]
               
                  /\ phase' = [phase EXCEPT ![p][m] = "COMMITTED"]
     
                  /\ LET readym == {rm \in Msg :
                                /\ phase'[p][rm] = "COMMITTED"
                                /\ delivered[p][rm] = FALSE
                                /\ \A pm \in Msg :
                                    phase'[p][pm] \in {"PROPOSED","ACCEPTED"}
                                                                => localTS[p][pm].c > globalTS'[p][rm].c }
                                                                
                     IN  /\ delivered' = [delivered EXCEPT ![p] = [pm \in Msg |->
                                                                              IF pm \in readym THEN TRUE ELSE @[pm]]]
                                                                              
                         /\ SendAndRemove2(  { [type |-> "DELIVER", m |-> tm,  b |-> cballot[p][tm],  lts |-> localTS[p][tm]   ,  gts |-> globalTS'[p][tm]  ]   : tm \in  readym    },    p, mset)
    
    
                  /\ UNCHANGED <<clock, localTS, sent, cballot, hasmaxlts, max_delivered_gts>>
    
    
    
    
    
    
    
    
deliver(p) == 
    \E msg \in incoming[p]:
        /\ msg.type = "DELIVER"    
        /\ cballot[p][msg.m] = msg.b    
        /\ msg.gts.c > max_delivered_gts[p][msg.m].c
        /\ phase' = [phase EXCEPT ![p][msg.m] = "COMMITTED"]
        /\ localTS' = [localTS EXCEPT ![p][msg.m] = msg.lts]
        /\ max_delivered_gts' = [max_delivered_gts EXCEPT ![p][msg.m] = msg.gts]        
        /\ globalTS' = [globalTS EXCEPT ![p][msg.m] = msg.gts]
        /\ clock' = [clock EXCEPT ![p] =  Max(@,msg.gts.c )  ]
        /\ UNCHANGED <<delivered, incoming, sent, cballot, hasmaxlts>>
        
    
---------------------------------------------------------------------------------
Next ==
    \/ \E m \in Msg: Multicast(m)
    \/ \E p \in Proc:
        \/ recMulticast(p)
        \/ recAccept(p)
        \/ \E m \in Msg: recAck(p,m)
        \/ deliver(p)
        
        
        

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------

----------------------------------------------------------------------------
THEOREM TypeTheorem == Spec => []TypeOK


=============================================================================
\* Modification History
\* Last modified Sat Jul 31 00:01:36 CST 2021 by eric
\* Created Thu Jul 29 16:06:02 CST 2021 by eric

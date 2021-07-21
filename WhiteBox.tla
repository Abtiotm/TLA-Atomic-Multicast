------------------------------ MODULE WhiteBox ------------------------------

EXTENDS Integers

CONSTANT Processor,     \* {"p1","p2","p3"}
         status,        \* [p1 |-> "LEADER", p2 |-> "FOLLOWER", p3 |-> "LEADER"]
         Majority,      \*{"g1"->{"p1","p2"}},"g2"->{"p1"}} 
         Chat,          \* 原文m改为c  {"c1"}
         Destination,   \* {"c1"->{"g1","g2"}}//,"c2"->{"g1"}} 
\*         Leader,
         Group,          \* [p1 |-> "g1", p2 |-> "g1", p3 |-> "g2"]
         GSet           \*{"g1","g2"}         



\*ASSUME  
\*  /\ Majority \subseteq SUBSET Processor
\*  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}


Messages ==
  [type : {"MULTICAST"}, chat : Chat]  
      \cup
  [type : {"ACCEPT"},  chat : Chat , g : GSet ,lts : (Nat \cup {-1})] 
      \cup
  [type : {"ACCEPT_ACK"}, chat : Chat ,  acc : Processor]  \* 加入acc
      \cup                              
  [type : {"DELIVER"}, chat : Chat , lts : Nat \cup {-1} , gts : Nat \cup {-1}, g : GSet] \* 加入g0





Maximum(S) == 
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m


dest(c) == Destination[c]










VARIABLES
\*  status, 
  Phase,
  LocalTS,
  GlobalTS,
  clock,
  Delivered,

  max_delivered_gts,
  msgs


MaxLTS(ltsc) == ltsc[ CHOOSE p \in Processor : \A p1 \in Processor : ltsc[p] \geq ltsc[p1] ]

\*MaxLTS(c) == CHOOSE p \in Processor :  \A  p1 \in Processor: LocalTS[c][p1]  \leq LocalTS[c][p] 



-----------------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}



MinD(S) == 
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : GlobalTS[n] \leq GlobalTS[m]
  

\* GlobalTS 各p唯一
RECURSIVE setD(_)
setD(S) == IF S = {} THEN FALSE
                     ELSE /\ Delivered' = [Delivered EXCEPT ![CHOOSE m1 \in S : m1 = MinD(S)] = TRUE] 
                          /\ setD(S \ {CHOOSE m1 \in S : m1 = MinD(S)})


TypeOK ==  
\*  /\ status \in {"LEADER","FOLLOWER","RECOVERING"}
  /\ clock \in Nat
  /\ LocalTS \in Nat \cup {-1}
  /\ GlobalTS  \in Nat \cup {-1}
  /\ Phase \in {"START","PROPOSED","ACCEPTED"}
  /\ Delivered \in {TRUE,FALSE}
  /\ max_delivered_gts \in Nat
  /\ msgs \subseteq Messages

Init ==  \* The initial predicate.
\*  /\ status = [p \in Processor |-> 0]
  /\ clock = [p \in Processor |-> 0]
  /\ Phase = [c \in Chat |-> "START"]
  /\ Delivered = [c \in Chat |-> FALSE]
  /\ GlobalTS = [c \in Chat |-> [p \in Processor |-> -1]]
  /\ LocalTS  = [c \in Chat |-> [p \in Processor |-> -1]]
  /\ max_delivered_gts = [p \in Processor |-> 0]



  
  /\ msgs = {}
-----------------------------------------------------------------------------
multicast(c) ==   /\ Send([type |-> "MULTICAST", chat |-> c])
                  /\ UNCHANGED << Phase,LocalTS,GlobalTS,clock,Delivered,max_delivered_gts>>


\* 收到MULTICAST(m)后发送ACCEPT(m,g0,cballot,LocalTS[m])                  
sendACC(c,p) == /\ Group[p] \in dest(c)
                /\ status[p] = "LEADER"
                /\ \E m \in msgs :  /\ m.type = "MULTICAST"
                                    /\ m.chat = c
                
                                    
                                    /\ (/\ Phase[c] = "START" 
                                        /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
                                        /\ LocalTS' = [LocalTS EXCEPT ![c][p] = clock[p] ]
                                        /\ Phase' = [Phase EXCEPT ![c] = "PROPOSED"])
                                       
                                    /\ Send([type |-> "ACCEPT", chat |-> c, g |-> Group[p] ,lts |-> LocalTS[c][p]])
                                    /\ UNCHANGED <<GlobalTS,Delivered,max_delivered_gts>>

\* 收到ACCEPT(m,g0,cballot,LocalTS[m]) 后发送ACCEPT_ACK(m,g0,Bal)
sendACK(c,p) ==  /\ Group[p] \in dest(c)
                 /\ status[p] \in {"LEADER","FOLLOWER"}
                 /\ \E m \in msgs :    /\ m.type = "ACCEPT"
                                       /\ m.chat = c
                                       /\ m.g = Group[p]

                                       /\ (/\ Phase[c] \in {"START","PROPOSED"} /\ Phase' = [Phase EXCEPT ![c] = "ACCEPTED"] )
                                       /\ LocalTS' = [LocalTS EXCEPT ![c][p] = m.lts]
                                       /\ clock' = [clock EXCEPT ![p] = IF clock[p] \geq MaxLTS(LocalTS[c]) THEN clock[p] ELSE MaxLTS(LocalTS[c]) ] 
                                       /\ Send([type |-> "ACCEPT_ACK", chat |-> c,  acc |-> p])
                                       /\ UNCHANGED <<GlobalTS,Delivered,max_delivered_gts>>



\* 收到ACCEPT_ACK(m,g0,Bal)后发送deliver(c,b,lts,gts)
sendDeliver(c,p) ==  /\ Group[p] \in dest(c)
                     /\ status[p] = "LEADER"
                     /\ \E MS \in Majority[Group[p]] :    
                            LET mset == {m \in msgs : /\ m.type = "ACCEPT_ACK"
                                                      /\ m.chat  = c}

                            IN  /\ \A ac \in MS : \E m \in mset : /\ m.acc = ac
                                                                  /\ GlobalTS' = [GlobalTS EXCEPT ![c][p] = MaxLTS(LocalTS[c]) ]
                                                                  /\ Phase' = [Phase EXCEPT ![c][p] = "COMMITTED"]
                                
                                                                  /\ LET cset == {m1 \in mset : /\ Phase[m1.chat] = "COMMITTED"
                                                                                                /\ Delivered[m1.chat] = FALSE
                                                                                                /\ \A m2 \in msgs : (Phase[m2.chat] \in {"ACCEPTED","PROPOSED"} /\ \A p2 \in Processor : LocalTS[m2.chat][p2] > GlobalTS[m1.chat][p])
                                                                                                
                                                                                 }
                                                                     IN setD(cset)
                                
                                
                                /\ Send([type |-> "DELIVER", chat |-> c,  lts |-> LocalTS[c][p], gts |->GlobalTS[c][p], g |-> Group[p] ])
                     /\ UNCHANGED <<LocalTS,clock,max_delivered_gts>>
    


deliver(c,p) == 
                        /\ \E m \in msgs :  /\ m.g = Group[p]
                                            /\ m.type = "DELIVER"
                                            /\ m.chat = c
                                            /\ status[p] \in {"FOLLOWER","LEADER"} 

                                            /\ Phase' = [Phase EXCEPT ![c] = "COMMITTED"]
                                            /\ LocalTS' = [LocalTS EXCEPT ![c][p] = m.lts]
                                            /\ GlobalTS' = [GlobalTS EXCEPT ![c][p] = m.gts]
                                            /\ clock' = [clock EXCEPT ![p] = Maximum({clock,m.gts})]
                                            /\ max_delivered_gts' = [ max_delivered_gts EXCEPT ![p] = m.gts ]   
                        /\ UNCHANGED <<Delivered,msgs>>


----------------------------------------------------------------------------
Next ==  \* The next-state action
  \/ \E p \in Processor : \E c \in Chat:   \/ multicast(c)
                                           \/ sendACC(c,p)
                                           \/ sendACK(c,p)
                                           \/ sendDeliver(c,p)
\*                                           \/ deliver(c,p)

Spec == Init /\ [][Next]_<< Phase,LocalTS, GlobalTS, clock, Delivered,max_delivered_gts,msgs>>

THEOREM Spec => []TypeOK
=============================================================================
\* Modification History
\* Last modified Tue Jul 20 14:54:31 CST 2021 by eric
\* Created Sun Jun 27 10:41:14 CST 2021 by eric

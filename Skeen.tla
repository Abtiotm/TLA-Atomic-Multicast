------------------------------- MODULE Skeen -------------------------------
EXTENDS Integers

\*Maximum(S) == 
\*  IF S = {} THEN -1
\*            ELSE CHOOSE n \in S : \A m \in S : n \geq m

Max(S) == CHOOSE x \in S : \A y \in S : y <= x


                      
            
CONSTANT Processor, \* {"p1","p2","p3"}
         Chat    \* 原文m改为c  {"c1","c2"}
\*         State,
\*         Destination,   \* {"c1"->{"g1","g2"},"c2"->{"g1"}}         
\*         Group,          \* [p1 |-> "g1", p2 |-> "g1", p3 |-> "g2"]
\*         GSet           \*{"g1","g2"}

\*dest(c) == Destination[c]














-----------------------------------------------------------------
VARIABLES
  clock,     \*clock[p]
  Phase,     \*Phase[m]
  LocalTS,   \*LocalTS[m][p]
  GlobalTS,  \*GlobalTS[m][p]
\*   maxLTS, 
  Delivered, \*Delivered[m]
\*   dSet,
  msgs
  
  
  
  
  
  
  

Message ==
  [type : {"MULTICAST"}, chat : Chat] 
      \cup
  [type : {"PROPOSE"}, chat : Chat, lts : [Processor -> Nat]] \* g0 : GSet, 
\*      \cup
\*  [type : {"deliver"}, m : Message] 



MaxLTS(lts) == CHOOSE x \in Processor : \A p \in Processor : lts[p] <= lts[x]


  
  
MinD(S) == 
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : GlobalTS[n] \leq GlobalTS[m]
  

\* GlobalTS 各p唯一
RECURSIVE setD(_)
setD(S) == IF S = {} THEN FALSE
                     ELSE /\ Delivered' = [Delivered EXCEPT ![CHOOSE m1 \in S : m1 = MinD(S)] = TRUE] 
                          /\ setD(S \ {CHOOSE m1 \in S : m1 = MinD(S)})
  
  
  
  
  

  
  
SKTypeOK ==  
  /\ Phase \in [Chat -> {"START", "PROPOSED", "COMMITTED"}]
  /\ Delivered \in [Chat -> {TRUE, FALSE}]
  /\ clock \in [Processor -> Nat]
  /\ GlobalTS \in [Chat -> [Processor -> (Nat \cup {-1})]]
  /\ LocalTS \in [Chat ->[Processor -> (Nat \cup {-1})]]
  /\ msgs \subseteq Message
  
SKInit ==  \* The initial predicate.
  /\ Phase = [c \in Chat |-> "START"]
  /\ clock = [p \in Processor |-> 0]
\*   /\ maxLTS = [Message |-> -1]
  /\ GlobalTS = [c \in Chat|-> 
                   [p \in Processor |-> 0]]
  /\ LocalTS  = [c \in Chat|-> 
                   [p \in Processor |-> 0]]
  /\ Delivered = [c \in Chat |-> FALSE]
  /\ msgs = {}  

-------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}
-------------------------------------------------------------------
\* 广播m
multicast(c) == /\ Send([type |-> "MULTICAST", chat |-> c])
                /\ UNCHANGED<< clock,Phase,LocalTS,GlobalTS,Delivered >>
                

\* 收到MULTICAST(m)后发送PROPOSE(m,g0,LocalTS[m])
propose(c,p) == \* /\ Group[p] \in dest(c)
                /\ \E msg \in msgs :  /\ msg.type = "MULTICAST"
                                      /\ msg.chat = c
                                      /\ clock' = [clock EXCEPT ![p] = clock[p]+1]
                                      /\ LocalTS' = [LocalTS EXCEPT ![c][p] = clock[p]]
                                      /\ Phase' = [Phase EXCEPT ![c] = "PROPOSED"]
                                      /\ Send([type |-> "PROPOSE", chat |-> c, lts |-> LocalTS[c] ])  \* g0 |-> Group[p], 
                                      /\ UNCHANGED<<GlobalTS,Delivered>>


\* 收到PROPOSE(m,g,Lts(g))后deliver(m')
deliver3(c,p) == /\ \E msg \in msgs : /\ msg.type = "PROPOSE"
                                      /\ msg.chat = c
                                      \* /\ msg.g0 = Group[p]
                                      /\ GlobalTS' = [GlobalTS EXCEPT ![c][p] = msg.lts[MaxLTS(msg.lts)]]\*LocalTS[c][CHOOSE x \in Processor: \A y \in Processor : LocalTS[c][y] <= LocalTS[c][x]]]\*MaxLTS(LocalTS[c])]\*Max(LocalTS[c])]\*
                                      /\ clock' = [clock EXCEPT ![p] = IF clock[p] \geq GlobalTS[c][p] THEN clock[p] ELSE GlobalTS[c][p]]
                                      /\ Phase' = [Phase EXCEPT ![c] = "COMMITTED"]


                                      /\ LET cset == {m1 \in msgs : /\ Phase[m1.chat] = "COMMITTED"
                                                                    /\ Delivered[m1.chat] = FALSE
                                                                    /\ \A m2 \in msgs : Phase[m2.chat] = "PROPOSED" /\ \A p2 \in Processor : LocalTS[m2.chat][p2] > GlobalTS[m1.chat][p]}
                                         IN setD(cset)
                                       
                                        
                                        
                                        
                                        \* \E c1a \in Message : \A c1b \in Message:/\ Phase[c1a][p] = "COMMITTED"
                                        \*                                            /\ Phase[c1b][p] = "COMMITTED"
                                        \*                                            /\ Delivered[c1] = False
                                        
                                        \*                                            /\ \A c2 \in Message : IF (Phase[c2][p] = "PROPOSED" /\ LocalTS[c2][p] > GlobalTS[c2]
                                        \*                                               THEN Delivered' = [Delivered EXCEPT ![c2] = True]
                                      /\ UNCHANGED<<msgs,LocalTS>>                          
----------------------------------------------------------------------------
SKNext ==  \/ \E c \in Chat:  \/ multicast(c)
                              \/ \E p \in Processor : propose(c,p) \/ deliver3(c,p)
                                           


SKSpec == SKInit /\ [][SKNext]_<<clock,Phase,LocalTS,GlobalTS,Delivered,msgs>>

THEOREM SKSpec => []SKTypeOK
=============================================================================
\* Modification History
\* Last modified Thu Jul 08 20:18:10 CST 2021 by eric
\* Created Sat Jun 26 16:04:39 CST 2021 by eric

------------------------------- MODULE Skeen -------------------------------
(*
The specification of Skeen's protocol for atomic multicast;
see Section III of the DSN2019 paper "White-Box Atomic Multicast"
by Alexey Gotsman, Anatole Lefort, and Gregory Chockler.
*)
EXTENDS Naturals, Sequences, FiniteSets, TLC
----------------------------------------------------------------------------
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])

Max(a, b) == IF a > b THEN a ELSE b
----------------------------------------------------------------------------
CONSTANTS
    Msg,    \* the set of messages, ranged over by m
    Proc,   \* the set of processes, ranged over by p
    Dest    \* Dest[m] \subseteq Proc: the set of destination processes of m \in Msg
    
ASSUME
    /\ Dest \in [Msg -> SUBSET Proc]

Priority == CHOOSE f \in [Proc -> 1 .. Cardinality(Proc)] : Injective(f)
----------------------------------------------------------------------------
VARIABLES
    clock,      \* clock[p]: the clock at process p \in Proc
    phase,      \* phase[p][m]: the phase of the message m \in Msg at process p \in Proc
    localTS,    \* localTS[p][m]: the local ts of the message m \in Msg at process p \in Proc
    globalTS,   \* globalTS[p][m]: the global ts of the message m \in Msg at process p \in Proc
    delivered,  \* delivered[p][m]: has m \in Msg been delivered at process p \in Proc
    incoming,   \* incoming[p] \subseteq Message (defined below): the incoming channel of process p \in Proc
    sent        \* sent \subseteq Msg: the set of messages that have been multicast; only for TLC
    
pvars == <<clock, phase, localTS, globalTS, delivered>>
vars == <<clock, phase, localTS, globalTS, delivered, incoming, sent>>
----------------------------------------------------------------------------
TS == [c : 0 .. Cardinality(Msg), p : Proc] \* c for counter

GT(u, v) == \* Is u > v?
    \/ u.c > v.c
    \/ /\ u.c = v.c
       /\ Priority[u.p] > Priority[v.p]

MaxV(vs) == CHOOSE u \in vs: \A v \in vs: u # v => GT(u, v)
----------------------------------------------------------------------------
Message == [type : {"MULTICAST"}, m : Msg]
    \cup [type : {"PROPOSE"}, m : Msg, p : Proc, lts : TS]

Send(msg) == \* Send msg \in Message to its destination processes
    incoming' = [p \in Proc |->
        IF p \in Dest[msg.m] THEN incoming[p] \cup {msg}
                             ELSE incoming[p]]

(*
Send smsg \in Message to its destination processes and remove rmsg \in Message from incoming[sender]

Precondition: sender \in Dest[msg.m]
*)
SendAndRemove(smsg, sender, rmsg) == 
    incoming' = [p \in Proc |->
        IF p = sender THEN (incoming[sender] \cup {smsg}) \ {rmsg}
                      ELSE IF p \in Dest[smsg.m] THEN incoming[p] \cup {smsg}
                                                 ELSE incoming[p]]
----------------------------------------------------------------------------
TypeOK ==
    /\ clock     \in [Proc -> 0 .. Cardinality(Msg)]
    /\ phase     \in [Proc -> [Msg -> {"START", "PROPOSED", "COMMITTED"}]]
    /\ localTS   \in [Proc -> [Msg -> TS]]
    /\ globalTS  \in [Proc -> [Msg -> TS]]
    /\ delivered \in [Proc -> [Msg -> BOOLEAN]]
    /\ incoming  \in [Proc -> SUBSET Message]
    /\ sent      \subseteq Msg
----------------------------------------------------------------------------
Init ==
    /\ clock     = [p \in Proc |-> 0]
    /\ phase     = [p \in Proc |-> [m \in Msg |-> "START"]]
    /\ localTS   = [p \in Proc |-> [m \in Msg |-> [c |-> 0, p |-> p]]]
    /\ globalTS  = [p \in Proc |-> [m \in Msg |-> [c |-> 0, p |-> p]]]
    /\ delivered = [p \in Proc |-> [m \in Msg |-> FALSE]]
    /\ incoming  = [p \in Proc |-> {}]
    /\ sent      = {}
----------------------------------------------------------------------------
Multicast(m) == \* Multicast m \in Msg
    /\ m \in Msg \ sent
    /\ sent' = sent \cup {m}
    /\ Send([type |-> "MULTICAST", m |-> m])
    /\ UNCHANGED pvars

Propose(p) == \* When p \in Proc receives a MULTICAST for some m \in Msg
    \E msg \in incoming[p]:
        /\ msg.type = "MULTICAST"
        /\ LET m == msg.m
           IN  /\ Assert(p \in Dest[m], "p should be one of the destination process of m") 
               /\ clock' = [clock EXCEPT ![p] = @ + 1]
               /\ localTS' = [localTS EXCEPT ![p][m] = [c |-> clock'[p], p |-> p]]
               /\ phase' = [phase EXCEPT ![p][m] = "PROPOSED"]
               /\ SendAndRemove([type |-> "PROPOSE", m |-> m, p |-> p,
                                  lts |-> localTS'[p][m]], p, msg)
               /\ UNCHANGED <<globalTS, delivered, sent>>

Deliver(p) == \* When p \in Proc receives all PROPOSE for some m \in Msg
    \E m \in Msg:
        LET msgofm  == {msg \in incoming[p] : msg.type = "PROPOSE" /\ msg.m = m}
            destofm == {msg.p : msg \in msgofm}
            ltsofm  == {msg.lts : msg \in msgofm}
        IN  /\ destofm = Dest[m]
            /\ globalTS' = [globalTS EXCEPT ![p][m] = MaxV(ltsofm)]
            /\ clock' = [clock EXCEPT ![p] = Max(clock[p], globalTS'[p][m].c)]
            /\ phase' = [phase EXCEPT ![p][m] = "COMMITTED"]
            /\ LET readym == {rm \in Msg :
                                /\ phase'[p][rm] = "COMMITTED"
                                /\ delivered[p][rm] = FALSE
                                /\ \A pm \in Msg :
                                    phase'[p][pm] = "PROPOSED"
                                        => GT(localTS[p][pm], globalTS'[p][rm])}
               IN  delivered' = [delivered EXCEPT ![p] = [pm \in Msg |->
                                    IF pm \in readym THEN TRUE ELSE @[pm]]]
            /\ UNCHANGED <<localTS, sent, incoming>>
----------------------------------------------------------------------------
Next ==
    \/ \E m \in Msg: Multicast(m)
    \/ \E p \in Proc:
        \/ Propose(p)
        \/ Deliver(p)

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------
(*
Invariant: Global timestamps are unique for each m \in Msg; see Section III.
*)
UniqueGTS ==
    \A p \in Proc, m1, m2 \in Msg:
        (m1 # m2 /\ phase[p][m1] = "COMMITTED" /\ phase[p][m2] = "COMMITTED")
            => globalTS[p][m1] # globalTS[p][m2]
        
(*
Invariant: Each m \in Msg is assigned a single global timestamp.
*)
SameGTS ==
    \A p1, p2 \in Proc, m \in Msg:
        (phase[p1][m] = "COMMITTED" /\ phase[p2][m] = "COMMITTED")
            => globalTS[p1][m] = globalTS[p2][m]
----------------------------------------------------------------------------
THEOREM TypeTheorem == Spec => []TypeOK

THEOREM UniqueGTSTheorem == Spec => []UniqueGTS

THEOREM SameGTSTheorem == Spec => []SameGTS
=============================================================================
\* Modification History
\* Last modified Fri Jul 23 20:42:57 CST 2021 by hengxin
\* Last modified Thu Jul 08 20:18:10 CST 2021 by eric
\* Created Sat Jun 26 16:04:39 CST 2021 by eric
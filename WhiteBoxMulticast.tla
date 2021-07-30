------------------------- MODULE WhiteBoxMulticast -------------------------
(*
The specification of the White-Box Multicast protocol for atomic multicast;
see Section IV of the DSN2019 paper "White-Box Atomic Multicast"
by Alexey Gotsman, Anatole Lefort, and Gregory Chockler.

Note that this version omits the recovery mechanism of leaders.
Therefore, this spec. does not involve any "ballots".
We leave it to the future work.
*)
EXTENDS Naturals, Sequences, FiniteSets, TLC
----------------------------------------------------------------------------
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])

Max(a, b) == IF a > b THEN a ELSE b
----------------------------------------------------------------------------
CONSTANTS
    Msg,    \* the set of messages, ranged over by m
    Proc,   \* the set of processes, ranged over by p
    Group,  \* the set of groups, ranged over by g
    Leader, \* Leader[g] \in Proc: the leader of the group g \in Group
    Member, \* Member[g] \subseteq Proc: the members of the group g \in Group
    Dest    \* Dest[m] \subseteq Group: the set of destination groups of m \in Msg
    
ASSUME
    /\ Leader \in [Group -> Proc]
    /\ Member \in [Group -> SUBSET Proc]
    /\ \A g \in Group: Leader[g] \in Member[g]
    /\ \A g1, g2 \in Group: Member[g1] \cap Member[g2] = {}
    /\ Dest \in [Msg -> SUBSET Group]

Priority == CHOOSE f \in [Group -> 1 .. Cardinality(Group)] : Injective(f)
----------------------------------------------------------------------------
VARIABLES
    clock,      \* clock[p]: the clock at process p \in Proc
    phase,      \* phase[p][m]: the phase of the message m \in Msg at process p \in Proc
    localTS,    \* localTS[p][m]: the local ts of the message m \in Msg at process p \in Proc
    globalTS,   \* globalTS[p][m]: the global ts of the message m \in Msg at process p \in Proc
    delivered,  \* delivered[p][m]: has m \in Msg been delivered at process p \in Proc?
    incoming,   \* incoming[p] \subseteq Message (defined below): the incoming channel of process p \in Proc
    sent        \* sent \subseteq Msg: the set of messages that have been multicast; only for TLC
    
pvars == <<clock, phase, localTS, globalTS, delivered>>
vars == <<clock, phase, localTS, globalTS, delivered, incoming, sent>>
----------------------------------------------------------------------------
MaxCounter == Cardinality(Msg) * Cardinality(Group)

TS == [c : 0 .. MaxCounter, p : Group] \* c for counter

GT(u, v) == \* Is u > v?
    \/ u.c > v.c
    \/ /\ u.c = v.c
       /\ Priority[u.p] > Priority[v.p]

MaxV(vs) == CHOOSE u \in vs: \A v \in vs: u # v => GT(u, v)
----------------------------------------------------------------------------
(*
TODO: type literals as CONSTANTS
*)
Message == [type : {"MULTICAST"}, m : Msg]
    \cup [type : {"ACCEPT"}, m : Msg, g : Group, lts : TS]
    \cup [type : {"ACCEPTACK"}, m : Msg, g : Proc]
    \cup [type : {"DELIVER"}, m : Msg, lts : TS, gts : TS]

Send(msg) == \* Send msg \in Message to the leaders of its destination groups
    incoming' = [p \in Proc |->
        IF p \in {Leader[g] : g \in Dest[msg.m]} THEN incoming[p] \cup {msg}
                                                 ELSE incoming[p]]

(*
TODO: to revise it.

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
    /\ clock     \in [Proc -> 0 .. MaxCounter]
    /\ phase     \in [Proc -> [Msg -> {"START", "PROPOSED", "ACCEPTED", "COMMITTED"}]]
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
multicast(m) == \* multicast m \in Msg
    /\ m \in Msg \ sent
    /\ sent' = sent \cup {m}
    /\ Send([type |-> "MULTICAST", m |-> m])
    /\ UNCHANGED pvars

Multicast == FALSE

\*Propose(p) == \* When p \in Proc receives a MULTICAST for some m \in Msg
\*    \E msg \in incoming[p]:
\*        /\ msg.type = "MULTICAST"
\*        /\ LET m == msg.m
\*           IN  /\ Assert(p \in Dest[m], "p should be one of the destination process of m") 
\*               /\ clock' = [clock EXCEPT ![p] = @ + 1]
\*               /\ localTS' = [localTS EXCEPT ![p][m] = [c |-> clock'[p], p |-> p]]
\*               /\ phase' = [phase EXCEPT ![p][m] = "PROPOSED"]
\*               /\ SendAndRemove([type |-> "PROPOSE", m |-> m, p |-> p,
\*                                  lts |-> localTS'[p][m]], p, msg)
\*               /\ UNCHANGED <<globalTS, delivered, sent>>
=============================================================================
\* Modification History
\* Last modified Fri Jul 30 23:05:23 CST 2021 by hengxin
\* Created Fri Jul 30 19:56:43 CST 2021 by hengxin
---- MODULE MC ----
EXTENDS Skeen, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2
----

\* MV CONSTANT definitions Proc
const_16274552074782000 == 
{p1, p2}
----

\* MV CONSTANT definitions Msg
const_16274552074783000 == 
{m1, m2}
----

\* SYMMETRY definition
symm_16274552074784000 == 
Permutations(const_16274552074782000) \union Permutations(const_16274552074783000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_16274552074785000 == 
m1 :> {p1, p2} @@ m2 :> {p2, p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:53:27 CST 2021 by hengxin

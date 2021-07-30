---- MODULE MC ----
EXTENDS Skeen, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3, m4
----

\* MV CONSTANT definitions Proc
const_162762331174837000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions Msg
const_162762331174838000 == 
{m1, m2, m3, m4}
----

\* SYMMETRY definition
symm_162762331174839000 == 
Permutations(const_162762331174837000) \union Permutations(const_162762331174838000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162762331174840000 == 
m1 :> {p1, p2, p3} @@ m2 :> {p2, p3, p4} @@ m3 :> {p3, p4, p1} @@ m4 :> {p4, p1, p2}
----

=============================================================================
\* Modification History
\* Created Fri Jul 30 13:35:11 CST 2021 by hengxin

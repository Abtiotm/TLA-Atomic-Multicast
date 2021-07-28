---- MODULE MC ----
EXTENDS Skeen, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3
----

\* MV CONSTANT definitions Proc
const_162745591209030000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Msg
const_162745591209031000 == 
{m1, m2, m3}
----

\* SYMMETRY definition
symm_162745591209032000 == 
Permutations(const_162745591209030000) \union Permutations(const_162745591209031000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162745591209033000 == 
m1 :> {p1, p2} @@ m2 :> {p2, p3} @@ m3 :> {p3, p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 15:05:12 CST 2021 by hengxin

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
const_1627454954853121000 == 
{p1, p2}
----

\* MV CONSTANT definitions Msg
const_1627454954853122000 == 
{m1, m2}
----

\* SYMMETRY definition
symm_1627454954854123000 == 
Permutations(const_1627454954853121000) \union Permutations(const_1627454954853122000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_1627454954854124000 == 
m1 :> {p1, p2} @@ m2 :> {p2, p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:49:14 CST 2021 by hengxin

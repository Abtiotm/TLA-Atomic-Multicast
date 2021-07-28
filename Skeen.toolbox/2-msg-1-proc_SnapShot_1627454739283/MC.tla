---- MODULE MC ----
EXTENDS Skeen, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2
----

\* MV CONSTANT definitions Proc
const_1627454737265107000 == 
{p1}
----

\* MV CONSTANT definitions Msg
const_1627454737265108000 == 
{m1, m2}
----

\* SYMMETRY definition
symm_1627454737265109000 == 
Permutations(const_1627454737265108000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_1627454737265110000 == 
m1 :> {p1} @@ m2 :> {p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:45:37 CST 2021 by hengxin

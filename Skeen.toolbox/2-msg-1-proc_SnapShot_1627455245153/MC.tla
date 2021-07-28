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
const_16274552431319000 == 
{p1}
----

\* MV CONSTANT definitions Msg
const_162745524313110000 == 
{m1, m2}
----

\* SYMMETRY definition
symm_162745524313111000 == 
Permutations(const_162745524313110000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162745524313112000 == 
m1 :> {p1} @@ m2 :> {p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:54:03 CST 2021 by hengxin

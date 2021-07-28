---- MODULE MC ----
EXTENDS Skeen, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1
----

\* MV CONSTANT definitions Proc
const_162745405717130000 == 
{p1}
----

\* MV CONSTANT definitions Msg
const_162745405717131000 == 
{m1}
----

\* SYMMETRY definition
symm_162745405717132000 == 
Permutations(const_162745405717130000) \union Permutations(const_162745405717131000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162745405717133000 == 
m1 :> {p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:34:17 CST 2021 by hengxin

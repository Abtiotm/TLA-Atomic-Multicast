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
const_162745525418116000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Msg
const_162745525418117000 == 
{m1, m2, m3}
----

\* SYMMETRY definition
symm_162745525418118000 == 
Permutations(const_162745525418116000) \union Permutations(const_162745525418117000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162745525418119000 == 
m1 :> {p1, p2} @@ m2 :> {p2, p3} @@ m3 :> {p3, p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:54:14 CST 2021 by hengxin

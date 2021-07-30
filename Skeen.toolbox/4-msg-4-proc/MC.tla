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
const_16274888492039000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions Msg
const_162748884920310000 == 
{m1, m2, m3, m4}
----

\* SYMMETRY definition
symm_162748884920311000 == 
Permutations(const_16274888492039000) \union Permutations(const_162748884920310000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162748884920312000 == 
m1 :> {p1, p2, p3} @@ m2 :> {p2, p3, p4} @@ m3 :> {p3, p4, p1} @@ m4 :> {p4, p1, p2}
----

=============================================================================
\* Modification History
\* Created Thu Jul 29 00:14:09 CST 2021 by hengxin

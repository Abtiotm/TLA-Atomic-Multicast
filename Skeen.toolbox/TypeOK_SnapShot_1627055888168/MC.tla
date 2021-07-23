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
const_16270459303239000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions Msg
const_162704593032310000 == 
{m1, m2, m3, m4}
----

\* SYMMETRY definition
symm_162704593032311000 == 
Permutations(const_16270459303239000) \union Permutations(const_162704593032310000)
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162704593032312000 == 
m1 :> {p1, p2, p3} @@ m2 :> {p2, p3, p4} @@ m3 :> {p3, p4, p1} @@ m4 :> {p4, p1, p2}
----

=============================================================================
\* Modification History
\* Created Fri Jul 23 21:12:10 CST 2021 by hengxin

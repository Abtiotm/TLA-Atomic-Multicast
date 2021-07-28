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
const_162745454038487000 == 
{p1}
----

\* MV CONSTANT definitions Msg
const_162745454038488000 == 
{m1}
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162745454038489000 == 
m1 :> {p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:42:20 CST 2021 by hengxin

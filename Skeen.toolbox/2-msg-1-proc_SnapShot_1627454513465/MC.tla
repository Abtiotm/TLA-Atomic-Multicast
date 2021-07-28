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
const_162745451144375000 == 
{p1}
----

\* MV CONSTANT definitions Msg
const_162745451144376000 == 
{m1}
----

\* CONSTANT definitions @modelParameterConstants:2Dest
const_162745451144377000 == 
m1 :> {p1}
----

=============================================================================
\* Modification History
\* Created Wed Jul 28 14:41:51 CST 2021 by hengxin

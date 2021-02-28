---- MODULE MC ----
EXTENDS ScenarioIII, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t0
----

\* MV CONSTANT definitions SW
const_161449196361956000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_161449196361957000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_161449196361958000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_161449196361959000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_161449196361960000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:52WHICH_SWITCH_MODEL
const_161449196361961000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

=============================================================================
\* Modification History
\* Created Sat Feb 27 21:59:23 PST 2021 by zmy

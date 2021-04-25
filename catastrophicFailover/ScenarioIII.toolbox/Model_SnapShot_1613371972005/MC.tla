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
const_1619256450321299000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_1619256450321300000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_1619256450321301000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_1619256450321302000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_1619256450322303000 == 
[ofc0 |-> 0, rc0 |-> 0, nib0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:52WHICH_SWITCH_MODEL
const_1619256450322304000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

=============================================================================
\* Modification History
\* Created Sat Apr 24 02:27:30 PDT 2021 by zmy

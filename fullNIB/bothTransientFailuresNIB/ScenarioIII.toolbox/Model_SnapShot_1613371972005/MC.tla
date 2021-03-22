---- MODULE MC ----
EXTENDS ScenarioIII, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1, s2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t0
----

\* MV CONSTANT definitions SW
const_16163955013461267000 == 
{s0, s1, s2}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_16163955013461268000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_16163955013461269000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_16163955013461270000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_16163955013461271000 == 
[ofc0 |-> 0, rc0 |-> 0, nib0 |-> 1]
----

\* CONSTANT definitions @modelParameterConstants:52WHICH_SWITCH_MODEL
const_16163955013461272000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL) @@ (s2 :> SW_SIMPLE_MODEL)
----

=============================================================================
\* Modification History
\* Created Sun Mar 21 23:45:01 PDT 2021 by zmy

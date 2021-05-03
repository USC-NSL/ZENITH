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
const_16199961043752000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_16199961043763000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_16199961043764000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_16199961043765000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_16199961043766000 == 
[ofc0 |-> 0, rc0 |-> 0, nib0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:52WHICH_SWITCH_MODEL
const_16199961043767000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

=============================================================================
\* Modification History
\* Created Sun May 02 15:55:04 PDT 2021 by zmy

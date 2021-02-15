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
const_161336821248212000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_161336821248213000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_161336821248214000 == 
<<{s0}, {s1}>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_161336821248215000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_161336821248216000 == 
[ofc0 |-> 1, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:52WHICH_SWITCH_MODEL
const_161336821248217000 == 
(s0 :> SW_COMPLEX_MODEL) @@ (s1 :> SW_COMPLEX_MODEL)
----

=============================================================================
\* Modification History
\* Created Sun Feb 14 21:50:12 PST 2021 by root

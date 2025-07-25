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
const_161301863311343000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_161301863311344000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_161301863311345000 == 
<<{s0}, {s1}>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_161301863311346000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_161301863311347000 == 
[ofc0 |-> 1, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:49MAX_NUM_SW_FAILURE
const_161301863311348000 == 
1
----

=============================================================================
\* Modification History
\* Created Wed Feb 10 20:43:53 PST 2021 by root

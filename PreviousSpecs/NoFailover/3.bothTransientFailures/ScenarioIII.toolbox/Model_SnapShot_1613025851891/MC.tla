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
const_161302262459573000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_161302262459574000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_161302262459575000 == 
<<{s0}, {s1}>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_161302262459576000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_161302262459577000 == 
[ofc0 |-> 1, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:49MAX_NUM_SW_FAILURE
const_161302262459578000 == 
1
----

=============================================================================
\* Modification History
\* Created Wed Feb 10 21:50:24 PST 2021 by root

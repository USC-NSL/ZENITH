---- MODULE MC ----
EXTENDS drain, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1
----

\* MV CONSTANT definitions SW
const_1626127312876114000 == 
{s0, s1}
----

\* CONSTANT definitions @modelParameterConstants:19UPGRADER_REQUEST_QUEUE
const_1626127312876115000 == 
<<[type |-> REMOVE_SW, sw |-> s0], [type |-> RUN_SW, sw |-> s0]>>
----

\* CONSTANT definitions @modelParameterConstants:20EXPANDER_REQUEST_QUEUE
const_1626127312876116000 == 
<<[type |-> REMOVE_SW, sw |-> s0]>>
----

=============================================================================
\* Modification History
\* Created Mon Jul 12 15:01:52 PDT 2021 by zmy

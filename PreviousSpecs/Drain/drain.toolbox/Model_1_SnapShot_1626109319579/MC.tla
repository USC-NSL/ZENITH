---- MODULE MC ----
EXTENDS drain, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1
----

\* MV CONSTANT definitions SW
const_1626924722391222000 == 
{s0, s1}
----

\* CONSTANT definitions @modelParameterConstants:19UPGRADER_REQUEST_QUEUE
const_1626924722391223000 == 
<<[type |-> DRAIN_SW, sw |-> s0], [type |-> UNDRAIN_SW, sw |-> s0]>>
----

\* CONSTANT definitions @modelParameterConstants:20EXPANDER_REQUEST_QUEUE
const_1626924722391224000 == 
<<[type |-> DOWN_SW, sw |-> s0]>>
----

=============================================================================
\* Modification History
\* Created Wed Jul 21 20:32:02 PDT 2021 by zmy

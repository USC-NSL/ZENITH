---- MODULE MC ----
EXTENDS SwitchCompleteTransientFailure, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t0
----

\* MV CONSTANT definitions SW
const_161752075641646000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_161752075641647000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:6IR2SW
const_161752075641648000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s1)
----

\* CONSTANT definitions @modelParameterConstants:8SW_MODULE_CAN_FAIL_OR_NOT
const_161752075641649000 == 
[cpu |-> 0, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:25SW_FAIL_ORDERING
const_161752075641650000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 1]}>>
----

\* CONSTANT definitions @modelParameterConstants:34MaxNumIRs
const_161752075641651000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:41MaxNumFlows
const_161752075641652000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:44IR2FLOW
const_161752075641653000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:45WHICH_SWITCH_MODEL
const_161752075641654000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:47MAX_NUM_CONTROLLER_SUB_FAILURE
const_161752075641655000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:48TOPO_DAG_MAPPING
const_161752075641656000 == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {3}, e |-> {}])
----

\* CONSTANT definitions @modelParameterConstants:56FINAL_DAG
const_161752075641657000 == 
[v |-> {1, 2}, e |-> {<<1, 2>>}]
----

=============================================================================
\* Modification History
\* Created Sun Apr 04 00:19:16 PDT 2021 by root

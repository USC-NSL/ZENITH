---- MODULE MC ----
EXTENDS SwitchCompleteTransientFailure, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1, s2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t0, t1
----

\* MV CONSTANT definitions SW
const_1617581791302137000 == 
{s0, s1, s2}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_1617581791302138000 == 
{t0, t1}
----

\* CONSTANT definitions @modelParameterConstants:6IR2SW
const_1617581791302139000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s2) @@ (4 :> s1) @@ (5 :> s2)
----

\* CONSTANT definitions @modelParameterConstants:8SW_MODULE_CAN_FAIL_OR_NOT
const_1617581791302140000 == 
[cpu |-> 0, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:25SW_FAIL_ORDERING
const_1617581791302141000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 1]}>>
----

\* CONSTANT definitions @modelParameterConstants:34MaxNumIRs
const_1617581791302142000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:41MaxNumFlows
const_1617581791302143000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:44IR2FLOW
const_1617581791302144000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:45WHICH_SWITCH_MODEL
const_1617581791302145000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL) @@ (s2 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:47MAX_NUM_CONTROLLER_SUB_FAILURE
const_1617581791302146000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:48TOPO_DAG_MAPPING
const_1617581791302147000 == 
({} :> [v |-> {1, 2, 3}, e |-> {<<1, 2>>, <<1, 3>>}]) @@ ({s0} :> [v |-> {4, 5}, e |-> {<<5, 4>>}])
----

\* CONSTANT definitions @modelParameterConstants:56FINAL_DAG
const_1617581791302148000 == 
[v |-> {1, 2, 3}, e |-> {<<1, 2>>, <<1, 3>>}]
----

=============================================================================
\* Modification History
\* Created Mon Apr 05 00:16:31 UTC 2021 by root

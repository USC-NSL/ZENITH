---- MODULE MC ----
EXTENDS SwitchPermanentFailure, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1, s2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t0
----

\* MV CONSTANT definitions SW
const_1617010698548750000 == 
{s0, s1, s2}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_1617010698548751000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:4SW_MODULE_CAN_FAIL_OR_NOT
const_1617010698548752000 == 
[cpu |-> 1, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_1617010698548753000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 0]}>>
----

\* CONSTANT definitions @modelParameterConstants:27MaxNumIRs
const_1617010698548754000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:37WHICH_SWITCH_MODEL
const_1617010698548755000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
@@ (s2 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:39MAX_NUM_CONTROLLER_SUB_FAILURE
const_1617010698548756000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:47FINAL_DAG
const_1617010698548757000 == 
[v |-> {4, 5}, e |-> {<<5, 4>>}]
----

\* CONSTANT definitions @modelParameterConstants:52IR2SW
const_1617010698548758000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s2) @@ (4 :> s1) @@ (5 :> s2)
----

\* CONSTANT definitions @modelParameterConstants:53TOPO_DAG_MAPPING
const_1617010698548759000 == 
({} :> [v |-> {1, 2, 3}, e |-> {<<1, 2>>, <<1, 3>>}]) @@ ({s0} :> [v |-> {4, 5}, e |-> {<<5, 4>>}])
----

\* CONSTANT definitions @modelParameterConstants:56IR2FLOW
const_1617010698548760000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:57MaxNumFlows
const_1617010698548761000 == 
5
----

=============================================================================
\* Modification History
\* Created Mon Mar 29 02:38:18 PDT 2021 by root

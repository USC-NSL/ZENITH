---- MODULE MC ----
EXTENDS SwitchPermanentFailure, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t0
----

\* MV CONSTANT definitions SW
const_1616756068798268000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_1616756068798269000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:5SW_MODULE_CAN_FAIL_OR_NOT
const_1616756068798270000 == 
[cpu |-> 1, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:19SW_FAIL_ORDERING
const_1616756068798271000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 0]}>>
----

\* CONSTANT definitions @modelParameterConstants:30MaxNumIRs
const_1616756068798272000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:42WHICH_SWITCH_MODEL
const_1616756068798273000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:44MAX_NUM_CONTROLLER_SUB_FAILURE
const_1616756068798274000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:52FINAL_DAG
const_1616756068798275000 == 
[v |-> {4}, e |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:57IR2SW
const_1616756068798276000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s0) @@ (4 :> s1)
----

\* CONSTANT definitions @modelParameterConstants:58TOPO_DAG_MAPPING
const_1616756068798277000 == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {4}, e |-> {}])
----

=============================================================================
\* Modification History
\* Created Fri Mar 26 03:54:28 PDT 2021 by root

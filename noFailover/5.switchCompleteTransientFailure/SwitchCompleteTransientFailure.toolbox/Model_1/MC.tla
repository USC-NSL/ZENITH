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
const_16172847034941174000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_16172847034941175000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:6IR2SW
const_16172847034941176000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s1)
----

\* CONSTANT definitions @modelParameterConstants:8SW_MODULE_CAN_FAIL_OR_NOT
const_16172847034941177000 == 
[cpu |-> 0, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:25SW_FAIL_ORDERING
const_16172847034941178000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 1]}>>
----

\* CONSTANT definitions @modelParameterConstants:35MaxNumIRs
const_16172847034941179000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:47MaxNumFlows
const_16172847034941180000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:50IR2FLOW
const_16172847034941181000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:51WHICH_SWITCH_MODEL
const_16172847034941182000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:53MAX_NUM_CONTROLLER_SUB_FAILURE
const_16172847034941183000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:54TOPO_DAG_MAPPING
const_16172847034941184000 == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {3}, e |-> {}])
----

\* CONSTANT definitions @modelParameterConstants:62FINAL_DAG
const_16172847034941185000 == 
[v |-> {1, 2}, e |-> {<<1, 2>>}]
----

=============================================================================
\* Modification History
\* Created Thu Apr 01 06:45:03 PDT 2021 by root

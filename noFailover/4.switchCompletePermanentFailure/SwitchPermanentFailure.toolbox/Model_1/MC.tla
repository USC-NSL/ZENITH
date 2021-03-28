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
const_1616911689454560000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_1616911689454561000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:4SW_MODULE_CAN_FAIL_OR_NOT
const_1616911689454562000 == 
[cpu |-> 1, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_1616911689454563000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 0]}>>
----

\* CONSTANT definitions @modelParameterConstants:27MaxNumIRs
const_1616911689454564000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:37WHICH_SWITCH_MODEL
const_1616911689454565000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:39MAX_NUM_CONTROLLER_SUB_FAILURE
const_1616911689454566000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:47FINAL_DAG
const_1616911689454567000 == 
[v |-> {4}, e |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:52IR2SW
const_1616911689454568000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s0) @@ (4 :> s1)
----

\* CONSTANT definitions @modelParameterConstants:53TOPO_DAG_MAPPING
const_1616911689454569000 == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {4}, e |-> {}])
----

\* CONSTANT definitions @modelParameterConstants:56IR2FLOW
const_1616911689454570000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:57MaxNumFlows
const_1616911689454571000 == 
4
----

=============================================================================
\* Modification History
\* Created Sat Mar 27 23:08:09 PDT 2021 by root

---- MODULE MC ----
EXTENDS ScenarioIII, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s0, s1, s2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t0
----

\* MV CONSTANT definitions SW
const_1624295748279324000 == 
{s0, s1, s2}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_1624295748279325000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_1624295748279326000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 0]}>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_1624295748279327000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_1624295748279328000 == 
[ofc0 |-> 0, rc0 |-> 0, nib0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:52WHICH_SWITCH_MODEL
const_1624295748279329000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)@@ (s2 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:75IR2FLOW
const_1624295748279330000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:81IR2SW
const_1624295748279331000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s2) @@ (4 :> s1) @@ (5 :> s2)
----

\* CONSTANT definitions @modelParameterConstants:90MaxNumFlows
const_1624295748279332000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:91TOPO_DAG_MAPPING
const_1624295748279333000 == 
({} :> [v |-> {1, 2, 3}, e |-> {<<1, 2>>, <<1, 3>>}]) @@ ({s0} :> [v |-> {4, 5}, e |-> {<<5, 4>>}])
----

\* CONSTANT definitions @modelParameterConstants:92FINAL_DAG
const_1624295748279334000 == 
[v |-> {4, 5}, e |-> {<<5, 4>>}]
----

=============================================================================
\* Modification History
\* Created Mon Jun 21 10:15:48 PDT 2021 by zmy

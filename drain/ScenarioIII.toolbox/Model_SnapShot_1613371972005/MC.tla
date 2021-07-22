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
const_1625786338431198000 == 
{s0, s1, s2}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_1625786338431199000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:18SW_FAIL_ORDERING
const_1625786338431200000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 0]}>>
----

\* CONSTANT definitions @modelParameterConstants:28MaxNumIRs
const_1625786338431201000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:40MAX_NUM_CONTROLLER_SUB_FAILURE
const_1625786338431202000 == 
[ofc0 |-> 0, rc0 |-> 0, nib0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:52WHICH_SWITCH_MODEL
const_1625786338431203000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)@@ (s2 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:75IR2FLOW
const_1625786338431204000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:81IR2SW
const_1625786338431205000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s1)
----

\* CONSTANT definitions @modelParameterConstants:90MaxNumFlows
const_1625786338431206000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:91TOPO_DAG_MAPPING
const_1625786338431207000 == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {3}, e |-> {}])
----

\* CONSTANT definitions @modelParameterConstants:92FINAL_DAG
const_1625786338431208000 == 
[v |-> {3}, e |-> {}]
----

=============================================================================
\* Modification History
\* Created Thu Jul 08 16:18:58 PDT 2021 by zmy

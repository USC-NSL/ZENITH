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
const_161819923046082000 == 
{s0, s1}
----

\* MV CONSTANT definitions CONTROLLER_THREAD_POOL
const_161819923046083000 == 
{t0}
----

\* CONSTANT definitions @modelParameterConstants:5IR2SW
const_161819923046084000 == 
(1 :> s0) @@ (2 :> s1) @@ (3 :> s1)
----

\* CONSTANT definitions @modelParameterConstants:7SW_MODULE_CAN_FAIL_OR_NOT
const_161819923046085000 == 
[cpu |-> 0, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:24SW_FAIL_ORDERING
const_161819923046086000 == 
<<{[sw |-> s0, partial |-> 0, transient |-> 1]}>>
----

\* CONSTANT definitions @modelParameterConstants:33MaxNumIRs
const_161819923046087000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:40MaxNumFlows
const_161819923046088000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:43IR2FLOW
const_161819923046089000 == 
[x \in 1..MaxNumIRs |-> x]
----

\* CONSTANT definitions @modelParameterConstants:44WHICH_SWITCH_MODEL
const_161819923046090000 == 
(s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

\* CONSTANT definitions @modelParameterConstants:46MAX_NUM_CONTROLLER_SUB_FAILURE
const_161819923046091000 == 
[ofc0 |-> 0, rc0 |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:47TOPO_DAG_MAPPING
const_161819923046092000 == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {3}, e |-> {}])
----

\* CONSTANT definitions @modelParameterConstants:55FINAL_DAG
const_161819923046093000 == 
[v |-> {1, 2}, e |-> {<<1, 2>>}]
----

\* Constant expression definition @modelExpressionEval
const_expr_161819923046094000 == 
Paths(10, {<<1, 2>>, <<1, 3>>, <<2, 3>>})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161819923046094000>>)
----

=============================================================================
\* Modification History
\* Created Sun Apr 11 20:47:10 PDT 2021 by root

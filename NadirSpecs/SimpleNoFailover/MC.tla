---- MODULE MC ----
EXTENDS NoFailover, TLC

CONSTANTS
s0, s1
----

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

\* CONSTANT definitions @modelParameterConstants:6MaxDAGID
const_161819923046085000 == 
15
----

\* CONSTANT definitions @modelParameterConstants:10TOTAL_IR_DEL_SET
const_161819923046086000 ==
(MaxDAGID + 1)..(2 * MaxDAGID)
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

\* CONSTANT definitions @modelParameterConstants:44TOTAL_IR_SET
const_161819923046090000 ==
1..MaxNumIRs
----

\* CONSTANT definitions @modelParameterConstants:45TOTAL_DAG_SET
const_161819923046091000 ==
1..MaxDAGID

\* CONSTANT definitions @modelParameterConstants:46TOTAL_FLOW_SET
const_161819923046093000 ==
1..MaxNumFlows

\* CONSTANT definitions @modelParameterConstants:47TOPO_DAG_MAPPING
const_161819923046092000 == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {3}, e |-> {}])
----

=============================================================================

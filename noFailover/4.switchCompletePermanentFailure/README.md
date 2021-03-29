To be able to run any of the specifications in this folder, please change the .tla file to SwitchPermanentFailure.tla and put them inside the same directory as SwitchPermanentFailure.toolbox. You should then be able to add the specification to the TLA toolbox and run it using the given model.

The parameters of the model are;

1) SW; This defines the set of switches e.g. [model value] {s0, s1}

2) SW_FAIL_ORDERING; defines the ordering based on which the switches should fail and whether it is a transient failure or permanent failure, e.g. <<{[sw |-> s0, partial |-> 0, transient |-> 0, ], [sw |-> s1, partial |-> 0, transient |-> 1]}, {[sw |-> s2, partial |-> 1, transient |-> 1]}>> means s0 and s1 must fail before s2 fails, however, s0 and s1 might fail in any order. s0 faces a complete permanent failure, s1 faces a complete transient failure and s2 faces a partial transient failure.

3) CONTROLLER_THREAD_POOL; defines the set of available threads e.g. [model value] {t0}

4) MAX_NUM_CONTROLLER_SUB_FAILURE; defines the maxmimum number of internal partial failures, each component of control plane might face. e.g. [ofc0 |-> 1, rc0 |-> 0]

5) MaxNumIRs; Should be equal to the total number of IRs in DAG_FAILED_SW_MAPPING. [integer]

6) WHICH_SW_MODEL; determines which of the two available models each switch use (either SW_SIMPLE_MODEL or SW_COMPLEX_MODEL. e.g. (s0 :> SW_COMPLEX_MODEL) @@ (s1 :> SW_SIMPLE_MODEL). Note that SW_SIMPLE_MODEL does everything in one atomic operation and does not fail at all.

7) DAG_FAILED_SW_MAPPING: This is a mapping from the set of failed switch to a DAG. For example, ({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({s0} :> [v |-> {4}, e |-> {}]) means if no switch has failed, the DAG that should be installed in the topology has two IRs and IR1 should be installed before IR2. If s0 fails, the DAG has only one IR with no dependencies. 

8) SW_MODULE_CAN_FAIL_OR_NOT: [Only for partial failures]. it defines whether each of the components of the switch can fail in the execution or not e.g. [cpu |-> 1, nicAsic |-> 0, ofa |-> 0, installer |-> 0].

9) FINAL_DAG: This is the expected final DAG installed in the network e.g. [v |-> {1, 2, 3}, e |-> {<<1, 2>>, <<1, 3>>}

10) IR2SW: A mapping from IR to the switch that defines which switch each IR belongs to e.g. (1 :> s0) @@ (2 :> s1)

11) IR2FLOW: A mapping from IR to a flow number that the IR is going to install or delete e.g. (1 :> 2) @@ (2 :> 3)

12) MaxNumFlows: Should be equal to the total number of FLOWs in IR2FLOW. [integer]

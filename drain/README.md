To be able to run any of the specifications in this folder, please change the .tla file to ScenarioIII.tla and 
put them inside the same directory as ScenarioIII.toolbox. You should then be able to add the specification to
the TLA toolbox and run it using the given model.

The parameters of the model are;
* SW; This defines the set of switches e.g. [model value] {s0, s1}
* SW_FAIL_ORDERING; defines the ordering based on which the switches should fail e.g. <<{s0}, {s1}>>
means s0 must fail before s1, or <<{s0, s1}, {s2}>> means s0 and s1 must fail before s2 fails, however, s0 and s1
might fail in any order.
* CONTROLLER_THREAD_POOL; defines the set of available threads e.g. [model value] {t0}
* MAX_NUM_CONTROLLER_SUB_FAILURE; defines the maxmimum number of internal partial failures, each component of 
control plane might face. e.g. [ofc0 |-> 1, rc0 |-> 0]
* MaxNumIRs; the maximum number of IRs (all the possible non-isomorphic DAGs are generated based on this). 
* WHICH_SW_MODEL; determines which of the two available models each switch use (either SW_SIMPLE_MODEL or 
SW_COMPLEX_MODEL. e.g. (s0 :> SW_COMPLEX_MODEL) @@ (s1 :> SW_SIMPLE_MODEL). Note that SW_SIMPLE_MODEL does
everything in one atomic operation and does not fail at all. 

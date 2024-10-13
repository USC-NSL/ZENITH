--------------------- MODULE eval_constants ---------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS SW
CONSTANTS WHICH_SWITCH_MODEL
CONSTANTS SW_SIMPLE_ID
CONSTANTS SW_SIMPLE_MODEL, SW_COMPLEX_MODEL
CONSTANTS SW_FAIL_ORDERING
CONSTANTS SW_MODULE_CAN_FAIL_OR_NOT
CONSTANTS MAX_NUM_CONTROLLER_SUB_FAILURE
CONSTANTS NotFailed, Failed

ASSUME WHICH_SWITCH_MODEL \in [SW -> {SW_SIMPLE_MODEL, SW_COMPLEX_MODEL}]

ASSUME \A x \in {
        SW_FAIL_ORDERING[z]: z \in DOMAIN SW_FAIL_ORDERING
    }: \/ x = {}
       \/ \A y \in x: /\ "transient" \in DOMAIN y
                      /\ "sw" \in DOMAIN y
                      /\ "partial" \in DOMAIN y
                      /\ y.transient \in {0, 1}
                      /\ y.sw \in SW          
                      /\ y.partial \in {0, 1}

ASSUME /\ "cpu" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "nicAsic" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "ofa" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "installer" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT

rangeSeq(seq) == {seq[i]: i \in DOMAIN seq} 
whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID] 

=======================================================================

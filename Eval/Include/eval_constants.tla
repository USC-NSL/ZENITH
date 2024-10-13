--------------------- MODULE eval_constants ---------------------
EXTENDS Integers, FiniteSets, TLC

(***************************************************************************)
(* This module contains definitions that we use for writing our evaluation *)
(* modules. All modules that would be involved in that process (i.e. the   *)
(* switches, Zenith, etc.) MUST extend this module.                        *)
(***************************************************************************)

(* Set of model values for our switch instances *)
CONSTANTS SW

(***************************************************************************)
(* We have the choice of using either the monolithic, simple model, or the *)
(* more complex, multi-processing model. The simple model is useful for    *)
(* simulating complete switch failures, where a whole switch crashes with  *)
(* all modules, as it shrinks the state space to explore.                  *)
(***************************************************************************)
CONSTANTS WHICH_SWITCH_MODEL

(* Identifier for the monolithic switch process *)
CONSTANTS SW_SIMPLE_ID

(* Identifier for switch type to use (either complex or simple) *)
CONSTANTS SW_SIMPLE_MODEL, SW_COMPLEX_MODEL

(*****************************************************************************)
(* To shrink the state space, we impose an order on switch failures, since   *)
(* switches are independent, and as long as all DAGs are explored, the order *)
(* of failure does not affect the states that we'll explore.                 *)
(*****************************************************************************)
CONSTANTS SW_FAIL_ORDERING

(*******************************************************************************)
(* Maximum number of flows to consider. A flow maps directly to an instruction *)
(* that can be sent to a switch via `INSTALL_FLOW`.                            *)
(*******************************************************************************)
CONSTANTS MaxNumFlows

(* Tag, labeling that a lock was free. *)
CONSTANTS NO_LOCK

(* Map, showing which modules can or cannot fail in a complex switch *)
CONSTANTS SW_MODULE_CAN_FAIL_OR_NOT

(***************************************************************************)
(* Map from control plane instances to the maximum number of failures they *) 
(* can have during the same evaluaion run.                                 *)
(***************************************************************************)
CONSTANTS MAX_NUM_CONTROLLER_SUB_FAILURE

(* Labels for distinguishing between living/dead modules *)
CONSTANTS NotFailed, Failed

(* All switches are accounted for in `WHICH_SWITCH_MODEL` *)
ASSUME WHICH_SWITCH_MODEL \in [SW -> {SW_SIMPLE_MODEL, SW_COMPLEX_MODEL}]

(* `SW_FAIL_ORDERING` must have correct form *)
ASSUME \A x \in {
        SW_FAIL_ORDERING[z]: z \in DOMAIN SW_FAIL_ORDERING
    }: \/ x = {}
       \/ \A y \in x: /\ "transient" \in DOMAIN y
                      /\ "sw" \in DOMAIN y
                      /\ "partial" \in DOMAIN y
                      /\ y.transient \in {0, 1}
                      /\ y.sw \in SW          
                      /\ y.partial \in {0, 1}

(* `SW_MODULE_CAN_FAIL_OR_NOT` must account for all sub-modules in a switch *)
ASSUME /\ "cpu" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "nicAsic" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "ofa" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "installer" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT

rangeSeq(seq) == {seq[i]: i \in DOMAIN seq} 
whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID] 

=======================================================================

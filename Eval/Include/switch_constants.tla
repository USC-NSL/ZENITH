------------------- MODULE switch_constants -------------------
EXTENDS TLC

(* Model Value identifiers for processes in complex switch model *)
CONSTANTS NIC_ASIC_IN, NIC_ASIC_OUT, OFA_IN, OFA_OUT, INSTALLER

(* Processes for creating failures *)
CONSTANTS SW_FAILURE_PROC, SW_RESOLVE_PROC, GHOST_UNLOCK_PROC

(* Message types for controller without reconciliation *)
CONSTANTS INSTALL_FLOW, DELETE_FLOW, INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY, KEEP_ALIVE

(* Extra message types for controller with reconciliation *)
CONSTANTS ALL_FLOW, FLOW_STAT_REQ, FLOW_STAT_REPLY, NO_ENTRY, ENTRY_FOUND

(* Module failure/recovery event types *)
CONSTANTS NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN, INSTALLER_UP

=============================================================================

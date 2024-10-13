-------------------------- MODULE nib_constants --------------------------
EXTENDS FiniteSets, TLC

(* IR states to track within the NIB *)
CONSTANTS IR_NONE, IR_SENT, IR_DONE

(* Switch states to track within the NIB *)
CONSTANTS SW_RUN, SW_SUSPEND

(* Label to declare an IR unlocked for other threads to work on *)
CONSTANTS IR_UNLOCK

(**************************************************************************)
(* Label for internal controller module states within NIB.                *)
(* This is the minimum set, and will be extended for each spec if needed. *)
(**************************************************************************)
CONSTANTS NO_STATUS, STATUS_START_SCHEDULING, STATUS_LOCKING, 
          STATUS_SENT_DONE, START_RESET_IR

(* Label for noting that an enqueued IR was never tagged by a thread *)
CONSTANTS NO_TAG

(* Maximum number of INSTALL IRs to consider *)
CONSTANTS MaxNumIRs

\* CONSTANTS OFC_FAILOVER, SHOULD_FAILOVER

\* CONSTANTS FAILOVER_INIT, FAILOVER_READY, FAILOVER_TERMINATE, 
\*           FAILOVER_TERMINATE_DONE, FAILOVER_NONE

\* CONSTANTS TERMINATE_NONE, TERMINATE_INIT, TERMINATE_DONE

\* CONSTANTS INIT_NONE, INIT_PROCESS, INIT_MASTER, INIT_TRANSITION

\* CONSTANTS SW_ROLE_UPDATE

\* CONSTANTS BAD_REQUEST, ROLE_REQ, ROLE_TYPE, ROLE_REPLY

\* CONSTANTS ASYNC_EVENT

===========================================================================
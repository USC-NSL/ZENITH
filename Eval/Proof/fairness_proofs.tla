---- MODULE fairness_proofs ----
EXTENDS TLAPS, zenith

\* In Zenith, Weak Fairness of all actions is assumed, but in the TLA+ specification,
\* it is only stated for `Next` and individual processes.
\* Because of how `pc` variable is defined, we have the following theorem:
\*
\* ```
\*     For any PlusCal process `proc`, where the next state predicate of `proc`
\*     consists of the disjunction of actions A1, A2, ..., Am, only one action
\*     at most is enabled at any time.
\* ```
\*
\* The plain english version of this theorem is that it is impossible for a correct
\* PlsusCal algorithm to have the `pc` variable of a single process be in more than
\* one label at once.
\*
\* This means that for every process of choice, if an action Ai is enabled, then all
\* other actions Aj such that i # j _MUST_ be disabled, or equivalently, any Aj
\* action such that i # j will remain dissabled, unless an Ai action occures.
\* With the above, we can invoke the WF/SF conjunction rule to assert that Weak/Strong
\* fairness of a process, carries to its individual actions as well (see [1], section
\* 8.5.3 for the statement and proof of this rule).
\*
\* To our knowledge, the theorem above isn't stated formally in any sources that we
\* know of (PlusCal is rarely used with TLAPS, at least for now), however, the informal
\* statement of this property appears in [2], section 5.10.1.
\*
\* TLAPS has poor support for PlusCal, thus an equivalent of this theorem is not
\* anywhere to be found, however, proving it is extremely tedious as well, thus we
\* will omit the proof for these theorems.
\*
\* References:
\*  [1] Leslie Lamport, Specifying Systems (`https://lamport.azurewebsites.net/tla/book-21-07-04.pdf`)
\*  [2] Leslie Lamport, A PlusCal User's Manual, P-Syntax Version 1.8 (`https://lamport.azurewebsites.net/tla/p-manual.pdf`)

THEOREM FAIRNESS_SW ==
    \A self \in ({SW_SIMPLE_ID} \X SW) : 
        WF_vars(swProcess(self)) => WF_vars(SwitchSimpleProcess(self))

THEOREM FAIRNESS_NIB_EH ==
    \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : 
        WF_vars(rcNibEventHandler(self)) => WF_vars(RCSNIBEventHndlerProc(self))

THEOREM FAIRNESS_TE ==
    \A self \in ({rc0} \X {CONT_TE}) : 
        WF_vars(controllerTrafficEngineering(self)) => 
            /\ WF_vars(ControllerTEProc(self))
            /\ WF_vars(ControllerTEEventProcessing(self))
            /\ WF_vars(ControllerTEComputeDagBasedOnTopo(self))
            /\ WF_vars(ControllerTEWaitForStaleDAGToBeRemoved(self))
            /\ WF_vars(ControllerTERemoveUnnecessaryIRs(self))
            /\ WF_vars(ConnectEdges(self))
            /\ WF_vars(ControllerUnscheduleIRsInDAG(self))
            /\ WF_vars(ControllerTESubmitNewDAG(self))

THEOREM FAIRNESS_BOSS ==
    \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : 
        WF_vars(controllerBossSequencer(self)) =>
            /\ WF_vars(ControllerBossSeqProc(self))
            /\ WF_vars(WaitForRCSeqWorkerTerminate(self))

THEOREM FAIRNESS_SEQ ==
    \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : 
        WF_vars(controllerSequencer(self)) =>
            /\ WF_vars(ControllerWorkerSeqProc(self))
            /\ WF_vars(ControllerWorkerSeqScheduleDAG(self))
            /\ WF_vars(SchedulerMechanism(self))
            /\ WF_vars(AddDeleteDAGIRDoneSet(self))
            /\ WF_vars(RemoveDagFromQueue(self))

THEOREM FAIRNESS_WP ==
    \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : 
        WF_vars(controllerWorkerThreads(self)) =>
            /\ WF_vars(ControllerThread(self))
            /\ WF_vars(ControllerThreadSendIR(self))
            /\ WF_vars(ControllerThreadForwardIR(self))
            /\ WF_vars(ControllerThreadRemoveIRFromQueue(self))

THEOREM FAIRNESS_EH ==
    \A self \in ({ofc0} \X {CONT_EVENT}) : 
        WF_vars(controllerEventHandler(self)) => 
            /\ WF_vars(ControllerEventHandlerProc(self))
            /\ WF_vars(ControllerEvenHanlderRemoveEventFromQueue(self))
            /\ WF_vars(ControllerSuspendSW(self))
            /\ WF_vars(ControllerRequestTCAMClear(self))
            /\ WF_vars(ControllerCheckIfThisIsLastEvent(self))
            /\ WF_vars(getIRsToBeChecked(self))
            /\ WF_vars(ResetAllIRs(self))
            /\ WF_vars(ControllerFreeSuspendedSW(self))

THEOREM FAIRNESS_MS == 
    \A self \in ({ofc0} \X {CONT_MONITOR}) : 
        WF_vars(controllerMonitoringServer(self)) => 
            /\ WF_vars(ControllerMonitorCheckIfMastr(self))
            /\ WF_vars(MonitoringServerRemoveFromQueue(self))
            /\ WF_vars(ControllerProcessIRMod(self))
            /\ WF_vars(ForwardToEH(self))
====
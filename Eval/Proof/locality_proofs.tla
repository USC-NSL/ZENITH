--------------------------- MODULE locality_proofs ---------------------------
EXTENDS TLAPS, zenith

\* `Locality` lemmas are lemmas that state that certain actions always leave certain
\* variables unchanged. These lemmas allow us to formally do away with certain steps
\* that trivially kepp certain invariants unchanged.
\* These lemmas are either for processes or whole modules:
\*  - Process Lemmas: If a certain process takes no steps, then certain variables are unchanged
\*  - Module Lemmas: If a certain module (i.e. set of processes) take no steps, then certain variables are unchanged
\* Ideally, we would only have to let TLAPS replace formula definitions and let it do the rest, but
\* since our formulas are really big, the solvers just cannot handle all of them at once, even if the
\* proof goal is trivial.
\* For sake of brevity, we show one of these and omit the rest, as they are for the most part the exact
\* same (all we need to prove is that the only primed variables that change are the local variables)

LEMMA SwitchProcessLocality ==
    \A sw \in SW: 
        TypeOK /\ AUX_TypeOK /\ Next /\ ~(swProcess(<<SW_SIMPLE_ID, sw>>)) => UNCHANGED swProcessLocals(sw)
<1> USE DEF Next, swProcessLocals, ProcSet,
            SWITCH_LABELS, SWITCH_FAIL_LABELS, SWITCH_RESOLVE_LABELS, NIB_EH_LABELS, 
            TE_LABELS, BOSS_LABELS, SEQ_LABELS, WP_LABELS, EH_LABELS, MS_LABELS, ALL_LABELS
<1> SUFFICES ASSUME 
        NEW sw \in SW, 
        TypeOK, AUX_TypeOK, Next, ~(swProcess(<<SW_SIMPLE_ID, sw>>))
    PROVE UNCHANGED swProcessLocals(sw)
        OBVIOUS 
<1>1 CASE (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
    <2>1 PICK self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self)
        BY <1>1
    <2>2 pc' = [pc EXCEPT ![self] = "SwitchFailure"]
        BY <2>1 DEF swFailureProc, SwitchFailure
    <2>3 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
        BY <2>1, <2>2 DEF TypeOK
    <2> QED BY <2>1, <2>3 DEF swFailureProc, SwitchFailure
<1>2 CASE (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
    <2>1 PICK self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self)
        BY <1>2
    <2>2 pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
        BY <2>1 DEF swResolveFailure, SwitchResolveFailure
    <2>3 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
        BY <2>1, <2>2 DEF TypeOK
    <2> QED BY <2>1, <2>3 DEF swResolveFailure, SwitchResolveFailure
<1>3 CASE (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
    <2>1 PICK self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self)
        BY <1>3
    <2>2 pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]
        BY <2>1 DEF rcNibEventHandler, RCSNIBEventHndlerProc
    <2>3 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
        BY <2>1, <2>2 DEF TypeOK
    <2> QED BY <2>1, <2>3 DEF rcNibEventHandler, RCSNIBEventHndlerProc
<1>4 CASE (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
    <2>1 PICK self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self)
        BY <1>4
    <2>2 CASE ControllerTEProc(self)
        <3>1 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
            <4>init CASE (init = TRUE)
                <5>1 pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                    BY <2>2, <4>init DEF ControllerTEProc
                <5> QED BY <5>1 DEF TypeOK
            <4>notinit CASE ~(init = TRUE)
                <5>1 pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                    BY <2>2, <4>notinit DEF ControllerTEProc
                <5> QED BY <5>1 DEF TypeOK
            <4> QED BY <4>init, <4>notinit
        <3> QED BY <2>2, <3>1 DEF ControllerTEProc
    <2>3 CASE ControllerTEEventProcessing(self)
        <3>1 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
            <4>notinit CASE (init # TRUE)
                <5>topo CASE (topoChangeEvent = NADIR_NULL)
                    <6>topo CASE (topoChangeEvent' = NADIR_NULL)
                        <7>1 pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                            BY <2>3, <4>notinit, <5>topo, <6>topo DEF ControllerTEEventProcessing
                        <7> QED BY <7>1 DEF TypeOK
                    <6>else CASE ~(topoChangeEvent' = NADIR_NULL)
                        <7>1 pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                            BY <2>3, <4>notinit, <5>topo, <6>else DEF ControllerTEEventProcessing
                        <7> QED BY <7>1 DEF TypeOK
                    <6> QED BY <6>topo, <6>else
                <5>else CASE ~(topoChangeEvent = NADIR_NULL)
                    <6>1 pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                        BY <2>3, <4>notinit, <5>else DEF ControllerTEEventProcessing
                    <6> QED BY <6>1 DEF TypeOK
                <5> QED BY <5>topo, <5>else
            <4>init CASE ~(init # TRUE)
                <5>1 pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                    BY <2>3, <4>init DEF ControllerTEEventProcessing
                <5> QED BY <5>1 DEF TypeOK
            <4> QED BY <4>notinit, <4>init
        <3> QED BY <2>3, <3>1 DEF ControllerTEEventProcessing
    <2>4 CASE ControllerTEComputeDagBasedOnTopo(self)
        <3>1 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
            <4>notinit CASE (init = FALSE)
                <5>1 pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                    BY <2>4, <4>notinit DEF ControllerTEComputeDagBasedOnTopo
                <5> QED BY <5>1 DEF TypeOK
            <4>init CASE ~(init = FALSE)
                <5>1 pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                    BY <2>4, <4>init DEF ControllerTEComputeDagBasedOnTopo
                <5> QED BY <5>1 DEF TypeOK
            <4> QED BY <4>notinit, <4>init
        <3> QED BY <2>4, <3>1 DEF ControllerTEComputeDagBasedOnTopo
    <2>5 CASE ControllerTEWaitForStaleDAGToBeRemoved(self)
        <3>1 pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
            BY <2>5 DEF ControllerTEWaitForStaleDAGToBeRemoved
        <3>2 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
            BY <3>1 DEF TypeOK
        <3> QED BY <2>5, <3>2 DEF ControllerTEWaitForStaleDAGToBeRemoved
    <2>6 CASE ControllerTERemoveUnnecessaryIRs(self)
        <3>1 pc'[<<SW_SIMPLE_ID, sw>>] = pc[<<SW_SIMPLE_ID, sw>>]
            <4>notempty CASE (Cardinality(setRemovableIRs) > 0)
                <5>1 pc' = [pc EXCEPT ![self] = "ConnectEdges"]
                    BY <2>6, <4>notempty DEF ControllerTERemoveUnnecessaryIRs
                <5> QED BY <5>1 DEF TypeOK
            <4>empty CASE ~(Cardinality(setRemovableIRs) > 0)
                <5>1 pc' = [pc EXCEPT ![self] = "ControllerUnscheduleIRsInDAG"]
                    BY <2>6, <4>empty DEF ControllerTERemoveUnnecessaryIRs
                <5> QED BY <5>1 DEF TypeOK
            <4> QED BY <4>notempty, <4>empty
        <3> QED BY <2>6, <3>1 DEF ControllerTERemoveUnnecessaryIRs
    <2>7 CASE ConnectEdges(self)
        BY <2>7 DEF ConnectEdges
    <2>8 CASE ControllerUnscheduleIRsInDAG(self)
        BY <2>8 DEF ControllerUnscheduleIRsInDAG
    <2>9 CASE ControllerTESubmitNewDAG(self)
        BY <2>9 DEF ControllerTESubmitNewDAG
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF controllerTrafficEngineering
<1>5 CASE (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
    <2>1 PICK self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self)
        BY <1>5
    <2>2 CASE ControllerBossSeqProc(self)
        BY <2>2 DEF ControllerBossSeqProc
    <2>3 CASE WaitForRCSeqWorkerTerminate(self)
        BY <2>3 DEF WaitForRCSeqWorkerTerminate
    <2> QED BY <2>1, <2>2, <2>3 DEF controllerBossSequencer
<1>6 CASE (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
    <2>1 PICK self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self)
        BY <1>6
    <2>2 CASE ControllerWorkerSeqProc(self)
        BY <2>2 DEF ControllerWorkerSeqProc
    <2>3 CASE ControllerWorkerSeqScheduleDAG(self)
        BY <2>3 DEF ControllerWorkerSeqScheduleDAG
    <2>4 CASE SchedulerMechanism(self)
        BY <2>4 DEF SchedulerMechanism
    <2>5 CASE AddDeleteDAGIRDoneSet(self)
        BY <2>5 DEF AddDeleteDAGIRDoneSet
    <2>6 CASE RemoveDagFromQueue(self)
        BY <2>6 DEF RemoveDagFromQueue
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF controllerSequencer
<1>7 CASE (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
    <2>1 PICK self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self)
        BY <1>7
    <2>2 CASE ControllerThread(self)
        BY <2>2 DEF ControllerThread
    <2>3 CASE ControllerThreadSendIR(self)
        BY <2>3 DEF ControllerThreadSendIR
    <2>4 CASE ControllerThreadForwardIR(self)
        BY <2>4 DEF ControllerThreadForwardIR
    <2>5 CASE ControllerThreadRemoveIRFromQueue(self)
        BY <2>5 DEF ControllerThreadRemoveIRFromQueue
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF controllerWorkerThreads
<1>8 CASE (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
    <2>1 PICK self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self)
        BY <1>8
    <2>2 CASE ControllerEventHandlerProc(self)
        BY <2>2 DEF ControllerEventHandlerProc
    <2>3 CASE ControllerEvenHanlderRemoveEventFromQueue(self)
        BY <2>3 DEF ControllerEvenHanlderRemoveEventFromQueue
    <2>4 CASE ControllerSuspendSW(self)
        BY <2>4 DEF ControllerSuspendSW
    <2>5 CASE ControllerRequestTCAMClear(self)
        BY <2>5 DEF ControllerRequestTCAMClear
    <2>6 CASE ControllerCheckIfThisIsLastEvent(self)
        BY <2>6 DEF ControllerCheckIfThisIsLastEvent
    <2>7 CASE getIRsToBeChecked(self)
        BY <2>7 DEF getIRsToBeChecked
    <2>8 CASE ResetAllIRs(self)
        BY <2>8 DEF ResetAllIRs
    <2>9 CASE ControllerFreeSuspendedSW(self)
        BY <2>9 DEF ControllerFreeSuspendedSW
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF controllerEventHandler
<1>9 CASE (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))
    <2>1 PICK self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self)
        BY <1>9
    <2>2 CASE ControllerMonitorCheckIfMastr(self)
        BY <2>2 DEF ControllerMonitorCheckIfMastr
    <2>3 CASE MonitoringServerRemoveFromQueue(self)
        BY <2>3 DEF MonitoringServerRemoveFromQueue
    <2>4 CASE ControllerProcessIRMod(self)
        BY <2>4 DEF ControllerProcessIRMod
    <2>5 CASE ForwardToEH(self)
        BY <2>5 DEF ForwardToEH
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF controllerMonitoringServer
<1>10 CASE (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
    <2>1 PICK self \in ({SW_SIMPLE_ID} \X SW): swProcess(self)
        BY <1>10
    <2> DEFINE other_sw == self[2]
    <2> USE DEF other_sw
    <2>2 /\ other_sw \in SW
         /\ swProcess(<<SW_SIMPLE_ID, other_sw>>)
        BY <2>1
    <2>3 other_sw # sw
        <3> SUFFICES ASSUME sw = other_sw PROVE FALSE
        <3>1 ~swProcess(<<SW_SIMPLE_ID, sw>>)
            OBVIOUS 
        <3>2 swProcess(<<SW_SIMPLE_ID, sw>>)
            BY <2>1
        <3> QED BY <3>1, <3>2
    <2>4 /\ ingressPkt' = [ingressPkt EXCEPT ![other_sw] = Head(controller2Switch[other_sw])]
         /\ AUX_C2S_deq' = [AUX_C2S_deq EXCEPT ![other_sw] = Append(AUX_C2S_deq[other_sw], ingressPkt'[other_sw])]
         /\ AUX_SEQ_deq' = [AUX_SEQ_deq EXCEPT ![other_sw] = Append(AUX_SEQ_deq[other_sw], ingressPkt'[other_sw])]
        BY <2>2 DEF swProcess, SwitchSimpleProcess
    <2>5 /\ ingressPkt'[sw] = ingressPkt[sw]
         /\ AUX_C2S_deq'[sw] = AUX_C2S_deq[sw]
         /\ AUX_SEQ_deq'[sw] = AUX_SEQ_deq[sw]
        BY <2>3, <2>4 DEF TypeOK, AUX_TypeOK
    <2> QED BY <2>5
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

LEMMA SwitchFailureLocality == 
    \A sw \in SW:
       TypeOK /\ AUX_TypeOK /\ Next /\ ~(swFailureProc(<<SW_FAILURE_PROC, sw>>)) => UNCHANGED swFailureProcLocals(sw)
PROOF OMITTED
  
LEMMA SwitchResolveLocality == 
    \A sw \in SW:
       TypeOK /\ AUX_TypeOK /\ Next /\ ~(swResolveFailure(<<SW_RESOLVE_PROC, sw>>)) => UNCHANGED swResolveFailureLocals(sw)
PROOF OMITTED

LEMMA NIBEHProcessLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~(\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self)) => UNCHANGED rcNibEventHandlerLocals
PROOF OMITTED

LEMMA TEProcessLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~(\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self)) => UNCHANGED controllerTrafficEngineeringLocals
PROOF OMITTED

LEMMA BOSSProcessLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~(\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self)) => UNCHANGED controllerBossSequencerLocals
PROOF OMITTED

LEMMA SEQProcessLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~(\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self)) => UNCHANGED controllerSequencerLocals
PROOF OMITTED

LEMMA WPProcessLocality == 
    \A t \in CONTROLLER_THREAD_POOL:
        TypeOK /\ AUX_TypeOK /\ Next /\ ~(controllerWorkerThreads(<<ofc0, t>>)) => UNCHANGED controllerWorkerThreadsLocals(t)
PROOF OMITTED

LEMMA EHProcessLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~(\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self)) => UNCHANGED controllerEventHandlerLocals
PROOF OMITTED

LEMMA MSProcessLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~(\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self)) => UNCHANGED controllerMonitoringServerLocals
PROOF OMITTED

LEMMA SwitchModuleLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~SwitchModuleActions => UNCHANGED swModuleVariables
PROOF OMITTED

LEMMA RCModuleLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~RCModuleActions => UNCHANGED rcModuleVariables
PROOF OMITTED

LEMMA OFCModuleLocality == TypeOK /\ AUX_TypeOK /\ Next /\ ~OFCModuleActions => UNCHANGED ofcModuleVariables
PROOF OMITTED

=============================================================================
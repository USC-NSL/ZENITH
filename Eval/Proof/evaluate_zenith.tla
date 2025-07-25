---- MODULE evaluate_zenith ----
EXTENDS Integers, Sequences, FiniteSets, TLC, dag

CONSTANTS SW
CONSTANTS ofc0, rc0
CONSTANTS CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_TE
CONSTANTS CONTROLLER_THREAD_POOL, CONT_MONITOR, CONT_EVENT, NIB_EVENT_HANDLER
CONSTANTS IR_NONE, IR_SENT, IR_DONE
CONSTANTS SW_RUN, SW_SUSPEND
CONSTANTS DAG_STALE, DAG_NEW, DAG_SUBMIT, DAG_NONE
CONSTANTS TOPO_MOD, IR_MOD, IR_FAILED
CONSTANTS INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM, INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY, CLEARED_TCAM_SUCCESSFULLY, KEEP_ALIVE
CONSTANTS NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN, INSTALLER_UP
CONSTANTS MaxDAGID, MaxNumIRs
CONSTANTS TOPO_DAG_MAPPING, IR2SW
CONSTANTS Failed, NotFailed
CONSTANTS SW_SIMPLE_ID, SW_RESOLVE_PROC, SW_FAILURE_PROC, SW_FAIL_ORDERING
CONSTANTS NADIR_NULL
CONSTANTS SW_THREAD_SHARD_MAP

CONSTANTS FINAL_DAG

VARIABLES sw_fail_ordering_var, switchStatus, installedIRs, TCAM, 
    controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, 
    switchObject, statusResolveMsg, swSeqChangedStatus, 
    controller2Switch, switch2Controller, TEEventQueue, DAGEventQueue, 
    DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, 
    RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, 
    ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, 
    currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, 
    setRemovableIRs, irsToUnschedule, unschedule, seqEvent, 
    toBeScheduledIRs, nextIR, currDAG, IRDoneSet, nextIRObjectToSend, 
    index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, 
    pc,
    irSet, pickedIR,
    irToRemove, irToAdd, irsToConnect, irToConnect,
    AUX_IRQ_enq, AUX_IRQ_deq, AUX_C2S_enq, AUX_C2S_deq, 
    AUX_SEQ_sched_num, AUX_SEQ_enq, AUX_SEQ_deq

vars == << sw_fail_ordering_var, switchStatus, installedIRs, TCAM, 
           controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, 
           switchObject, statusResolveMsg, swSeqChangedStatus, 
           controller2Switch, switch2Controller, TEEventQueue, DAGEventQueue, 
           DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, 
           RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, 
           ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, 
           currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, 
           setRemovableIRs, irsToUnschedule, unschedule, seqEvent, 
           toBeScheduledIRs, nextIR, currDAG, IRDoneSet, nextIRObjectToSend, 
           index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, 
           pc, irSet, pickedIR, irToRemove, irToAdd, irsToConnect, irToConnect,
           AUX_IRQ_enq, AUX_IRQ_deq, AUX_C2S_enq, AUX_C2S_deq, 
           AUX_SEQ_sched_num, AUX_SEQ_enq, AUX_SEQ_deq >>

(* All of our processes *)
ProcSet == 
    (({SW_SIMPLE_ID} \X SW)) \cup 
    (({SW_FAILURE_PROC} \X SW)) \cup 
    (({SW_RESOLVE_PROC} \X SW)) \cup 
    (({rc0} \X {NIB_EVENT_HANDLER})) \cup 
    (({rc0} \X {CONT_TE})) \cup 
    (({rc0} \X {CONT_BOSS_SEQ})) \cup 
    (({rc0} \X {CONT_WORKER_SEQ})) \cup 
    (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup 
    (({ofc0} \X {CONT_EVENT})) \cup 
    (({ofc0} \X {CONT_MONITOR}))

Init == (* Global variables *)
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ switchStatus =                [
                              x \in SW |-> [
                                  cpu |-> NotFailed,
                                  nicAsic |-> NotFailed,
                                  ofa |-> NotFailed,
                                  installer |-> NotFailed
                              ]
                          ]
        /\ installedIRs = <<>>
        /\ TCAM = [x \in SW |-> {}]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
        /\ ingressPkt = [x \in SW |-> NADIR_NULL]
        /\ statusMsg = [x \in SW |-> NADIR_NULL]
        /\ switchObject = [x \in SW |-> NADIR_NULL]
        /\ statusResolveMsg = [x \in SW |-> NADIR_NULL]
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ TEEventQueue = <<>>
        /\ DAGEventQueue = <<>>
        /\ DAGQueue = <<>>
        /\ IRQueueNIB = <<>>
        /\ RCNIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ ScheduledIRs = [x \in 1..2*MaxNumIRs |-> FALSE]
        /\ seqWorkerIsBusy = FALSE
        /\ nibEvent = NADIR_NULL
        /\ topoChangeEvent = NADIR_NULL
        /\ currSetDownSw = {}
        /\ prev_dag_id = NADIR_NULL
        /\ init = TRUE
        /\ DAGID = NADIR_NULL
        /\ nxtDAG = NADIR_NULL
        /\ nxtDAGVertices = {}
        /\ setRemovableIRs = {}
        /\ irsToUnschedule = {}
        /\ unschedule = NADIR_NULL
        /\ seqEvent = NADIR_NULL
        /\ toBeScheduledIRs = {}
        /\ nextIR = NADIR_NULL
        /\ currDAG = NADIR_NULL
        /\ IRDoneSet = {}
        /\ nextIRObjectToSend = [t \in CONTROLLER_THREAD_POOL |-> NADIR_NULL]
        /\ index = [t \in CONTROLLER_THREAD_POOL |-> 0]
        /\ monitoringEvent = NADIR_NULL
        /\ setIRsToReset = {}
        /\ resetIR = NADIR_NULL
        /\ msg = NADIR_NULL
        /\ currentIRID = NADIR_NULL
        /\ irSet = {}
        /\ pickedIR = NADIR_NULL
        /\ irToRemove = NADIR_NULL
        /\ irToAdd = NADIR_NULL
        /\ irsToConnect = {}
        /\ irToConnect = NADIR_NULL
        /\ AUX_IRQ_enq = [t \in CONTROLLER_THREAD_POOL |-> <<>>]
        /\ AUX_IRQ_deq = [t \in CONTROLLER_THREAD_POOL |-> <<>>]
        /\ AUX_C2S_enq = [sw \in SW |-> <<>>]
        /\ AUX_C2S_deq = [sw \in SW |-> <<>>]
        /\ AUX_SEQ_sched_num = 1
        /\ AUX_SEQ_enq = [sw \in SW |-> <<>>]
        /\ AUX_SEQ_deq = [sw \in SW |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

Zenith == INSTANCE zenith

SwitchStep == \E self \in ({SW_SIMPLE_ID} \X SW): Zenith!swProcess(self)
SwitchFailStep == \E self \in ({SW_FAILURE_PROC} \X SW): Zenith!swFailureProc(self)
SwitchRecoveryStep == \E self \in ({SW_RESOLVE_PROC} \X SW): Zenith!swResolveFailure(self)
RCNibEventHandlerStep == \E self \in ({rc0} \X {NIB_EVENT_HANDLER}): Zenith!rcNibEventHandler(self)
ControllerTrafficEngineeringStep == \E self \in ({rc0} \X {CONT_TE}): Zenith!controllerTrafficEngineering(self)
ControllerBossSequencerStep == \E self \in ({rc0} \X {CONT_BOSS_SEQ}): Zenith!controllerBossSequencer(self)
ControllerSequencerStep == \E self \in ({rc0} \X {CONT_WORKER_SEQ}): Zenith!controllerSequencer(self)
ControllerWorkerThreadsStep == \E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): Zenith!controllerWorkerThreads(self)
ControllerEventHandlerStep == \E self \in ({ofc0} \X {CONT_EVENT}): Zenith!controllerEventHandler(self)
ControllerMonitoringServerStep == \E self \in ({ofc0} \X {CONT_MONITOR}): Zenith!controllerMonitoringServer(self)

Next == \/ SwitchStep
        \/ SwitchFailStep
        \/ SwitchRecoveryStep
        \/ RCNibEventHandlerStep
        \/ ControllerTrafficEngineeringStep
        \/ ControllerBossSequencerStep
        \/ ControllerSequencerStep
        \/ ControllerWorkerThreadsStep
        \/ ControllerEventHandlerStep
        \/ ControllerMonitoringServerStep

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(Zenith!swProcess(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(Zenith!swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(Zenith!swResolveFailure(self))
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(Zenith!rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(Zenith!controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(Zenith!controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(Zenith!controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(Zenith!controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(Zenith!controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(Zenith!controllerMonitoringServer(self))

ModuleSpec == 
    /\ Init 
    /\ [][Zenith!ModuleNext]_vars
    /\ WF_vars(Zenith!ModuleNext)
    /\ Zenith!SWModuleFairness
    /\ Zenith!RCModuleFairness
    /\ Zenith!OFCModuleFairness

\* Liveness Properties
CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in FINAL_DAG.v
                                                  /\ x \in TCAM[Zenith!getSwitchForIR(x)]
                                               \/ /\ x \notin FINAL_DAG.v
                                                  /\ x \notin TCAM[Zenith!getSwitchForIR(x)])
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ NIBIRStatus[x].primary = IR_DONE
                                                       \/ x \notin FINAL_DAG.v)
                                                       
InstallationLivenessProp == <>[] (/\ CorrectDAGInstalled 
                                  /\ CorrectDoneStatusController)
\* Safety Properties
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
whichDAG(ir) == CHOOSE x \in rangeSeq(TOPO_DAG_MAPPING): ir \in x.v

ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ whichDAG(Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)) # whichDAG(Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY))
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)                                                         
                                                         /\ <<Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e

TypeOK == Zenith!TypeOK
AUX_TypeOK == Zenith!AUX_TypeOK
AUX_SeqOrderPreserved == Zenith!AUX_SeqOrderPreserved
IRQ_ordering == Zenith!IRQ_ordering
C2S_ordering == Zenith!C2S_ordering
continuity_C2S_to_switch == Zenith!continuity_C2S_to_switch
continuity_IRQ_to_C2S == Zenith!continuity_IRQ_to_C2S
continuity_SEQ_to_IRQ == Zenith!continuity_SEQ_to_IRQ
progression_inv == Zenith!progression_inv

CONSTANTS
s0, s1
----

CONSTANTS
t0
----

\* Consider a topology of 2 switches
const_SW == {s0, s1}
----

\* Since we build on top of `CompletePermanentFailure`, we can just use 1 thread
const_CONTROLLER_THREAD_POOL == {t0}
----

\* Consider only transient failures (so no partial and complete)
\* const_SW_FAIL_ORDERING == <<>>
const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 1]}>>
\* const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 1]}, {[sw |-> s0, partial |-> 0, transient |-> 1]}>>
\* const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 1]}, {[sw |-> s1, partial |-> 0, transient |-> 1]}>>
----

\* Consider 3 instructions to install
const_MaxNumIRs == 3
\* const_MaxNumIRs == 4
----

const_MaxDAGID == 15
----

\* Eventually, assuming fairness, we converge to the case where all switches are alive and the DAG is installed
const_FINAL_DAG == [v |-> {1, 2}, e |-> {<<1, 2>>}]

\* Where to install each IR?
const_IR2SW == (1 :> s0) @@ (2 :> s1) @@ (3 :> s1)
\* const_IR2SW == (1 :> s0) @@ (2 :> s1) @@ (3 :> s1) @@ (4 :> s0)

\* Mapping between topology and DAG
const_TOPO_DAG_MAPPING == 
    ({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ 
    ({s0} :> [v |-> {3}, e |-> {}])
\* const_TOPO_DAG_MAPPING == 
\*     ({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ 
\*     ({s0} :> [v |-> {3}, e |-> {}]) @@
\*     ({s1} :> [v |-> {4}, e |-> {}]) @@
\*     ({s0, s1} :> [v |-> {}, e |-> {}])

const_SW_THREAD_SHARD_MAP == (s0 :> t0) @@ (s1 :> t0)

====
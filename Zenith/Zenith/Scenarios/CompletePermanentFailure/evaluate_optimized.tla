---------------------------- MODULE evaluate_optimized ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag, NadirTypes, NadirAckQueue

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR, CONT_EVENT, 
          WATCH_DOG, NIB_EVENT_HANDLER, CONT_TE
CONSTANTS TOPO_DAG_MAPPING, IR2SW, FINAL_DAG

(* Lock for switch and controller for optimization, shared between the two *)
VARIABLES switchLock, controllerLock

(* Shared queues between Zenith and the switch *)
VARIABLES swSeqChangedStatus, controller2Switch, switch2Controller

(* This is a hidden variable of switch specification, which we will expose. *)
VARIABLES installedIRs

(* These are hidden variables of Zenith specification, which we will expose. *)
VARIABLES NIBIRStatus, FirstInstall

(* PlusCal program counter, shared between the two modules *)
VARIABLES pc

(* Internal variables, we'll not bother hiding them, since there is quite a few of them *)

\* For switches
VARIABLES sw_fail_ordering_var, SwProcSet, 
          switchStatus, NicAsic2OfaBuff, Ofa2NicAsicBuff, 
          Installer2OfaBuff, Ofa2InstallerBuff, TCAM, controlMsgCounter, 
          RecoveryStatus, ingressPkt, ingressIR, egressMsg, ofaInMsg, 
          ofaOutConfirmation, installerInIR, statusMsg, notFailedSet, 
          failedElem, obj, failedSet, statusResolveMsg, recoveredElem

\* For zenith
VARIABLES TEEventQueue, DAGEventQueue, DAGQueue, nextIRIDToSend,
          IRQueueNIB, RCNIBEventQueue, 
          ContProcSet, RCProcSet, OFCProcSet, 
          controllerSubmoduleFailNum, controllerSubmoduleFailStat, DAGState, 
          RCIRStatus, RCSwSuspensionStatus, SwSuspensionStatus, 
          rcInternalState, ofcInternalState, seqWorkerIsBusy,
          SetScheduledIRs, 
          DAGID, deleterID,
          monitoringEvent, index, toBeScheduledIRs, 
          stepOfFailure, stepOfFailure_, stepOfFailure_c,
          setRemovableIRs, currDAG, nextIR, currIR, init, worker, currSetDownSw,
          event, msg, resetIR, currIRInDAG, prev_dag_id, topoChangeEvent,
          setIRsToReset, nxtDAGVertices, irID, setIRsInDAG, 
          seqEvent, nxtDAG, controllerFailedModules


(* Each time either of the switches OR Zenith take a step, these CAN change *)
shared_vars == <<
    switchLock, controllerLock,
    swSeqChangedStatus, controller2Switch, switch2Controller,
    pc
>>

(* Each time Zenith takes a step, these remain unchanged *)
internal_switch_vars == <<
    installedIRs,
    sw_fail_ordering_var, SwProcSet, 
    switchStatus, NicAsic2OfaBuff, Ofa2NicAsicBuff, 
    Installer2OfaBuff, Ofa2InstallerBuff, TCAM, controlMsgCounter, 
    RecoveryStatus, ingressPkt, ingressIR, egressMsg, ofaInMsg, 
    ofaOutConfirmation, installerInIR, statusMsg, notFailedSet, 
    failedElem, obj, failedSet, statusResolveMsg, recoveredElem
>>

(* Each time a switch takes a step, these remain unchanged *)
internal_zenith_vars == <<
    NIBIRStatus, FirstInstall, nextIRIDToSend,
    TEEventQueue, DAGEventQueue, DAGQueue, 
    IRQueueNIB, RCNIBEventQueue, 
    ContProcSet, RCProcSet, OFCProcSet, 
    controllerSubmoduleFailNum, controllerSubmoduleFailStat, DAGState, 
    RCIRStatus, RCSwSuspensionStatus, SwSuspensionStatus, 
    rcInternalState, ofcInternalState,
    SetScheduledIRs, 
    DAGID, deleterID, 
    monitoringEvent, index, toBeScheduledIRs, 
    stepOfFailure, stepOfFailure_, stepOfFailure_c,
    setRemovableIRs, currDAG, nextIR, currIR, init, worker, currSetDownSw,
    event, msg, resetIR, currIRInDAG, prev_dag_id, topoChangeEvent,
    setIRsToReset, nxtDAGVertices, irID, setIRsInDAG, 
    seqEvent, nxtDAG, controllerFailedModules, seqWorkerIsBusy
>>

(* Any one of these variables can stutter ... *)

vars == <<
    switchLock, controllerLock,
    swSeqChangedStatus, controller2Switch, switch2Controller,
    pc,
    installedIRs,
    sw_fail_ordering_var, SwProcSet, 
    switchStatus, NicAsic2OfaBuff, Ofa2NicAsicBuff, 
    Installer2OfaBuff, Ofa2InstallerBuff, TCAM, controlMsgCounter, 
    RecoveryStatus, ingressPkt, ingressIR, egressMsg, ofaInMsg, 
    ofaOutConfirmation, installerInIR, statusMsg, notFailedSet, 
    failedElem, obj, failedSet, statusResolveMsg, recoveredElem,
    NIBIRStatus, FirstInstall, nextIRIDToSend,
    TEEventQueue, DAGEventQueue, DAGQueue, 
    IRQueueNIB, RCNIBEventQueue, 
    ContProcSet, RCProcSet, OFCProcSet, 
    controllerSubmoduleFailNum, controllerSubmoduleFailStat, DAGState, 
    RCIRStatus, RCSwSuspensionStatus, SwSuspensionStatus, 
    rcInternalState, ofcInternalState,
    SetScheduledIRs, 
    DAGID, deleterID, seqWorkerIsBusy,
    monitoringEvent, index, toBeScheduledIRs, 
    stepOfFailure, stepOfFailure_, stepOfFailure_c,
    setRemovableIRs, currDAG, nextIR, currIR, init, worker, currSetDownSw,
    event, msg, resetIR, currIRInDAG, prev_dag_id, topoChangeEvent,
    setIRsToReset, nxtDAGVertices, irID, setIRsInDAG, 
    seqEvent, nxtDAG, controllerFailedModules
>>

(* All of our processes *)
ProcSet == 
    (* Switches *)
    (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup 
    (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup 
    (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup 
    (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup 
    (({GHOST_UNLOCK_PROC} \X SW)) \cup 
    (* Zenith *)
    (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup 
    (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup 
    (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup 
    (({ofc0} \X {CONT_MONITOR})) \cup (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Locks *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        (* Shared queues *)
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        (* Exposed Zenith variables *)
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        (* Hidden Zenith variables *)
        /\ TEEventQueue = <<>>
        /\ DAGEventQueue = <<>>
        /\ DAGQueue = <<>>
        /\ IRQueueNIB = <<>>
        /\ RCNIBEventQueue = <<>>
        /\ RCProcSet = ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, NIB_EVENT_HANDLER, CONT_TE})
        /\ OFCProcSet = ((({ofc0} \X CONTROLLER_THREAD_POOL)) \cup
                         (({ofc0} \X {CONT_EVENT})) \cup
                         (({ofc0} \X {CONT_MONITOR})))
        /\ ContProcSet = (RCProcSet \cup OFCProcSet)
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ rcInternalState = [x \in RCProcSet |-> [type |-> NO_STATUS]]
        /\ ofcInternalState = [x \in OFCProcSet |-> [type |-> NO_STATUS]]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ seqWorkerIsBusy = FALSE
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> [type |-> 0]]
        /\ topoChangeEvent = [self \in ({rc0} \X {CONT_TE}) |-> [type |-> 0]]
        /\ currSetDownSw = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag_id = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ init = [self \in ({rc0} \X {CONT_TE}) |-> 1]
        /\ DAGID = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ nxtDAG = [self \in ({rc0} \X {CONT_TE}) |-> [type |-> 0]]
        /\ deleterID = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ setRemovableIRs = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ currIR = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ currIRInDAG = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ nxtDAGVertices = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ setIRsInDAG = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ seqEvent = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> [type |-> 0]]
        /\ worker = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> 0]
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> [dag |-> 0]]
        /\ nextIRIDToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ stepOfFailure_c = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ stepOfFailure = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [type |-> 0]]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
        /\ controllerFailedModules = [self \in ({ofc0, rc0} \X {WATCH_DOG}) |-> {}]
        (* Exposed switch variables *)
        /\ installedIRs = <<>>
        (* Hidden switch variables *)
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ SwProcSet = ((({NIC_ASIC_IN} \X SW)) \cup
                        (({NIC_ASIC_OUT} \X SW)) \cup
                        (({OFA_IN} \X SW)) \cup
                        (({OFA_OUT} \X SW)) \cup
                        (({INSTALLER} \X SW)) \cup
                        (({SW_FAILURE_PROC} \X SW)) \cup
                        (({SW_RESOLVE_PROC} \X SW)))
        /\ switchStatus = [
                              x \in SW |-> [
                                  cpu |-> NotFailed,
                                  nicAsic |-> NotFailed,
                                  ofa |-> NotFailed,
                                  installer |-> NotFailed
                              ]
                          ]
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> <<>>]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
        /\ ingressPkt = [self \in ({SW_SIMPLE_ID} \X SW) |-> [type |-> 0]]
        /\ ingressIR = [self \in ({NIC_ASIC_IN} \X SW) |-> [type |-> 0]]
        /\ egressMsg = [self \in ({NIC_ASIC_OUT} \X SW) |-> [type |-> 0]]
        /\ ofaInMsg = [self \in ({OFA_IN} \X SW) |-> [type |-> 0]]
        /\ ofaOutConfirmation = [self \in ({OFA_OUT} \X SW) |-> 0]
        /\ installerInIR = [self \in ({INSTALLER} \X SW) |-> 0]
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> <<>>]
        /\ notFailedSet = [self \in ({SW_FAILURE_PROC} \X SW) |-> {}]
        /\ failedElem = [self \in ({SW_FAILURE_PROC} \X SW) |-> ""]
        /\ obj = [self \in ({SW_FAILURE_PROC} \X SW) |-> [type |-> 0]]
        /\ failedSet = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> <<>>]
        /\ recoveredElem = [self \in ({SW_RESOLVE_PROC} \X SW) |-> ""]
        (* Global program counter *)
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({NIC_ASIC_IN} \X SW) -> "SwitchRcvPacket"
                                        [] self \in ({NIC_ASIC_OUT} \X SW) -> "SwitchFromOFAPacket"
                                        [] self \in ({OFA_IN} \X SW) -> "SwitchOfaProcIn"
                                        [] self \in ({OFA_OUT} \X SW) -> "SwitchOfaProcOut"
                                        [] self \in ({INSTALLER} \X SW) -> "SwitchInstallerProc"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({ofc0, rc0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

(* Get instances of Zenith and the topology and create the `Next` predicate *)
Switch == INSTANCE switch
Zenith == INSTANCE optimized

SwitchStep == /\ Switch!Next
              /\ UNCHANGED internal_zenith_vars
ZenithStep == /\ Zenith!Next
              /\ UNCHANGED internal_switch_vars

Next == \/ SwitchStep
        \/ ZenithStep

(* Evaluation specification *)
Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_internal_switch_vars(Switch!swProcess(self))
        /\ \A self \in ({NIC_ASIC_IN} \X SW) : WF_internal_switch_vars(Switch!swNicAsicProcPacketIn(self))
        /\ \A self \in ({NIC_ASIC_OUT} \X SW) : WF_internal_switch_vars(Switch!swNicAsicProcPacketOut(self))
        /\ \A self \in ({OFA_IN} \X SW) : WF_internal_switch_vars(Switch!ofaModuleProcPacketIn(self))
        /\ \A self \in ({OFA_OUT} \X SW) : WF_internal_switch_vars(Switch!ofaModuleProcPacketOut(self))
        /\ \A self \in ({INSTALLER} \X SW) : WF_internal_switch_vars(Switch!installerModuleProc(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_internal_switch_vars(Switch!swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_internal_switch_vars(Switch!swResolveFailure(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_internal_switch_vars(Switch!ghostUnlockProcess(self))
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_internal_zenith_vars(Zenith!rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_internal_zenith_vars(Zenith!controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_internal_zenith_vars(Zenith!controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_internal_zenith_vars(Zenith!controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_internal_zenith_vars(Zenith!controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_internal_zenith_vars(Zenith!controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_internal_zenith_vars(Zenith!controllerMonitoringServer(self))
        /\ \A self \in ({ofc0, rc0} \X {WATCH_DOG}) : WF_internal_zenith_vars(Zenith!watchDog(self))

\* Liveness Properties
CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in FINAL_DAG.v
                                                  /\ \E y \in DOMAIN TCAM[Zenith!getSwitchForIR(x)]: TCAM[Zenith!getSwitchForIR(x)][y] = x
                                               \/ /\ x \notin FINAL_DAG.v
                                                  /\ ~\E y \in DOMAIN TCAM[Zenith!getSwitchForIR(x)]: TCAM[Zenith!getSwitchForIR(x)][y] = x)
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ NIBIRStatus[x] = IR_DONE
                                                       \/ x \notin FINAL_DAG.v)
                                                       
InstallationLivenessProp == <>[] (/\ CorrectDAGInstalled 
                                  /\ CorrectDoneStatusController)
\* Safety Properties
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
whichDAG(ir) == CHOOSE x \in rangeSeq(TOPO_DAG_MAPPING): ir \in x.v

ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ whichDAG(Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)) # whichDAG(Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY))
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)                                                         
                                                         /\ <<Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e

----
(* EVALUATION *)
----

CONSTANTS
s0, s1, s2
----

CONSTANTS
t0
----

\* Consider a topology of 3 switches
const_SW == {s0, s1, s2}
----

\* Synchronization of the worker pool remains unchanged since `BothTransientFailure` spec,
\* thus we can be sure that it is correct with regards to races between two threads in it.
\* Since the state space is large, we simplify it into a single thread.
const_CONTROLLER_THREAD_POOL == {t0}
----

\* Consider only complete failures (so no partial and transient)
const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 0]}>>
----

\* Consider 5 instructions to install
const_MaxNumIRs == 5
----

const_MaxDAGID == 15
----

\* This spec has a pretty large state space, so let us put aside OFC module failures
\* We have already verified that we are robust to them as part of `bothTransientFailure`
const_MAX_NUM_CONTROLLER_SUB_FAILURE == [ofc0 |-> 0, rc0 |-> 0]
----

\* Use the simple switch model
\* Since this is a complete failure, there is no point in simulating internal behavior
const_WHICH_SWITCH_MODEL == (s0 :> SW_SIMPLE_MODEL) @@ 
                            (s1 :> SW_SIMPLE_MODEL) @@ 
                            (s2 :> SW_SIMPLE_MODEL)
----

\* Because of a technicallity, we need to allow CPU failures, but ideally this would not have an effect
const_SW_MODULE_CAN_FAIL_OR_NOT == [cpu |-> 1, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* Where to install each IR?
const_IR2SW == (1 :> s0) @@ (2 :> s1) @@ (3 :> s2) @@ (4 :> s1) @@ (5 :> s2)

\* Mapping between topology and DAG
const_TOPO_DAG_MAPPING == 
    \* Start with a single IR on each switch
    ({} :> [v |-> {1, 2, 3}, e |-> {<<1, 2>>, <<1, 3>>}]) @@ 
    \* Then, let `s0` go away and install 2 completely new IRs
    ({s0} :> [v |-> {4, 5}, e |-> {<<5, 4>>}])

\* The network should end up with the following DAG always
const_FINAL_DAG == [v |-> {4, 5}, e |-> {<<5, 4>>}]

=============================================================================

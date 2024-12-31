---------------------------- MODULE evaluate_nr_simplified ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, dag, nib_constants, NadirTypes

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR, CONT_EVENT, 
          WATCH_DOG, NIB_EVENT_HANDLER, CONT_TE
CONSTANTS TOPO_DAG_MAPPING, IR2SW, IR2FLOW, FINAL_DAG
CONSTANTS RCProcSet, OFCProcSet

(* Lock for switch and controller for optimization, shared between the two *)
VARIABLES switchLock, controllerLock

(* Shared queues between Zenith and the switch *)
VARIABLES swSeqChangedStatus, controller2Switch, switch2Controller

(* This is a hidden variable of switch specification, which we will expose. *)
VARIABLES installedIRs

(* These are hidden variables of Zenith specification, which we will expose. *)
VARIABLES NIBIRStatus, nextIRIDToSend

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
VARIABLES TEEventQueue, DAGEventQueue, DAGQueue, 
          IRQueueNIB, RCNIBEventQueue,
          DAGState, RCIRStatus, 
          RCSwSuspensionStatus, SwSuspensionStatus, 
          rcInternalState, ofcInternalState, SetScheduledIRs, 
          ir2sw, seqWorkerIsBusy, IRDoneSet, idThreadWorkingOnIR, 
          event, topoChangeEvent, currSetDownSw, 
          prev_dag_id, init, DAGID, nxtDAG, deleterID, setRemovableIRs, 
          currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, 
          seqEvent, worker, toBeScheduledIRs, nextIR,
          currDAG, IRSet, index, 
          monitoringEvent, setIRsToReset, 
          resetIR, msg, irID, removedIR


(* Each time either of the switches OR Zenith take a step, these CAN change *)
shared_vars == <<
    swSeqChangedStatus, controller2Switch, switch2Controller,
    pc
>>

(* Each time Zenith takes a step, these remain unchanged *)
internal_switch_vars == <<
    installedIRs,
    switchLock, controllerLock,
    sw_fail_ordering_var, SwProcSet, 
    switchStatus, NicAsic2OfaBuff, Ofa2NicAsicBuff, 
    Installer2OfaBuff, Ofa2InstallerBuff, TCAM, controlMsgCounter, 
    RecoveryStatus, ingressPkt, ingressIR, egressMsg, ofaInMsg, 
    ofaOutConfirmation, installerInIR, statusMsg, notFailedSet, 
    failedElem, obj, failedSet, statusResolveMsg, recoveredElem
>>

(* Each time a switch takes a step, these remain unchanged *)
internal_zenith_vars == <<
    TEEventQueue, DAGEventQueue, DAGQueue, 
    IRQueueNIB, RCNIBEventQueue, 
    DAGState, RCIRStatus, 
    RCSwSuspensionStatus, NIBIRStatus, SwSuspensionStatus, 
    rcInternalState, ofcInternalState, SetScheduledIRs, 
    ir2sw, seqWorkerIsBusy, IRDoneSet, idThreadWorkingOnIR, 
    event, topoChangeEvent, currSetDownSw, 
    prev_dag_id, init, DAGID, nxtDAG, deleterID, setRemovableIRs, 
    currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, 
    seqEvent, worker, toBeScheduledIRs, nextIR,
    currDAG, IRSet, nextIRIDToSend, index, 
    monitoringEvent, setIRsToReset, 
    resetIR, msg, irID, removedIR
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
    TEEventQueue, DAGEventQueue, DAGQueue, 
    IRQueueNIB, RCNIBEventQueue, 
    DAGState, RCIRStatus, 
    RCSwSuspensionStatus, NIBIRStatus, SwSuspensionStatus, 
    rcInternalState, ofcInternalState, SetScheduledIRs, 
    ir2sw, seqWorkerIsBusy, IRDoneSet, idThreadWorkingOnIR, 
    event, topoChangeEvent, currSetDownSw, 
    prev_dag_id, init, DAGID, nxtDAG, deleterID, setRemovableIRs, 
    currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, 
    seqEvent, worker, toBeScheduledIRs, nextIR,
    currDAG, IRSet, nextIRIDToSend, index, 
    monitoringEvent, setIRsToReset, 
    resetIR, msg, irID, removedIR
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
    (({ofc0} \X {CONT_MONITOR}))

(* Get instances of Zenith and the topology and create the `Next` predicate *)
Switch == INSTANCE switch
Zenith == INSTANCE zenith_nr_simplified

Init == (* Locks *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        (* Shared queues *)
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        (* Exposed Zenith variables *)
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ nextIRIDToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        (* Hidden Zenith variables *)
        /\ TEEventQueue = <<>>
        /\ DAGEventQueue = <<>>
        /\ DAGQueue = <<>>
        /\ IRQueueNIB = <<>>
        /\ RCNIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ rcInternalState = [x \in RCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]]
        /\ ofcInternalState = [x \in OFCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ ir2sw = IR2SW
        /\ seqWorkerIsBusy = FALSE
        /\ idThreadWorkingOnIR = [x \in 1..2*MaxNumIRs |-> NADIR_NULL]
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> NADIR_NULL]
        /\ topoChangeEvent = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ currSetDownSw = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag_id = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ init = [self \in ({rc0} \X {CONT_TE}) |-> 1]
        /\ DAGID = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ nxtDAG = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ deleterID = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ setRemovableIRs = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ currIR = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ currIRInDAG = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ nxtDAGVertices = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ setIRsInDAG = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ seqEvent = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        /\ worker = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ IRDoneSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ removedIR = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
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
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

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

\* Liveness Properties
CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in FINAL_DAG.v
                                                  /\ \E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x]
                                               \/ /\ x \notin FINAL_DAG.v
                                                  /\ ~\E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x])
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ NIBIRStatus[x] = IR_DONE
                                                       \/ x \notin FINAL_DAG.v)
                                                       
InstallationLivenessProp == <>[] (/\ CorrectDAGInstalled 
                                  /\ CorrectDoneStatusController)
InstallationInvProp == \/ ENABLED Next
                       \/ /\ CorrectDAGInstalled
                          /\ CorrectDoneStatusController
\* Safety Properties
IRCriticalSection == LET 
                        IRCriticalSet == {"ControllerThreadSendIR", "ControllerThreadForwardIR", "ControllerThreadSaveToDB2", "WaitForIRToHaveCorrectStatus", "ReScheduleifIRNone"}
                     IN   
                        \A x, y \in {ofc0} \X CONTROLLER_THREAD_POOL: \/ x = y
                                                                      \/ <<pc[x], pc[y]>> \notin IRCriticalSet \X IRCriticalSet
                                                                      \/ /\ <<pc[x], pc[y]>> \in IRCriticalSet \X IRCriticalSet
                                                                         /\ nextIRIDToSend[x] # nextIRIDToSend[y]

firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
whichDAG(ir) == CHOOSE x \in rangeSeq(TOPO_DAG_MAPPING): ir \in x.v

ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ whichDAG(Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)) # whichDAG(Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY))
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)                                                         
                                                         /\ <<Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e

TypeOK == Zenith!TypeOK
----
(* EVALUATION *)
----

\* Processes
const_RCProcSet == NadirProcessIdentifier(rc0, {CONT_WORKER_SEQ, CONT_BOSS_SEQ, NIB_EVENT_HANDLER, CONT_TE, CONT_MONITOR})
const_OFCProcSet == NadirProcessIdentifier(ofc0, CONTROLLER_THREAD_POOL \cup {CONT_EVENT, CONT_MONITOR})

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
const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 1]}>>
----

\* Consider 3 instructions to install
const_MaxNumIRs == 3
----

const_MaxDAGID == 15
----

\* Since we build on top of `CompletePermanentFailure`, we can just focus on switch failures
const_MAX_NUM_CONTROLLER_SUB_FAILURE == [ofc0 |-> 0, rc0 |-> 0]
----

\* Use the simple switch model
const_WHICH_SWITCH_MODEL == (s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

const_SW_MODULE_CAN_FAIL_OR_NOT == [cpu |-> 0, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* Eventually, assuming fairness, we converge to the case where all switches are alive and the DAG is installed
const_FINAL_DAG == [v |-> {1, 2}, e |-> {<<1, 2>>}]

const_IR2FLOW == [x \in 1..MaxNumIRs |-> x]

\* Where to install each IR?
const_IR2SW == (1 :> s0) @@ (2 :> s1) @@ (3 :> s1)

\* Mapping between topology and DAG
const_TOPO_DAG_MAPPING == 
    ({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ 
    ({s0} :> [v |-> {3}, e |-> {}])

=============================================================================

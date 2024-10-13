---------------------------- MODULE evaluate ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, dag, nib_constants

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_SEQ, CONT_MONITOR, CONT_EVENT, WATCH_DOG

(* Lock for switch and controller for optimization, shared between the two *)
VARIABLES switchLock, controllerLock

(* Shared queues between Zenith and the switch *)
VARIABLES swSeqChangedStatus, controller2Switch, switch2Controller

(* This is a hidden variable of switch specification, which we will expose. *)
VARIABLES installedIRs

(* These are hidden variables of Zenith specification, which we will expose. *)
VARIABLES dependencyGraph, IRStatus, FirstInstall, nextIRToSent

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
VARIABLES ContProcSet, 
          controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
          IR2SW, idThreadWorkingOnIR, controllerStateNIB, 
          SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, 
          switchOrdering, workerThreadRanking, toBeScheduledIRs, nextIR, 
          stepOfFailure_, rowIndex, rowRemove, stepOfFailure_c, 
          monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, 
          controllerFailedModules 

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
    dependencyGraph, IRStatus, FirstInstall, nextIRToSent,
    ContProcSet, 
    controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
    IR2SW, idThreadWorkingOnIR, controllerStateNIB, 
    SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, 
    switchOrdering, workerThreadRanking, toBeScheduledIRs, nextIR, 
    stepOfFailure_, rowIndex, rowRemove, stepOfFailure_c, 
    monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, 
    controllerFailedModules
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
    dependencyGraph, IRStatus, FirstInstall, nextIRToSent,
    ContProcSet, 
    controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
    IR2SW, idThreadWorkingOnIR, controllerStateNIB, 
    SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, 
    switchOrdering, workerThreadRanking, toBeScheduledIRs, nextIR, 
    stepOfFailure_, rowIndex, rowRemove, stepOfFailure_c, 
    monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, 
    controllerFailedModules
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
    (({rc0} \X {CONT_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup 
    (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})) \cup 
    (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Locks *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        (* Shared queues *)
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        (* Exposed Zenith variables *)
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ nextIRToSent = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Hidden Zenith variables *)
        /\ ContProcSet = ((({rc0} \X {CONT_SEQ})) \cup
                            (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup
                            (({ofc0} \X {CONT_EVENT})) \cup
                            (({ofc0} \X {CONT_MONITOR})))
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ switchOrdering = (CHOOSE x \in [SW -> 1..Cardinality(SW)]:
                        ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ IR2SW = (CHOOSE x \in [1..MaxNumIRs -> SW]:
                    ~\E y, z \in DOMAIN x: /\ y > z
                                           /\ switchOrdering[x[y]] =< switchOrdering[x[z]])
        /\ idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK]
        /\ controllerStateNIB = [
                                    x \in ContProcSet |-> [
                                        type |-> NO_STATUS
                                    ]
                                ]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]:
                                  ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ rowIndex = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ rowRemove = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ stepOfFailure_c = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ stepOfFailure = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [type |-> 0]]
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
                                        [] self \in ({rc0} \X {CONT_SEQ}) -> "ControllerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({ofc0, rc0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

(* Get instances of Zenith and the topology and create the `Next` predicate *)
Switch == INSTANCE switch
Zenith == INSTANCE zenith

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
        /\ \A self \in ({rc0} \X {CONT_SEQ}) : WF_internal_zenith_vars(Zenith!controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_internal_zenith_vars(Zenith!controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_internal_zenith_vars(Zenith!controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_internal_zenith_vars(Zenith!controllerMonitoringServer(self))
        /\ \A self \in ({ofc0, rc0} \X {WATCH_DOG}) : WF_internal_zenith_vars(Zenith!watchDog(self))

OperationsRanking == <<
    "ControllerSeqProc",
    "SchedulerMechanism",
    "SeqUpdateDBState1",
    "AddToScheduleIRSet",
    "ScheduleTheIR",
    "SeqClearDBState",
    "ControllerSeqStateReconciliation",
    "ControllerThread",
    "ControllerThreadSaveToDB1",
    "ControllerThreadLockTheIRUsingSemaphore",
    "ControllerThreadRemoveQueue1",
    "ControllerThreadSendIR",
    "ControllerThreadForwardIR",
    "ControllerThreadSaveToDB2",
    "WaitForIRToHaveCorrectStatus",
    "ReScheduleifIRNone",
    "ControllerThreadUnlockSemaphore",
    "RemoveFromScheduledIRSet",
    "ControllerThreadClearDB",
    "ControllerThreadRemoveQueue2",
    "ControllerThreadStateReconciliation",
    "ControllerEventHandlerProc",
    "ControllerSuspendSW",
    "ControllerEventHandlerSaveToDB1",
    "ControllerFreeSuspendedSW",
    "ControllerCheckIfThisIsLastEvent",
    "getIRsToBeChecked",
    "ResetAllIRs",
    "ControllerResetIRStatAfterRecovery",
    "ControllerEventHandlerClearDB",
    "ControllerEvenHanlderRemoveEventFromQueue",
    "ControllerEventHandlerStateReconciliation",
    "ControllerMonitorCheckIfMastr",
    "ControllerUpdateIR2",
    "MonitoringServerRemoveFromQueue",
    "ControllerWatchDogProc"
>>

OperationIndex(name) == CHOOSE x \in 1..Len(OperationsRanking): OperationsRanking[x] = name
                      
OperationsVariableSet == [
    ControllerSeqProc |-> {"IRStatus", "SwSuspensionStatus", "SetScheduledIRs", "idThreadWorkingOnIR"}, 
    SchedulerMechanism |-> {},
    SeqUpdateDBState1 |-> {},
    AddToScheduleIRSet |-> {"SetScheduledIRs"},
    ScheduleTheIR |-> {"controllerThreadPoolIRQueue"},
    SeqClearDBState |-> {},
    ControllerSeqStateReconciliation |-> {"SetScheduledIRs"},
    ControllerThread |-> {"controllerThreadPoolIRQueue"},
    ControllerThreadSaveToDB1 |-> {},
    ControllerThreadLockTheIRUsingSemaphore |-> {"idThreadWorkingOnIR"},
    ControllerThreadRemoveQueue1 |-> {"controllerThreadPoolIRQueue"},
    ControllerThreadSendIR |-> {"SwSuspensionStatus","IRStatus"},
    ControllerThreadForwardIR |-> {"controller2Switch"},
    ControllerThreadSaveToDB2 |-> {},
    WaitForIRToHaveCorrectStatus |-> {"SwSuspensionStatus"},
    ReScheduleifIRNone |-> {"IRStatus"},
    ControllerThreadUnlockSemaphore |-> {"idThreadWorkingOnIR"},
    RemoveFromScheduledIRSet |-> {"SetScheduledIRs"},
    ControllerThreadClearDB |-> {},
    ControllerThreadRemoveQueue2 |-> {"controllerThreadPoolIRQueue"},
    ControllerThreadStateReconciliation |-> {"IRStatus", "idThreadWorkingOnIR", "SetScheduledIRs"},
    ControllerEventHandlerProc |-> {"SwSuspensionStatus", "swSeqChangedStatus"},
    ControllerSuspendSW |-> {"SwSuspensionStatus"},
    ControllerEventHandlerSaveToDB1 |-> {},
    ControllerFreeSuspendedSW |-> {"SwSuspensionStatus"},
    ControllerCheckIfThisIsLastEvent |-> {"swSeqChangedStatus"},
    getIRsToBeChecked |-> {"IRStatus"},
    ResetAllIRs |-> {},
    ControllerResetIRStatAfterRecovery |-> {"IRStatus"},
    ControllerEventHandlerClearDB |-> {},
    ControllerEvenHanlderRemoveEventFromQueue |-> {"swSeqChangedStatus"},
    ControllerEventHandlerStateReconciliation |-> {"SwSuspensionStatus"},
    ControllerMonitorCheckIfMastr |-> {"switch2Controller"},
    ControllerUpdateIR2 |-> {"IRStatus"},
    MonitoringServerRemoveFromQueue |-> {"switch2Controller"},
    ControllerWatchDogProc |-> {"controllerStatus", "controllerLock"}
]

\* Liveness Properties
AllInstalled == (\A x \in 1..MaxNumIRs: \E y \in DOMAIN installedIRs: installedIRs[y] = x)
AllDoneStatusController == (\A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE)
InstallationLivenessProp == <>[] (/\ AllInstalled 
                                  /\ AllDoneStatusController)

\* Safety Properties
IRCriticalSection == 
    LET 
        IRCriticalSet == {
            "ControllerThreadSendIR", "ControllerThreadForwardIR", "ControllerThreadSaveToDB2", 
            "WaitForIRToHaveCorrectStatus", "ReScheduleifIRNone"
        }
    IN   
        \A x, y \in {ofc0} \X CONTROLLER_THREAD_POOL: 
            \/ x = y
            \/ <<pc[x], pc[y]>> \notin IRCriticalSet \X IRCriticalSet
            \/ /\ <<pc[x], pc[y]>> \in IRCriticalSet \X IRCriticalSet
               /\ nextIRToSent[x] # nextIRToSent[y]

RedundantInstallation == \A x \in 1..MaxNumIRs: \/ IRStatus[x] = IR_DONE
                                                \/ FirstInstall[x] = 0

firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})

ConsistencyReq == 
    \A x, y \in rangeSeq(installedIRs): 
        \/ x = y
        \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)
           /\ <<y, x>> \notin dependencyGraph
        \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
           /\ <<x, y>> \notin dependencyGraph

----
(* EVALUATION *)
----

CONSTANTS
s0, s1
----

CONSTANTS
t0
----

const_161337196895832000 == 
{s0, s1}
----

const_161337196895833000 == 
{t0}
----

const_161337196895834000 == 
<<>>
----

const_161337196895835000 == 
2
----

const_161337196895836000 == 
[ofc0 |-> 1, rc0 |-> 0]
----

const_161337196895837000 == 
(s0 :> SW_COMPLEX_MODEL) @@ (s1 :> SW_COMPLEX_MODEL)
----

const_161337196895838000 ==
[cpu |-> 1, nicAsic |-> 1, ofa |-> 1, installer |-> 1]
----

const_161337196895839000 ==
2
----

=============================================================================

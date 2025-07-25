---- MODULE evaluate_drain ----
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, NadirTypes

CONSTANTS core0
CONSTANTS CORE_SERVICER, CORE_HANDLER
CONSTANTS IR2SW, DAG, DAGID
CONSTANTS app0, DRAIN_APP

\* Shared between Zenith and the drain application
VARIABLES DAGEventQueue

\* Shared between Zenith and switches
VARIABLES switchLock, controllerLock, controller2Switch, switch2Controller

\* Program counter
VARIABLES pc

(* Internal variables, we'll not bother hiding them, since there is quite a few of them *)

\* For simple switch
VARIABLES installedIRs, sw_fail_ordering_var, SwProcSet, 
          switchStatus, TCAM, controlMsgCounter, RecoveryStatus,
          ingressPkt, statusMsg, obj, statusResolveMsg


\* For zenith
VARIABLES NIBIRStatus, FirstInstall, NIBEventQueue, 
          DAGState, SwSuspensionStatus, currentDAGObject, levels, 
          irListToSend, msg, irSetToReset

\* For drain application
VARIABLES DrainRequestQueue, currentRequest, currentTopology, currentPaths, nodeToDrain, 
          currentIRs, endpoints, pathsAfterDrain, drainPathSetIRs, drainedDAG, 
          nextDAGID

internal_switch_vars == <<
    installedIRs, sw_fail_ordering_var, SwProcSet, 
    switchStatus, installedIRs, TCAM, controlMsgCounter, RecoveryStatus,
    ingressPkt, statusMsg, obj, statusResolveMsg
>>

internal_zenith_vars == <<
    NIBEventQueue, DAGState, NIBIRStatus, FirstInstall,
    SwSuspensionStatus, currentDAGObject, levels, irListToSend, msg, 
    irSetToReset
>>

internal_drain_vars == <<
    DrainRequestQueue, currentRequest, currentTopology, currentPaths, nodeToDrain, 
    currentIRs, endpoints, pathsAfterDrain, drainPathSetIRs, drainedDAG, 
    nextDAGID
>>

\* When a switch takes a step, these do not change
nonswitch_vars == <<
    NIBIRStatus, FirstInstall, NIBEventQueue, 
    DAGState, SwSuspensionStatus, currentDAGObject, levels, 
    irListToSend, msg, irSetToReset,
    
    DrainRequestQueue, currentRequest, currentTopology, currentPaths, nodeToDrain, 
    currentIRs, endpoints, pathsAfterDrain, drainPathSetIRs, drainedDAG, 
    nextDAGID
>>
\* When Zenith takes a step, these do not change
nonzenith_vars == <<
    installedIRs, sw_fail_ordering_var, SwProcSet, 
    switchStatus, TCAM, controlMsgCounter, RecoveryStatus,
    ingressPkt, statusMsg, obj, statusResolveMsg,

    DrainRequestQueue, currentRequest, currentTopology, currentPaths, nodeToDrain, 
    currentIRs, endpoints, pathsAfterDrain, drainPathSetIRs, drainedDAG, 
    nextDAGID
>>
\* When drain app takes a step, these do not change
nondrain_vars == <<
    NIBIRStatus, FirstInstall, NIBEventQueue, 
    DAGState, SwSuspensionStatus, currentDAGObject, levels, 
    irListToSend, msg, irSetToReset,

    installedIRs, sw_fail_ordering_var, SwProcSet, 
    switchStatus, TCAM, controlMsgCounter, RecoveryStatus,
    ingressPkt, statusMsg, obj, statusResolveMsg
>>

ProcSet == 
    (* Switches *)
    (({SW_SIMPLE_ID} \X SW)) \cup 
    (({SW_FAILURE_PROC} \X SW)) \cup 
    (({SW_RESOLVE_PROC} \X SW)) \cup 
    (({GHOST_UNLOCK_PROC} \X SW)) \cup 
    (* Zenith *)
    (({core0} \X {CORE_SERVICER})) \cup 
    (({core0} \X {CORE_HANDLER})) \cup
    (* Drain app *)
    (({app0} \X {DRAIN_APP}))

Init == (* Global variables *)
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..2*MaxNumIRs |-> 0]
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ DAGEventQueue = <<>>
        /\ NIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ DrainRequestQueue = <<>>
        (* Process coreServicer *)
        /\ currentDAGObject = [self \in ({core0} \X {CORE_SERVICER}) |-> NADIR_NULL]
        /\ levels = [self \in ({core0} \X {CORE_SERVICER}) |-> NADIR_NULL]
        /\ irListToSend = [self \in ({core0} \X {CORE_SERVICER}) |-> NADIR_NULL]
        (* Process coreHandler *)
        /\ msg = [self \in ({core0} \X {CORE_HANDLER}) |-> NADIR_NULL]
        /\ irSetToReset = [self \in ({core0} \X {CORE_HANDLER}) |-> {}]
        (* Exposed switch variables *)
        /\ installedIRs = <<>>
        (* Hidden switch variables *)
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ SwProcSet = ((({SW_SIMPLE_ID} \X SW)) \cup
                        (({SW_FAILURE_PROC} \X SW)) \cup
                        (({SW_RESOLVE_PROC} \X SW)))
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
        (* Process swProcess *)
        /\ ingressPkt = [self \in ({SW_SIMPLE_ID} \X SW) |-> [type |-> 0]]
        (* Process swFailureProc *)
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> <<>>]
        /\ obj = [self \in ({SW_FAILURE_PROC} \X SW) |-> [type |-> 0]]
        (* Process swResolveFailure *)
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> <<>>]
        (* Process drainer *)
        /\ currentRequest = [self \in ({app0} \X {DRAIN_APP}) |-> NADIR_NULL]
        /\ currentTopology = [self \in ({app0} \X {DRAIN_APP}) |-> NADIR_NULL]
        /\ currentPaths = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ nodeToDrain = [self \in ({app0} \X {DRAIN_APP}) |-> NADIR_NULL]
        /\ currentIRs = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ endpoints = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ pathsAfterDrain = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ drainPathSetIRs = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ drainedDAG = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ nextDAGID = [self \in ({app0} \X {DRAIN_APP}) |-> 1]
        (* Program counter *)
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({core0} \X {CORE_SERVICER}) -> "CoreService"
                                        [] self \in ({core0} \X {CORE_HANDLER}) -> "CoreHandler"
                                        [] self \in ({app0} \X {DRAIN_APP}) |-> "DrainLoop"]

Switch == INSTANCE simple_switch
Zenith == INSTANCE AbstractCore
Drainer == INSTANCE drain

SwitchStep == /\ Switch!Next
              /\ UNCHANGED nonswitch_vars
servicerStep == /\ (\E self \in ({core0} \X {CORE_SERVICER}): Zenith!coreServicer(self))
                /\ UNCHANGED nonzenith_vars
handlerStep == /\ (\E self \in ({core0} \X {CORE_HANDLER}): Zenith!coreHandler(self))
               /\ UNCHANGED nonzenith_vars
DrainerStep == /\ Drainer!Next
               /\ UNCHANGED nondrain_vars

Next == \/ SwitchStep
        \/ servicerStep
        \/ handlerStep
        \/ DrainerStep

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_internal_switch_vars(Switch!swProcess(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_internal_switch_vars(Switch!swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_internal_switch_vars(Switch!swResolveFailure(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_internal_switch_vars(Switch!ghostUnlockProcess(self))
        /\ \A self \in ({core0} \X {CORE_SERVICER}) : WF_internal_zenith_vars(Zenith!coreServicer(self))
        /\ \A self \in ({core0} \X {CORE_SERVICER}) : WF_internal_zenith_vars(Zenith!coreHandler(self))
        /\ \A self \in ({app0} \X {DRAIN_APP}) : WF_internal_drain_vars(Drainer!drainer(self))
====
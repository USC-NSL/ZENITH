---- MODULE evaluate_AbstractCore ----
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, NadirTypes

CONSTANTS core0
CONSTANTS CORE_SERVICER, CORE_HANDLER
CONSTANTS IR2SW, DAG, DAGID


VARIABLES switchLock, controllerLock

VARIABLES controller2Switch, switch2Controller
VARIABLES installedIRs
VARIABLES NIBIRStatus, FirstInstall

VARIABLES pc

(* Internal variables, we'll not bother hiding them, since there is quite a few of them *)

\* For simple switch
VARIABLES sw_fail_ordering_var, SwProcSet, 
          switchStatus, TCAM, controlMsgCounter, RecoveryStatus,
          ingressPkt, statusMsg, obj, statusResolveMsg


\* For zenith
VARIABLES DAGEventQueue, NIBEventQueue, DAGState, 
          SwSuspensionStatus, currentDAGObject, levels, 
          irListToSend, msg, irSetToReset


----
(* EVALUATION *)
----

CONSTANTS
s0, s1
----

\* Consider a topology of 2 switches
const_SW == {s0, s1}
----

const_MaxNumIRs == 3
----

const_MaxDAGID == 15
----

\* Use the simple switch model
const_WHICH_SWITCH_MODEL == (s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

const_SW_MODULE_CAN_FAIL_OR_NOT == [cpu |-> 0, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

const_DAG == [v |-> {1, 2}, e |-> {<<1, 2>>}]
----

const_DAGID == 1
----

\* Where to install each IR?
const_IR2SW == (1 :> s0) @@ (2 :> s1) @@ (3 :> s1)
----

const_SW_FAIL_ORDERING == <<>>
----


shared_vars == <<switchLock, controllerLock, controller2Switch, switch2Controller>>

internal_switch_vars == <<
    sw_fail_ordering_var, SwProcSet, 
    switchStatus, installedIRs, TCAM, controlMsgCounter, RecoveryStatus,
    ingressPkt, statusMsg, obj, statusResolveMsg
>>

internal_zenith_vars == <<
    DAGEventQueue, NIBEventQueue, DAGState, NIBIRStatus, FirstInstall,
    SwSuspensionStatus, currentDAGObject, levels, irListToSend, msg, 
    irSetToReset, pc
>>

vars == <<
    switchLock, controllerLock, controller2Switch, switch2Controller,
    sw_fail_ordering_var, SwProcSet, 
    switchStatus, installedIRs, TCAM, controlMsgCounter, RecoveryStatus,
    ingressPkt, statusMsg, obj, statusResolveMsg,
    DAGEventQueue, NIBEventQueue, DAGState, NIBIRStatus, FirstInstall,
    SwSuspensionStatus, currentDAGObject, levels, irListToSend, msg, 
    irSetToReset, pc
>>

ProcSet == 
    (* Switches *)
    (({SW_SIMPLE_ID} \X SW)) \cup 
    (({SW_FAILURE_PROC} \X SW)) \cup 
    (({SW_RESOLVE_PROC} \X SW)) \cup 
    (({GHOST_UNLOCK_PROC} \X SW)) \cup 
    (* Zenith *)
    (({core0} \X {CORE_SERVICER})) \cup (({core0} \X {CORE_HANDLER}))

Init == (* Global variables *)
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..2*MaxNumIRs |-> 0]
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ DAGEventQueue = <<[id |-> DAGID, dag |-> DAG]>>
        /\ NIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
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
        (* Program counter *)
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({core0} \X {CORE_SERVICER}) -> "CoreService"
                                        [] self \in ({core0} \X {CORE_HANDLER}) -> "CoreHandler"]

Switch == INSTANCE simple_switch
Zenith == INSTANCE AbstractCore

SwitchStep == /\ Switch!Next
              /\ UNCHANGED internal_zenith_vars

servicerStep == /\ (\E self \in ({core0} \X {CORE_SERVICER}): Zenith!coreServicer(self))
                /\ UNCHANGED internal_switch_vars
handlerStep == /\ (\E self \in ({core0} \X {CORE_HANDLER}): Zenith!coreHandler(self))
               /\ UNCHANGED internal_switch_vars

Next == \/ SwitchStep
        \/ servicerStep
        \/ handlerStep

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_internal_switch_vars(Switch!swProcess(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_internal_switch_vars(Switch!swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_internal_switch_vars(Switch!swResolveFailure(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_internal_switch_vars(Switch!ghostUnlockProcess(self))
        /\ \A self \in ({core0} \X {CORE_SERVICER}) : WF_internal_zenith_vars(Zenith!coreServicer(self))
        /\ \A self \in ({core0} \X {CORE_SERVICER}) : WF_internal_zenith_vars(Zenith!coreHandler(self))

CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in DAG.v
                                                  /\ x \in TCAM[Zenith!getSwitchForIR(x)]
                                               \/ /\ x \notin DAG.v
                                                  /\ x \notin TCAM[Zenith!getSwitchForIR(x)])
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ NIBIRStatus[x].primary = IR_DONE
                                                       \/ x \notin DAG.v)
                                                       
InstallationLivenessProp == <>[] (/\ CorrectDAGInstalled 
                                  /\ CorrectDoneStatusController)
InstallationInvProp == \/ ENABLED Next
                       \/ /\ CorrectDAGInstalled
                          /\ CorrectDoneStatusController
\* Safety Properties
min(someSet) == CHOOSE x \in someSet: (\A y \in (someSet \ {x}): x \leq y)
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})

ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)                                                         
                                                         /\ <<Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)>> \notin DAG.e
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY)>> \notin DAG.e

====
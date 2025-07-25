------------------------ MODULE SwitchUnknownFailure ------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS sw1, sw2, sw3, sw4, Constroller, Drainer, tor1, tor2, SW_FAIL_UNKNOWN, SW_RUN,
          REBOOT, RB_NULL, RB_S, RB_F, DR_NULL, DR_S, DR_F, DR_SENT,
          IR_NONE, IR_SUCCEED, IR_SENT, IR_FAIL, RULE_MODIFICATION,
          RC_F, RC_S, RC_NULL
          
(* --algorithm SwitchUnknownFailure
variables 
    \* operation status: {SW_RUN, SW_FAIL, SW_FAIL_UNKNOWN, SW_UNREACHABLE}
    NONTOR_SW = {sw1, sw2, sw3, sw4},
    MaxNumIRs = 20,
    switchOperationStatus = [sw1 |-> SW_FAIL_UNKNOWN, sw3 |-> SW_FAIL_UNKNOWN, sw2 |-> SW_RUN, sw4 |-> SW_RUN], 
    \* RB_NULL (not applicable), RB_S (success), RB_F (fail)
    switchRebootStatus = [sw\in NONTOR_SW |-> RB_NULL], 
    \* DR_NULL, DR_S, DR_F
    switchDrainStatus = [sw\in NONTOR_SW |-> DR_NULL],
    \* NeighborSwitches mean data plane switches
    \* Hardcoded data plane topology
    topology = [sw1 |-> <<sw3, sw4>>, sw2 |-> <<sw3, sw4>>, sw3 |-> <<sw1, sw2, tor1, tor2>>, sw4 |-> <<sw1, sw2, tor1, tor2>>],
    \* Hardcoded dataplane switch failures 
    failUnknownSwitchSet = <<sw1, sw3>>,
    recoverStatus = RC_NULL,
    isFinished = FALSE,
    controller2Switch = [x\in NONTOR_SW |-> <<>>],
    drainer2Switch = [x\in NONTOR_SW |-> <<>>],
    drainRequestQueue = <<>>,
    lastUsedIRIndex = 1,
    IRStatus = [IR \in 1..MaxNumIRs |-> IR_NONE],

define 
    IsEmpty(S) == S = {}
    SwitchReachable(sw) == \/ switchOperationStatus[sw] =  SW_RUN 
                           \/ switchOperationStatus[sw] = SW_FAIL_UNKNOWN      
end define  

\* ------------------------------------------------------------------
\* -                   Controller Macros                            -
\* ------------------------------------------------------------------
macro RequestSwitchReboot() begin
    
end macro;

\* ------------------------------------------------------------------
\* -                   Switch Macros                                -
\* ------------------------------------------------------------------
macro HandleIR(switchID, IRID) begin
    print <<switchID, IRID, switchOperationStatus[switchID]>>;
    if switchOperationStatus[switchID] = SW_RUN then
        IRStatus[IRID] := IR_SUCCEED;
    elsif switchOperationStatus[switchID] = SW_FAIL_UNKNOWN then
        IRStatus[IRID] := IR_FAIL;
    else
        assert FALSE;
    end if;
end macro;

\* Naive reboot handling by just updating the switchRebootStatus 
\* TODO: Have two processes at switches. One is for reboot and another is for IR handling.
macro HandleReboot(switchID) begin
    switchRebootStatus[switchID] := RB_S;
end macro;

\* ------------------------------------------------------------------
\* -                   Drainer Procedures                           -
\* ------------------------------------------------------------------
procedure DrainSingleSwitch(switchToDrain) 
variables neighborSwitches = <<>>, 
          IRID = lastUsedIRIndex,
          nsw = ""
begin
GetNeighborSwitches:
    neighborSwitches := topology[switchToDrain];
DrainSingleSwitch: 
while Len(neighborSwitches) > 0 do
    \* use the local variable to store the IR ID to avoid getting changed by other threads
    IRID := lastUsedIRIndex;
    nsw := Head(neighborSwitches);
    IRStatus[IRID] := IR_SENT;
    controller2Switch[nsw] := Append(controller2Switch[nsw], [ChangeType |-> RULE_MODIFICATION,
                                                              switch |-> nsw,
                                                              IRIndex |-> IRID]);
    WaitSwitchACK:
        await IRStatus[IRID] /= IR_SENT;
    if IRStatus[IRID] /= IR_SUCCEED then
        switchDrainStatus[switchToDrain] := DR_F;
    end if;
    lastUsedIRIndex := lastUsedIRIndex + 1;
    neighborSwitches := Tail(neighborSwitches);
end while;
if switchDrainStatus[switchToDrain] = DR_NULL then
    switchDrainStatus[switchToDrain] := DR_S;
end if;
assert switchDrainStatus[switchToDrain] /= DR_NULL;
return;
end procedure;



\* ------------------------------------------------------------------
\* -                   Controller Procedures                        -
\* ------------------------------------------------------------------
\* Model the drain logic as part of the whole controller logic
procedure TryRebootSwitch(swToReboot) 
begin
TryRebootSingleSwitch:
assert /\ switchOperationStatus[swToReboot] = SW_FAIL_UNKNOWN
       /\ switchRebootStatus[swToReboot] = RB_NULL;
if switchDrainStatus[swToReboot] /= DR_S then
    \* Send the drain request
    drainRequestQueue := Append(drainRequestQueue, [drainRequestStatus |-> DR_SENT,
                                                        swID |-> swToReboot]);
    \* TODO: in current implementation, drainer has only one process
    \* And controller can only send one drain request and wait for ack.
    \* In the future we might want to extend this to multiprocesses.
    WaitDrainerACK:
        await Len(drainRequestQueue) = 0;
end if;
UpdateRebootStatus:
if switchDrainStatus[swToReboot] = DR_F then
    switchRebootStatus[swToReboot] := RB_F;
else
    controller2Switch[swToReboot] := Append(controller2Switch[swToReboot], [ChangeType |-> REBOOT,
                                                              switch |-> swToReboot,
                                                              IRIndex |-> 0]);
    \* Assumption here: as long as drain is successful, we can always reboot the switch successfully.
    \* TODO: maybe remove this assumption in the future                                                          
    WaitSwitchACK:
        await switchRebootStatus[swToReboot] = RB_S;
end if;
Return:
return;
end procedure;


\* ==========Controller Processes ===========
\* Given the failUnknownSwitchSet, the controller try to recover failures through rebooting switches.
\* Rebooting switches sequentially
fair process controller = "Controller"
variables fail_unknown_switch = 0
begin
SwitchUnknownFailRecovery:
while Len(failUnknownSwitchSet) > 0 do
    fail_unknown_switch := Head(failUnknownSwitchSet);
    if SwitchReachable(fail_unknown_switch) then
        call TryRebootSwitch(fail_unknown_switch);
        \* Assume the controller always knows the switch state (even if via timeout) 
        WaitForRebooterACK:
            await switchRebootStatus[fail_unknown_switch] /= RB_NULL;
    end if;
    UpdateFailUnknownSwitchSet:
    if switchRebootStatus[fail_unknown_switch] = RB_S then
        failUnknownSwitchSet := Tail(failUnknownSwitchSet);
    elsif switchRebootStatus[fail_unknown_switch] = RB_F then
        recoverStatus := RC_F;
        goto RecoveryResults;
    else
        assert switchRebootStatus[fail_unknown_switch] /= RB_NULL;
    end if;
end while;
RecoveryResults:
if recoverStatus /= RC_F then
    recoverStatus := RC_S;
end if;  
isFinished := TRUE; 
print recoverStatus;
end process
\* ======================================
 
\* ==========Drainer Processes ===========   
\* Drainer will drain switches sequentially
\* TODO: how to conduct concurrent draining safely?
fair process sequentialDrain = "SequentialDrainer"
variables drainReq = [drainRequestStatus |-> ""]
begin
SeqDrain:
while ~isFinished do
    await Len(drainRequestQueue) > 0;
    drainReq := Head(drainRequestQueue);
    call DrainSingleSwitch(drainReq.swID);
    WaitForSwitchACK:
    await switchDrainStatus[drainReq.swID] /= DR_NULL;
    drainRequestQueue := Tail(drainRequestQueue);
end while;
end process
 \* ======================================
 
 \* ==========Switch Module ===========
fair process switchPC \in NONTOR_SW
variables change = [type |-> 0]
begin    
\*SwitchReachableOrNot:
\*    await SwitchReachable(self);
SwitchIsReachable:
    while ~isFinished /\ SwitchReachable(self) do
        await Len(controller2Switch[self]) > 0;
        change := Head(controller2Switch[self]);   
        if change.ChangeType = RULE_MODIFICATION then
            HandleIR(self, change.IRIndex);
        elsif change.ChangeType = REBOOT then
            HandleReboot(self);
        end if;
        controller2Switch[self] := Tail(controller2Switch[self]);   
    end while;
end process
\* ======================================
 end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-8b91e4ff0c073de2d59c79316bc3f273
\* Label DrainSingleSwitch of procedure DrainSingleSwitch at line 75 col 1 changed to DrainSingleSwitch_
\* Label WaitSwitchACK of procedure DrainSingleSwitch at line 84 col 9 changed to WaitSwitchACK_
CONSTANT defaultInitValue
VARIABLES NONTOR_SW, MaxNumIRs, switchOperationStatus, switchRebootStatus, 
          switchDrainStatus, topology, failUnknownSwitchSet, recoverStatus, 
          isFinished, controller2Switch, drainer2Switch, drainRequestQueue, 
          lastUsedIRIndex, IRStatus, pc, stack

(* define statement *)
IsEmpty(S) == S = {}
SwitchReachable(sw) == \/ switchOperationStatus[sw] =  SW_RUN
                       \/ switchOperationStatus[sw] = SW_FAIL_UNKNOWN

VARIABLES switchToDrain, neighborSwitches, IRID, nsw, swToReboot, 
          fail_unknown_switch, drainReq, change

vars == << NONTOR_SW, MaxNumIRs, switchOperationStatus, switchRebootStatus, 
           switchDrainStatus, topology, failUnknownSwitchSet, recoverStatus, 
           isFinished, controller2Switch, drainer2Switch, drainRequestQueue, 
           lastUsedIRIndex, IRStatus, pc, stack, switchToDrain, 
           neighborSwitches, IRID, nsw, swToReboot, fail_unknown_switch, 
           drainReq, change >>

ProcSet == {"Controller"} \cup {"SequentialDrainer"} \cup (NONTOR_SW)

Init == (* Global variables *)
        /\ NONTOR_SW = {sw1, sw2, sw3, sw4}
        /\ MaxNumIRs = 20
        /\ switchOperationStatus = [sw1 |-> SW_FAIL_UNKNOWN, sw3 |-> SW_FAIL_UNKNOWN, sw2 |-> SW_RUN, sw4 |-> SW_RUN]
        /\ switchRebootStatus = [sw\in NONTOR_SW |-> RB_NULL]
        /\ switchDrainStatus = [sw\in NONTOR_SW |-> DR_NULL]
        /\ topology = [sw1 |-> <<sw3, sw4>>, sw2 |-> <<sw3, sw4>>, sw3 |-> <<sw1, sw2, tor1, tor2>>, sw4 |-> <<sw1, sw2, tor1, tor2>>]
        /\ failUnknownSwitchSet = <<sw1, sw3>>
        /\ recoverStatus = RC_NULL
        /\ isFinished = FALSE
        /\ controller2Switch = [x\in NONTOR_SW |-> <<>>]
        /\ drainer2Switch = [x\in NONTOR_SW |-> <<>>]
        /\ drainRequestQueue = <<>>
        /\ lastUsedIRIndex = 1
        /\ IRStatus = [IR \in 1..MaxNumIRs |-> IR_NONE]
        (* Procedure DrainSingleSwitch *)
        /\ switchToDrain = [ self \in ProcSet |-> defaultInitValue]
        /\ neighborSwitches = [ self \in ProcSet |-> <<>>]
        /\ IRID = [ self \in ProcSet |-> lastUsedIRIndex]
        /\ nsw = [ self \in ProcSet |-> ""]
        (* Procedure TryRebootSwitch *)
        /\ swToReboot = [ self \in ProcSet |-> defaultInitValue]
        (* Process controller *)
        /\ fail_unknown_switch = 0
        (* Process sequentialDrain *)
        /\ drainReq = [drainRequestStatus |-> ""]
        (* Process switchPC *)
        /\ change = [self \in NONTOR_SW |-> [type |-> 0]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "Controller" -> "SwitchUnknownFailRecovery"
                                        [] self = "SequentialDrainer" -> "SeqDrain"
                                        [] self \in NONTOR_SW -> "SwitchIsReachable"]

GetNeighborSwitches(self) == /\ pc[self] = "GetNeighborSwitches"
                             /\ neighborSwitches' = [neighborSwitches EXCEPT ![self] = topology[switchToDrain[self]]]
                             /\ pc' = [pc EXCEPT ![self] = "DrainSingleSwitch_"]
                             /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                             switchOperationStatus, 
                                             switchRebootStatus, 
                                             switchDrainStatus, topology, 
                                             failUnknownSwitchSet, 
                                             recoverStatus, isFinished, 
                                             controller2Switch, drainer2Switch, 
                                             drainRequestQueue, 
                                             lastUsedIRIndex, IRStatus, stack, 
                                             switchToDrain, IRID, nsw, 
                                             swToReboot, fail_unknown_switch, 
                                             drainReq, change >>

DrainSingleSwitch_(self) == /\ pc[self] = "DrainSingleSwitch_"
                            /\ IF Len(neighborSwitches[self]) > 0
                                  THEN /\ IRID' = [IRID EXCEPT ![self] = lastUsedIRIndex]
                                       /\ nsw' = [nsw EXCEPT ![self] = Head(neighborSwitches[self])]
                                       /\ IRStatus' = [IRStatus EXCEPT ![IRID'[self]] = IR_SENT]
                                       /\ controller2Switch' = [controller2Switch EXCEPT ![nsw'[self]] = Append(controller2Switch[nsw'[self]], [ChangeType |-> RULE_MODIFICATION,
                                                                                                                                                switch |-> nsw'[self],
                                                                                                                                                IRIndex |-> IRID'[self]])]
                                       /\ pc' = [pc EXCEPT ![self] = "WaitSwitchACK_"]
                                       /\ UNCHANGED << switchDrainStatus, 
                                                       stack, switchToDrain, 
                                                       neighborSwitches >>
                                  ELSE /\ IF switchDrainStatus[switchToDrain[self]] = DR_NULL
                                             THEN /\ switchDrainStatus' = [switchDrainStatus EXCEPT ![switchToDrain[self]] = DR_S]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED switchDrainStatus
                                       /\ Assert(switchDrainStatus'[switchToDrain[self]] /= DR_NULL, 
                                                 "Failure of assertion at line 94, column 1.")
                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ neighborSwitches' = [neighborSwitches EXCEPT ![self] = Head(stack[self]).neighborSwitches]
                                       /\ IRID' = [IRID EXCEPT ![self] = Head(stack[self]).IRID]
                                       /\ nsw' = [nsw EXCEPT ![self] = Head(stack[self]).nsw]
                                       /\ switchToDrain' = [switchToDrain EXCEPT ![self] = Head(stack[self]).switchToDrain]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED << controller2Switch, 
                                                       IRStatus >>
                            /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                            switchOperationStatus, 
                                            switchRebootStatus, topology, 
                                            failUnknownSwitchSet, 
                                            recoverStatus, isFinished, 
                                            drainer2Switch, drainRequestQueue, 
                                            lastUsedIRIndex, swToReboot, 
                                            fail_unknown_switch, drainReq, 
                                            change >>

WaitSwitchACK_(self) == /\ pc[self] = "WaitSwitchACK_"
                        /\ IRStatus[IRID[self]] /= IR_SENT
                        /\ IF IRStatus[IRID[self]] /= IR_SUCCEED
                              THEN /\ switchDrainStatus' = [switchDrainStatus EXCEPT ![switchToDrain[self]] = DR_F]
                              ELSE /\ TRUE
                                   /\ UNCHANGED switchDrainStatus
                        /\ lastUsedIRIndex' = lastUsedIRIndex + 1
                        /\ neighborSwitches' = [neighborSwitches EXCEPT ![self] = Tail(neighborSwitches[self])]
                        /\ pc' = [pc EXCEPT ![self] = "DrainSingleSwitch_"]
                        /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                        switchOperationStatus, 
                                        switchRebootStatus, topology, 
                                        failUnknownSwitchSet, recoverStatus, 
                                        isFinished, controller2Switch, 
                                        drainer2Switch, drainRequestQueue, 
                                        IRStatus, stack, switchToDrain, IRID, 
                                        nsw, swToReboot, fail_unknown_switch, 
                                        drainReq, change >>

DrainSingleSwitch(self) == GetNeighborSwitches(self)
                              \/ DrainSingleSwitch_(self)
                              \/ WaitSwitchACK_(self)

TryRebootSingleSwitch(self) == /\ pc[self] = "TryRebootSingleSwitch"
                               /\ Assert(/\ switchOperationStatus[swToReboot[self]] = SW_FAIL_UNKNOWN
                                         /\ switchRebootStatus[swToReboot[self]] = RB_NULL, 
                                         "Failure of assertion at line 107, column 1.")
                               /\ IF switchDrainStatus[swToReboot[self]] /= DR_S
                                     THEN /\ drainRequestQueue' = Append(drainRequestQueue, [drainRequestStatus |-> DR_SENT,
                                                                                                 swID |-> swToReboot[self]])
                                          /\ pc' = [pc EXCEPT ![self] = "WaitDrainerACK"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateRebootStatus"]
                                          /\ UNCHANGED drainRequestQueue
                               /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                               switchOperationStatus, 
                                               switchRebootStatus, 
                                               switchDrainStatus, topology, 
                                               failUnknownSwitchSet, 
                                               recoverStatus, isFinished, 
                                               controller2Switch, 
                                               drainer2Switch, lastUsedIRIndex, 
                                               IRStatus, stack, switchToDrain, 
                                               neighborSwitches, IRID, nsw, 
                                               swToReboot, fail_unknown_switch, 
                                               drainReq, change >>

WaitDrainerACK(self) == /\ pc[self] = "WaitDrainerACK"
                        /\ Len(drainRequestQueue) = 0
                        /\ pc' = [pc EXCEPT ![self] = "UpdateRebootStatus"]
                        /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                        switchOperationStatus, 
                                        switchRebootStatus, switchDrainStatus, 
                                        topology, failUnknownSwitchSet, 
                                        recoverStatus, isFinished, 
                                        controller2Switch, drainer2Switch, 
                                        drainRequestQueue, lastUsedIRIndex, 
                                        IRStatus, stack, switchToDrain, 
                                        neighborSwitches, IRID, nsw, 
                                        swToReboot, fail_unknown_switch, 
                                        drainReq, change >>

UpdateRebootStatus(self) == /\ pc[self] = "UpdateRebootStatus"
                            /\ IF switchDrainStatus[swToReboot[self]] = DR_F
                                  THEN /\ switchRebootStatus' = [switchRebootStatus EXCEPT ![swToReboot[self]] = RB_F]
                                       /\ pc' = [pc EXCEPT ![self] = "Return"]
                                       /\ UNCHANGED controller2Switch
                                  ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![swToReboot[self]] = Append(controller2Switch[swToReboot[self]], [ChangeType |-> REBOOT,
                                                                                                                                        switch |-> swToReboot[self],
                                                                                                                                        IRIndex |-> 0])]
                                       /\ pc' = [pc EXCEPT ![self] = "WaitSwitchACK"]
                                       /\ UNCHANGED switchRebootStatus
                            /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                            switchOperationStatus, 
                                            switchDrainStatus, topology, 
                                            failUnknownSwitchSet, 
                                            recoverStatus, isFinished, 
                                            drainer2Switch, drainRequestQueue, 
                                            lastUsedIRIndex, IRStatus, stack, 
                                            switchToDrain, neighborSwitches, 
                                            IRID, nsw, swToReboot, 
                                            fail_unknown_switch, drainReq, 
                                            change >>

WaitSwitchACK(self) == /\ pc[self] = "WaitSwitchACK"
                       /\ switchRebootStatus[swToReboot[self]] = RB_S
                       /\ pc' = [pc EXCEPT ![self] = "Return"]
                       /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                       switchOperationStatus, 
                                       switchRebootStatus, switchDrainStatus, 
                                       topology, failUnknownSwitchSet, 
                                       recoverStatus, isFinished, 
                                       controller2Switch, drainer2Switch, 
                                       drainRequestQueue, lastUsedIRIndex, 
                                       IRStatus, stack, switchToDrain, 
                                       neighborSwitches, IRID, nsw, swToReboot, 
                                       fail_unknown_switch, drainReq, change >>

Return(self) == /\ pc[self] = "Return"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ swToReboot' = [swToReboot EXCEPT ![self] = Head(stack[self]).swToReboot]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << NONTOR_SW, MaxNumIRs, switchOperationStatus, 
                                switchRebootStatus, switchDrainStatus, 
                                topology, failUnknownSwitchSet, recoverStatus, 
                                isFinished, controller2Switch, drainer2Switch, 
                                drainRequestQueue, lastUsedIRIndex, IRStatus, 
                                switchToDrain, neighborSwitches, IRID, nsw, 
                                fail_unknown_switch, drainReq, change >>

TryRebootSwitch(self) == TryRebootSingleSwitch(self)
                            \/ WaitDrainerACK(self)
                            \/ UpdateRebootStatus(self)
                            \/ WaitSwitchACK(self) \/ Return(self)

SwitchUnknownFailRecovery == /\ pc["Controller"] = "SwitchUnknownFailRecovery"
                             /\ IF Len(failUnknownSwitchSet) > 0
                                   THEN /\ fail_unknown_switch' = Head(failUnknownSwitchSet)
                                        /\ IF SwitchReachable(fail_unknown_switch')
                                              THEN /\ /\ stack' = [stack EXCEPT !["Controller"] = << [ procedure |->  "TryRebootSwitch",
                                                                                                       pc        |->  "WaitForRebooterACK",
                                                                                                       swToReboot |->  swToReboot["Controller"] ] >>
                                                                                                   \o stack["Controller"]]
                                                      /\ swToReboot' = [swToReboot EXCEPT !["Controller"] = fail_unknown_switch']
                                                   /\ pc' = [pc EXCEPT !["Controller"] = "TryRebootSingleSwitch"]
                                              ELSE /\ pc' = [pc EXCEPT !["Controller"] = "UpdateFailUnknownSwitchSet"]
                                                   /\ UNCHANGED << stack, 
                                                                   swToReboot >>
                                   ELSE /\ pc' = [pc EXCEPT !["Controller"] = "RecoveryResults"]
                                        /\ UNCHANGED << stack, swToReboot, 
                                                        fail_unknown_switch >>
                             /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                             switchOperationStatus, 
                                             switchRebootStatus, 
                                             switchDrainStatus, topology, 
                                             failUnknownSwitchSet, 
                                             recoverStatus, isFinished, 
                                             controller2Switch, drainer2Switch, 
                                             drainRequestQueue, 
                                             lastUsedIRIndex, IRStatus, 
                                             switchToDrain, neighborSwitches, 
                                             IRID, nsw, drainReq, change >>

UpdateFailUnknownSwitchSet == /\ pc["Controller"] = "UpdateFailUnknownSwitchSet"
                              /\ IF switchRebootStatus[fail_unknown_switch] = RB_S
                                    THEN /\ failUnknownSwitchSet' = Tail(failUnknownSwitchSet)
                                         /\ pc' = [pc EXCEPT !["Controller"] = "SwitchUnknownFailRecovery"]
                                         /\ UNCHANGED recoverStatus
                                    ELSE /\ IF switchRebootStatus[fail_unknown_switch] = RB_F
                                               THEN /\ recoverStatus' = RC_F
                                                    /\ pc' = [pc EXCEPT !["Controller"] = "RecoveryResults"]
                                               ELSE /\ Assert(switchRebootStatus[fail_unknown_switch] /= RB_NULL, 
                                                              "Failure of assertion at line 158, column 9.")
                                                    /\ pc' = [pc EXCEPT !["Controller"] = "SwitchUnknownFailRecovery"]
                                                    /\ UNCHANGED recoverStatus
                                         /\ UNCHANGED failUnknownSwitchSet
                              /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                              switchOperationStatus, 
                                              switchRebootStatus, 
                                              switchDrainStatus, topology, 
                                              isFinished, controller2Switch, 
                                              drainer2Switch, 
                                              drainRequestQueue, 
                                              lastUsedIRIndex, IRStatus, stack, 
                                              switchToDrain, neighborSwitches, 
                                              IRID, nsw, swToReboot, 
                                              fail_unknown_switch, drainReq, 
                                              change >>

WaitForRebooterACK == /\ pc["Controller"] = "WaitForRebooterACK"
                      /\ switchRebootStatus[fail_unknown_switch] /= RB_NULL
                      /\ pc' = [pc EXCEPT !["Controller"] = "UpdateFailUnknownSwitchSet"]
                      /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                      switchOperationStatus, 
                                      switchRebootStatus, switchDrainStatus, 
                                      topology, failUnknownSwitchSet, 
                                      recoverStatus, isFinished, 
                                      controller2Switch, drainer2Switch, 
                                      drainRequestQueue, lastUsedIRIndex, 
                                      IRStatus, stack, switchToDrain, 
                                      neighborSwitches, IRID, nsw, swToReboot, 
                                      fail_unknown_switch, drainReq, change >>

RecoveryResults == /\ pc["Controller"] = "RecoveryResults"
                   /\ IF recoverStatus /= RC_F
                         THEN /\ recoverStatus' = RC_S
                         ELSE /\ TRUE
                              /\ UNCHANGED recoverStatus
                   /\ isFinished' = TRUE
                   /\ PrintT(recoverStatus')
                   /\ pc' = [pc EXCEPT !["Controller"] = "Done"]
                   /\ UNCHANGED << NONTOR_SW, MaxNumIRs, switchOperationStatus, 
                                   switchRebootStatus, switchDrainStatus, 
                                   topology, failUnknownSwitchSet, 
                                   controller2Switch, drainer2Switch, 
                                   drainRequestQueue, lastUsedIRIndex, 
                                   IRStatus, stack, switchToDrain, 
                                   neighborSwitches, IRID, nsw, swToReboot, 
                                   fail_unknown_switch, drainReq, change >>

controller == SwitchUnknownFailRecovery \/ UpdateFailUnknownSwitchSet
                 \/ WaitForRebooterACK \/ RecoveryResults

SeqDrain == /\ pc["SequentialDrainer"] = "SeqDrain"
            /\ IF ~isFinished
                  THEN /\ Len(drainRequestQueue) > 0
                       /\ drainReq' = Head(drainRequestQueue)
                       /\ /\ stack' = [stack EXCEPT !["SequentialDrainer"] = << [ procedure |->  "DrainSingleSwitch",
                                                                                  pc        |->  "WaitForSwitchACK",
                                                                                  neighborSwitches |->  neighborSwitches["SequentialDrainer"],
                                                                                  IRID      |->  IRID["SequentialDrainer"],
                                                                                  nsw       |->  nsw["SequentialDrainer"],
                                                                                  switchToDrain |->  switchToDrain["SequentialDrainer"] ] >>
                                                                              \o stack["SequentialDrainer"]]
                          /\ switchToDrain' = [switchToDrain EXCEPT !["SequentialDrainer"] = drainReq'.swID]
                       /\ neighborSwitches' = [neighborSwitches EXCEPT !["SequentialDrainer"] = <<>>]
                       /\ IRID' = [IRID EXCEPT !["SequentialDrainer"] = lastUsedIRIndex]
                       /\ nsw' = [nsw EXCEPT !["SequentialDrainer"] = ""]
                       /\ pc' = [pc EXCEPT !["SequentialDrainer"] = "GetNeighborSwitches"]
                  ELSE /\ pc' = [pc EXCEPT !["SequentialDrainer"] = "Done"]
                       /\ UNCHANGED << stack, switchToDrain, neighborSwitches, 
                                       IRID, nsw, drainReq >>
            /\ UNCHANGED << NONTOR_SW, MaxNumIRs, switchOperationStatus, 
                            switchRebootStatus, switchDrainStatus, topology, 
                            failUnknownSwitchSet, recoverStatus, isFinished, 
                            controller2Switch, drainer2Switch, 
                            drainRequestQueue, lastUsedIRIndex, IRStatus, 
                            swToReboot, fail_unknown_switch, change >>

WaitForSwitchACK == /\ pc["SequentialDrainer"] = "WaitForSwitchACK"
                    /\ switchDrainStatus[drainReq.swID] /= DR_NULL
                    /\ drainRequestQueue' = Tail(drainRequestQueue)
                    /\ pc' = [pc EXCEPT !["SequentialDrainer"] = "SeqDrain"]
                    /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                    switchOperationStatus, switchRebootStatus, 
                                    switchDrainStatus, topology, 
                                    failUnknownSwitchSet, recoverStatus, 
                                    isFinished, controller2Switch, 
                                    drainer2Switch, lastUsedIRIndex, IRStatus, 
                                    stack, switchToDrain, neighborSwitches, 
                                    IRID, nsw, swToReboot, fail_unknown_switch, 
                                    drainReq, change >>

sequentialDrain == SeqDrain \/ WaitForSwitchACK

SwitchIsReachable(self) == /\ pc[self] = "SwitchIsReachable"
                           /\ IF ~isFinished /\ SwitchReachable(self)
                                 THEN /\ Len(controller2Switch[self]) > 0
                                      /\ change' = [change EXCEPT ![self] = Head(controller2Switch[self])]
                                      /\ IF change'[self].ChangeType = RULE_MODIFICATION
                                            THEN /\ PrintT(<<self, (change'[self].IRIndex), switchOperationStatus[self]>>)
                                                 /\ IF switchOperationStatus[self] = SW_RUN
                                                       THEN /\ IRStatus' = [IRStatus EXCEPT ![(change'[self].IRIndex)] = IR_SUCCEED]
                                                       ELSE /\ IF switchOperationStatus[self] = SW_FAIL_UNKNOWN
                                                                  THEN /\ IRStatus' = [IRStatus EXCEPT ![(change'[self].IRIndex)] = IR_FAIL]
                                                                  ELSE /\ Assert(FALSE, 
                                                                                 "Failure of assertion at line 54, column 9 of macro called at line 199, column 13.")
                                                                       /\ UNCHANGED IRStatus
                                                 /\ UNCHANGED switchRebootStatus
                                            ELSE /\ IF change'[self].ChangeType = REBOOT
                                                       THEN /\ switchRebootStatus' = [switchRebootStatus EXCEPT ![self] = RB_S]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED switchRebootStatus
                                                 /\ UNCHANGED IRStatus
                                      /\ controller2Switch' = [controller2Switch EXCEPT ![self] = Tail(controller2Switch[self])]
                                      /\ pc' = [pc EXCEPT ![self] = "SwitchIsReachable"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                      /\ UNCHANGED << switchRebootStatus, 
                                                      controller2Switch, 
                                                      IRStatus, change >>
                           /\ UNCHANGED << NONTOR_SW, MaxNumIRs, 
                                           switchOperationStatus, 
                                           switchDrainStatus, topology, 
                                           failUnknownSwitchSet, recoverStatus, 
                                           isFinished, drainer2Switch, 
                                           drainRequestQueue, lastUsedIRIndex, 
                                           stack, switchToDrain, 
                                           neighborSwitches, IRID, nsw, 
                                           swToReboot, fail_unknown_switch, 
                                           drainReq >>

switchPC(self) == SwitchIsReachable(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == controller \/ sequentialDrain
           \/ (\E self \in ProcSet:  \/ DrainSingleSwitch(self)
                                     \/ TryRebootSwitch(self))
           \/ (\E self \in NONTOR_SW: switchPC(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(controller) /\ WF_vars(TryRebootSwitch("Controller"))
        /\ /\ WF_vars(sequentialDrain)
           /\ WF_vars(DrainSingleSwitch("SequentialDrainer"))
        /\ \A self \in NONTOR_SW : WF_vars(switchPC(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-68114f19a70abd408a7db3d1aa8b2de8
RecoverySucceed == recoverStatus /= RC_F
=============================================================================
\* Modification History
\* Last modified Mon Sep 14 22:58:36 PDT 2020 by zmy
\* Created Sat Sep 12 17:09:27 PDT 2020 by zmy

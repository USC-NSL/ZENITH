---------------------------- MODULE DrainDeadlockAtOFCDownstream ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS NONTOR_SW, sw1, sw2, sw3, sw4, tor1, tor2, SW_RUN, SW_FAIL_UNKNOWN, SW_FAIL,
          DR_UNDRAINED, DR_DRAINED, DR_UNKNOWN, DR_SUCCESS, 
          IR_READY, IR_SENT, IR_DONE, IR_NONE,
          NUM_CONCURRENT_SW_FAILURES,
          Switch, OFCSwitchConnection, Drainer, RoutingController, OFC

(*--fair algorithm drain
variables 
          \* Hardcoded data plane topology
          topology = [sw1 |-> {sw3, sw4}, sw2 |-> {sw3, sw4}, sw3 |-> {sw1, sw2}, sw4 |-> {sw1, sw2}],
          \* other states
          finalDrainStatus = DR_UNKNOWN,
          lastUsedIRIndex = 1,
          \* -----------------states in RC (routing controller)--------------------- \*
          switchOperationStatusRCNIB = [x \in NONTOR_SW |-> SW_RUN],
          switchDrainStatusRCNIB = [x \in NONTOR_SW |-> DR_UNDRAINED],
          switchTargetDrainStatusRCNIB = [x \in NONTOR_SW |-> DR_UNDRAINED],
          switchesToBeDrained = {}, \* exclusive to RC
          switchesToBeUpdated = {}, \* exclusive to RC
          switchIRStatusRCNIB = [x \in NONTOR_SW |-> <<-1, IR_NONE>>], \* IR stutus in RC NIB, \* key: sw, value: <<IRID, status>>
          
          \* -----------------states in DR (Drainer)--------------------------------- \*
          switchDrainStatusDRNIB = [x \in NONTOR_SW |-> DR_UNDRAINED],
          switchTargetDrainStatusDRNIB = [sw1 |-> DR_DRAINED, sw2 |-> DR_UNDRAINED, sw3 |-> DR_DRAINED, sw4 |-> DR_UNDRAINED],
          \* -----------------states in OFC------------------------------------- \*
          switchOperationStatusOFC = [x \in NONTOR_SW |-> SW_RUN],
          \* -----------------states in switches------------------------------------- \*
          switchIRStatusTCAM = [x \in NONTOR_SW |-> <<-1, IR_NONE>>],
          \* -----------------global states ------------------------------------- \*
          isFinished = FALSE,
          nonFirstStep = FALSE
          
          
define 
    \* Compare target status and current status in drainer NIB
    FindSwitchedToBeDrainedDRNIB == {sw \in NONTOR_SW: switchDrainStatusDRNIB[sw] # switchTargetDrainStatusDRNIB[sw]}
    \* Compare target status and current status in RC NIB
    FindSwitchedToBeDrainedRCNIB == {sw \in NONTOR_SW: switchDrainStatusRCNIB[sw] # switchTargetDrainStatusRCNIB[sw]}  
    ReadyIRSetInRC == {sw \in NONTOR_SW: switchIRStatusRCNIB[sw][2] = IR_READY} 
    DoneIRSetInSwitch == {sw \in NONTOR_SW: switchIRStatusTCAM[sw][2] = IR_DONE} 
    IsAllIRDoneRCNIB(swSet) == /\ Cardinality(swSet) > 0
                               /\ \A sw \in swSet: switchIRStatusRCNIB[sw][2] = IR_DONE
                                
    DoneIRSetInRCNIB == {sw \in switchesToBeUpdated: switchIRStatusRCNIB[sw][2] = IR_DONE}
    SwitchReachable(sw) == \/ switchOperationStatusOFC[sw] =  SW_RUN 
                           \/ switchOperationStatusOFC[sw] = SW_FAIL_UNKNOWN   
end define

\* ==========Drainer Module ===========
\* single process for sequencer
\* ====================================
fair process drainer \in ({"drainer"} \X {Drainer})
begin
\* 1. Receive drain request, 2. Consult a sequencer (omit here)
\* 3. update switchTargetDrainStatusRCNIB in RC atomically
ProcessDRRequestAndSendToRC:
    await Cardinality(FindSwitchedToBeDrainedDRNIB) > 0;
\*    nonFirstStep := TRUE;
    \* Drainer writes drain target status to RC NIB 
    switchTargetDrainStatusRCNIB := switchTargetDrainStatusDRNIB;
\* Process drain results from RC
WaitRCACK:
    \* RC NIB notifies the drainer
    await Cardinality(FindSwitchedToBeDrainedRCNIB) = 0;
    switchDrainStatusDRNIB := switchTargetDrainStatusDRNIB;
    finalDrainStatus := DR_SUCCESS;
    isFinished := TRUE;
    print <<finalDrainStatus>>;
end process

\* ==========Routing controller Module ===========
\* downstream
\* ===============================================
fair process routingControllerDownstream \in ({"RCDownstream"} \X {RoutingController})
variables swToBeDrained, swToBeUpdated, switchesToBeDrainedLocal, switchesToBeUpdatedLocal;
begin
\* Drainer NIB notify RC about which switches to drain
ProcessDRRequestAndSendToSwitches:
    await Cardinality(FindSwitchedToBeDrainedRCNIB) > 0;
    switchesToBeDrained := FindSwitchedToBeDrainedRCNIB;
    switchesToBeDrainedLocal := switchesToBeDrained;
\* Find neighbor switches and put them into the NIB table, switchesToBeUpdated
FindNeighbors:
    while Cardinality(switchesToBeDrainedLocal) > 0 do
        \* Put neighbor switches into switchesToBeUpdated
        swToBeDrained := CHOOSE sw \in switchesToBeDrainedLocal: TRUE;
        switchesToBeUpdated := switchesToBeUpdated \union topology[swToBeDrained];
        switchesToBeDrainedLocal := switchesToBeDrainedLocal\{swToBeDrained}
    end while;
    switchesToBeUpdated := switchesToBeUpdated \ switchesToBeDrained;
    switchesToBeUpdatedLocal := switchesToBeUpdated;
\* Write IRs into the RC NIB
\* Assumption: generate a single IR for each switch 
GenerateIRs:
    while Cardinality(switchesToBeUpdatedLocal) > 0 do
        swToBeUpdated := CHOOSE sw \in switchesToBeUpdatedLocal: TRUE;
        switchIRStatusRCNIB[swToBeUpdated] := <<lastUsedIRIndex + 1, IR_READY>>;
        switchesToBeUpdatedLocal := switchesToBeUpdatedLocal\{swToBeUpdated};
        lastUsedIRIndex := lastUsedIRIndex + 1;
    end while;
end process

\* ==========Routing controller Module ===========
\* upstream: 
\* if *ALL* IR status is IR_DONE in the RC NIB, update drain status 
\* in switchDrainStatusRCNIB to be DR_DRAINED
\* ===============================================
fair process routingControllerUpstream \in ({"RCUpstream"} \X {RoutingController})
begin
UpdateDrainStatus:
    while ~isFinished do
        \* Read from RC NIB
        await IsAllIRDoneRCNIB(switchesToBeUpdated) /\ Cardinality(FindSwitchedToBeDrainedRCNIB) > 0;
        switchesToBeDrained := FindSwitchedToBeDrainedRCNIB;
        \* Update RC NIB
        UpdateSwitchDrainStatusRCNIB:
            switchDrainStatusRCNIB := [sw \in NONTOR_SW |-> IF sw \in switchesToBeDrained
                                                         THEN DR_DRAINED
                                                         ELSE switchDrainStatusRCNIB[sw]]
    end while;
end process

\* ==========OFC Module ===========
\* Two threads for OFC
\* OFCDownstream: receive notification from RC NIB about IRs to send
\* OFCUpstream: receive switch ack from switches
\* ===============================================
fair process OFCDownstream \in ({"OFCDownstream"} \X {OFC})
variables nextSWToUpdate
begin
\* Deadlock!!!
OFCDownstream:
    while ~isFinished do
        \* Read NIB check if there is any ready IR
        OFCReadNIB:
        await Cardinality(ReadyIRSetInRC) > 0;
        nextSWToUpdate := CHOOSE sw \in ReadyIRSetInRC: TRUE;
        OFCWriteNIB:
        \* Write NIB, Change IR_READY to IR_SENT
        \* We do not model the message passing here
        \* Implication: once states change here, 
        \* other modules subscribing this NIB will get notified immediately
        if switchOperationStatusOFC[nextSWToUpdate] = SW_RUN then
            switchIRStatusRCNIB[nextSWToUpdate][2] := IR_SENT;
        end if;
    end while;
end process

fair process OFCUpstream \in ({"OFCUpstream"} \X {OFC})
variables nextSWToUpdate, DONEIRSet = {}
begin
OFCUpstream:
    while ~isFinished do
        await Cardinality(DoneIRSetInSwitch) > 0;
        switchIRStatusRCNIB := [sw \in DOMAIN switchIRStatusRCNIB |-> IF sw \in DoneIRSetInSwitch 
                                                                      THEN <<switchIRStatusRCNIB[sw][1], IR_DONE>>
                                                                      ELSE switchIRStatusRCNIB[sw]]
    end while;
end process

\* Each switch correponds to a TCP connection at OFC
fair process OFCSwitchConn \in (NONTOR_SW \X {OFCSwitchConnection})
begin
OFCFailureDetection:
    while ~isFinished do
        await switchOperationStatusOFC[self[1]] = SW_FAIL;
        switchOperationStatusRCNIB[self[1]] := SW_FAIL;
    end while;
end process

\* ==========Switch Module ===========
fair process switchPC \in (NONTOR_SW \X {Switch})
begin
switch:
    while ~isFinished do
        await SwitchReachable(self[1]);
        await switchIRStatusRCNIB[self[1]][2] = IR_SENT;
        \* copy IRID to switch TCAM; \* change IR status to IR_DONE at switches, OFCUpstream will immediately notice this change.
        switchIRStatusTCAM[self[1]] := switchIRStatusRCNIB[self[1]] || switchIRStatusTCAM[self[1]][2] := IR_DONE;
    end while;
end process
       
       
\*\* ==========Switch Failure Module ===========
fair process FailureGenerator  \in {<<"FailureGenerator", "FailureGenerator">>}
variables failedSwitchSet = {}
begin
GenerateFailures:
\*with failures \in { subset \in SUBSET NONTOR_SW : Cardinality(subset) = NUM_CONCURRENT_SW_FAILURES } do
with failures \in { {sw1, sw2} } do
    failedSwitchSet := failures;
end with;

FailSwitches:
    \* Change operation status, OFC will get notified immediately 
    \* This is the only place where switchOperationStatusOFC is changed
    switchOperationStatusOFC := [sw \in NONTOR_SW |-> IF sw \in failedSwitchSet
                                                         THEN SW_FAIL
                                                         ELSE switchOperationStatusOFC[sw]];
    \* change TCAM to empty immediately
    switchIRStatusTCAM := [sw \in NONTOR_SW |-> IF sw \in failedSwitchSet
                                                THEN <<-1, IR_NONE>>
                                                ELSE switchIRStatusTCAM[sw]];
end process

   
end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b1305af0c8f159f3bad54025acaeeb07
\* Label OFCDownstream of process OFCDownstream at line 134 col 5 changed to OFCDownstream_
\* Label OFCUpstream of process OFCUpstream at line 154 col 5 changed to OFCUpstream_
\* Process variable nextSWToUpdate of process OFCDownstream at line 131 col 11 changed to nextSWToUpdate_
CONSTANT defaultInitValue
VARIABLES topology, finalDrainStatus, lastUsedIRIndex, 
          switchOperationStatusRCNIB, switchDrainStatusRCNIB, 
          switchTargetDrainStatusRCNIB, switchesToBeDrained, 
          switchesToBeUpdated, switchIRStatusRCNIB, switchDrainStatusDRNIB, 
          switchTargetDrainStatusDRNIB, switchOperationStatusOFC, 
          switchIRStatusTCAM, isFinished, nonFirstStep, pc

(* define statement *)
FindSwitchedToBeDrainedDRNIB == {sw \in NONTOR_SW: switchDrainStatusDRNIB[sw] # switchTargetDrainStatusDRNIB[sw]}

FindSwitchedToBeDrainedRCNIB == {sw \in NONTOR_SW: switchDrainStatusRCNIB[sw] # switchTargetDrainStatusRCNIB[sw]}
ReadyIRSetInRC == {sw \in NONTOR_SW: switchIRStatusRCNIB[sw][2] = IR_READY}
DoneIRSetInSwitch == {sw \in NONTOR_SW: switchIRStatusTCAM[sw][2] = IR_DONE}
IsAllIRDoneRCNIB(swSet) == /\ Cardinality(swSet) > 0
                           /\ \A sw \in swSet: switchIRStatusRCNIB[sw][2] = IR_DONE

DoneIRSetInRCNIB == {sw \in switchesToBeUpdated: switchIRStatusRCNIB[sw][2] = IR_DONE}
SwitchReachable(sw) == \/ switchOperationStatusOFC[sw] =  SW_RUN
                       \/ switchOperationStatusOFC[sw] = SW_FAIL_UNKNOWN

VARIABLES swToBeDrained, swToBeUpdated, switchesToBeDrainedLocal, 
          switchesToBeUpdatedLocal, nextSWToUpdate_, nextSWToUpdate, 
          DONEIRSet, failedSwitchSet

vars == << topology, finalDrainStatus, lastUsedIRIndex, 
           switchOperationStatusRCNIB, switchDrainStatusRCNIB, 
           switchTargetDrainStatusRCNIB, switchesToBeDrained, 
           switchesToBeUpdated, switchIRStatusRCNIB, switchDrainStatusDRNIB, 
           switchTargetDrainStatusDRNIB, switchOperationStatusOFC, 
           switchIRStatusTCAM, isFinished, nonFirstStep, pc, swToBeDrained, 
           swToBeUpdated, switchesToBeDrainedLocal, switchesToBeUpdatedLocal, 
           nextSWToUpdate_, nextSWToUpdate, DONEIRSet, failedSwitchSet >>

ProcSet == (({"drainer"} \X {Drainer})) \cup (({"RCDownstream"} \X {RoutingController})) \cup (({"RCUpstream"} \X {RoutingController})) \cup (({"OFCDownstream"} \X {OFC})) \cup (({"OFCUpstream"} \X {OFC})) \cup ((NONTOR_SW \X {OFCSwitchConnection})) \cup ((NONTOR_SW \X {Switch})) \cup ({<<"FailureGenerator", "FailureGenerator">>})

Init == (* Global variables *)
        /\ topology = [sw1 |-> {sw3, sw4}, sw2 |-> {sw3, sw4}, sw3 |-> {sw1, sw2}, sw4 |-> {sw1, sw2}]
        /\ finalDrainStatus = DR_UNKNOWN
        /\ lastUsedIRIndex = 1
        /\ switchOperationStatusRCNIB = [x \in NONTOR_SW |-> SW_RUN]
        /\ switchDrainStatusRCNIB = [x \in NONTOR_SW |-> DR_UNDRAINED]
        /\ switchTargetDrainStatusRCNIB = [x \in NONTOR_SW |-> DR_UNDRAINED]
        /\ switchesToBeDrained = {}
        /\ switchesToBeUpdated = {}
        /\ switchIRStatusRCNIB = [x \in NONTOR_SW |-> <<-1, IR_NONE>>]
        /\ switchDrainStatusDRNIB = [x \in NONTOR_SW |-> DR_UNDRAINED]
        /\ switchTargetDrainStatusDRNIB = [sw1 |-> DR_DRAINED, sw2 |-> DR_UNDRAINED, sw3 |-> DR_DRAINED, sw4 |-> DR_UNDRAINED]
        /\ switchOperationStatusOFC = [x \in NONTOR_SW |-> SW_RUN]
        /\ switchIRStatusTCAM = [x \in NONTOR_SW |-> <<-1, IR_NONE>>]
        /\ isFinished = FALSE
        /\ nonFirstStep = FALSE
        (* Process routingControllerDownstream *)
        /\ swToBeDrained = [self \in ({"RCDownstream"} \X {RoutingController}) |-> defaultInitValue]
        /\ swToBeUpdated = [self \in ({"RCDownstream"} \X {RoutingController}) |-> defaultInitValue]
        /\ switchesToBeDrainedLocal = [self \in ({"RCDownstream"} \X {RoutingController}) |-> defaultInitValue]
        /\ switchesToBeUpdatedLocal = [self \in ({"RCDownstream"} \X {RoutingController}) |-> defaultInitValue]
        (* Process OFCDownstream *)
        /\ nextSWToUpdate_ = [self \in ({"OFCDownstream"} \X {OFC}) |-> defaultInitValue]
        (* Process OFCUpstream *)
        /\ nextSWToUpdate = [self \in ({"OFCUpstream"} \X {OFC}) |-> defaultInitValue]
        /\ DONEIRSet = [self \in ({"OFCUpstream"} \X {OFC}) |-> {}]
        (* Process FailureGenerator *)
        /\ failedSwitchSet = [self \in {<<"FailureGenerator", "FailureGenerator">>} |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in ({"drainer"} \X {Drainer}) -> "ProcessDRRequestAndSendToRC"
                                        [] self \in ({"RCDownstream"} \X {RoutingController}) -> "ProcessDRRequestAndSendToSwitches"
                                        [] self \in ({"RCUpstream"} \X {RoutingController}) -> "UpdateDrainStatus"
                                        [] self \in ({"OFCDownstream"} \X {OFC}) -> "OFCDownstream_"
                                        [] self \in ({"OFCUpstream"} \X {OFC}) -> "OFCUpstream_"
                                        [] self \in (NONTOR_SW \X {OFCSwitchConnection}) -> "OFCFailureDetection"
                                        [] self \in (NONTOR_SW \X {Switch}) -> "switch"
                                        [] self \in {<<"FailureGenerator", "FailureGenerator">>} -> "GenerateFailures"]

ProcessDRRequestAndSendToRC(self) == /\ pc[self] = "ProcessDRRequestAndSendToRC"
                                     /\ Cardinality(FindSwitchedToBeDrainedDRNIB) > 0
                                     /\ switchTargetDrainStatusRCNIB' = switchTargetDrainStatusDRNIB
                                     /\ pc' = [pc EXCEPT ![self] = "WaitRCACK"]
                                     /\ UNCHANGED << topology, 
                                                     finalDrainStatus, 
                                                     lastUsedIRIndex, 
                                                     switchOperationStatusRCNIB, 
                                                     switchDrainStatusRCNIB, 
                                                     switchesToBeDrained, 
                                                     switchesToBeUpdated, 
                                                     switchIRStatusRCNIB, 
                                                     switchDrainStatusDRNIB, 
                                                     switchTargetDrainStatusDRNIB, 
                                                     switchOperationStatusOFC, 
                                                     switchIRStatusTCAM, 
                                                     isFinished, nonFirstStep, 
                                                     swToBeDrained, 
                                                     swToBeUpdated, 
                                                     switchesToBeDrainedLocal, 
                                                     switchesToBeUpdatedLocal, 
                                                     nextSWToUpdate_, 
                                                     nextSWToUpdate, DONEIRSet, 
                                                     failedSwitchSet >>

WaitRCACK(self) == /\ pc[self] = "WaitRCACK"
                   /\ Cardinality(FindSwitchedToBeDrainedRCNIB) = 0
                   /\ switchDrainStatusDRNIB' = switchTargetDrainStatusDRNIB
                   /\ finalDrainStatus' = DR_SUCCESS
                   /\ isFinished' = TRUE
                   /\ PrintT(<<finalDrainStatus'>>)
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << topology, lastUsedIRIndex, 
                                   switchOperationStatusRCNIB, 
                                   switchDrainStatusRCNIB, 
                                   switchTargetDrainStatusRCNIB, 
                                   switchesToBeDrained, switchesToBeUpdated, 
                                   switchIRStatusRCNIB, 
                                   switchTargetDrainStatusDRNIB, 
                                   switchOperationStatusOFC, 
                                   switchIRStatusTCAM, nonFirstStep, 
                                   swToBeDrained, swToBeUpdated, 
                                   switchesToBeDrainedLocal, 
                                   switchesToBeUpdatedLocal, nextSWToUpdate_, 
                                   nextSWToUpdate, DONEIRSet, failedSwitchSet >>

drainer(self) == ProcessDRRequestAndSendToRC(self) \/ WaitRCACK(self)

ProcessDRRequestAndSendToSwitches(self) == /\ pc[self] = "ProcessDRRequestAndSendToSwitches"
                                           /\ Cardinality(FindSwitchedToBeDrainedRCNIB) > 0
                                           /\ switchesToBeDrained' = FindSwitchedToBeDrainedRCNIB
                                           /\ switchesToBeDrainedLocal' = [switchesToBeDrainedLocal EXCEPT ![self] = switchesToBeDrained']
                                           /\ pc' = [pc EXCEPT ![self] = "FindNeighbors"]
                                           /\ UNCHANGED << topology, 
                                                           finalDrainStatus, 
                                                           lastUsedIRIndex, 
                                                           switchOperationStatusRCNIB, 
                                                           switchDrainStatusRCNIB, 
                                                           switchTargetDrainStatusRCNIB, 
                                                           switchesToBeUpdated, 
                                                           switchIRStatusRCNIB, 
                                                           switchDrainStatusDRNIB, 
                                                           switchTargetDrainStatusDRNIB, 
                                                           switchOperationStatusOFC, 
                                                           switchIRStatusTCAM, 
                                                           isFinished, 
                                                           nonFirstStep, 
                                                           swToBeDrained, 
                                                           swToBeUpdated, 
                                                           switchesToBeUpdatedLocal, 
                                                           nextSWToUpdate_, 
                                                           nextSWToUpdate, 
                                                           DONEIRSet, 
                                                           failedSwitchSet >>

FindNeighbors(self) == /\ pc[self] = "FindNeighbors"
                       /\ IF Cardinality(switchesToBeDrainedLocal[self]) > 0
                             THEN /\ swToBeDrained' = [swToBeDrained EXCEPT ![self] = CHOOSE sw \in switchesToBeDrainedLocal[self]: TRUE]
                                  /\ switchesToBeUpdated' = (switchesToBeUpdated \union topology[swToBeDrained'[self]])
                                  /\ switchesToBeDrainedLocal' = [switchesToBeDrainedLocal EXCEPT ![self] = switchesToBeDrainedLocal[self]\{swToBeDrained'[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "FindNeighbors"]
                                  /\ UNCHANGED switchesToBeUpdatedLocal
                             ELSE /\ switchesToBeUpdated' = switchesToBeUpdated \ switchesToBeDrained
                                  /\ switchesToBeUpdatedLocal' = [switchesToBeUpdatedLocal EXCEPT ![self] = switchesToBeUpdated']
                                  /\ pc' = [pc EXCEPT ![self] = "GenerateIRs"]
                                  /\ UNCHANGED << swToBeDrained, 
                                                  switchesToBeDrainedLocal >>
                       /\ UNCHANGED << topology, finalDrainStatus, 
                                       lastUsedIRIndex, 
                                       switchOperationStatusRCNIB, 
                                       switchDrainStatusRCNIB, 
                                       switchTargetDrainStatusRCNIB, 
                                       switchesToBeDrained, 
                                       switchIRStatusRCNIB, 
                                       switchDrainStatusDRNIB, 
                                       switchTargetDrainStatusDRNIB, 
                                       switchOperationStatusOFC, 
                                       switchIRStatusTCAM, isFinished, 
                                       nonFirstStep, swToBeUpdated, 
                                       nextSWToUpdate_, nextSWToUpdate, 
                                       DONEIRSet, failedSwitchSet >>

GenerateIRs(self) == /\ pc[self] = "GenerateIRs"
                     /\ IF Cardinality(switchesToBeUpdatedLocal[self]) > 0
                           THEN /\ swToBeUpdated' = [swToBeUpdated EXCEPT ![self] = CHOOSE sw \in switchesToBeUpdatedLocal[self]: TRUE]
                                /\ switchIRStatusRCNIB' = [switchIRStatusRCNIB EXCEPT ![swToBeUpdated'[self]] = <<lastUsedIRIndex + 1, IR_READY>>]
                                /\ switchesToBeUpdatedLocal' = [switchesToBeUpdatedLocal EXCEPT ![self] = switchesToBeUpdatedLocal[self]\{swToBeUpdated'[self]}]
                                /\ lastUsedIRIndex' = lastUsedIRIndex + 1
                                /\ pc' = [pc EXCEPT ![self] = "GenerateIRs"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << lastUsedIRIndex, 
                                                switchIRStatusRCNIB, 
                                                swToBeUpdated, 
                                                switchesToBeUpdatedLocal >>
                     /\ UNCHANGED << topology, finalDrainStatus, 
                                     switchOperationStatusRCNIB, 
                                     switchDrainStatusRCNIB, 
                                     switchTargetDrainStatusRCNIB, 
                                     switchesToBeDrained, switchesToBeUpdated, 
                                     switchDrainStatusDRNIB, 
                                     switchTargetDrainStatusDRNIB, 
                                     switchOperationStatusOFC, 
                                     switchIRStatusTCAM, isFinished, 
                                     nonFirstStep, swToBeDrained, 
                                     switchesToBeDrainedLocal, nextSWToUpdate_, 
                                     nextSWToUpdate, DONEIRSet, 
                                     failedSwitchSet >>

routingControllerDownstream(self) == ProcessDRRequestAndSendToSwitches(self)
                                        \/ FindNeighbors(self)
                                        \/ GenerateIRs(self)

UpdateDrainStatus(self) == /\ pc[self] = "UpdateDrainStatus"
                           /\ IF ~isFinished
                                 THEN /\ IsAllIRDoneRCNIB(switchesToBeUpdated) /\ Cardinality(FindSwitchedToBeDrainedRCNIB) > 0
                                      /\ switchesToBeDrained' = FindSwitchedToBeDrainedRCNIB
                                      /\ pc' = [pc EXCEPT ![self] = "UpdateSwitchDrainStatusRCNIB"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                      /\ UNCHANGED switchesToBeDrained
                           /\ UNCHANGED << topology, finalDrainStatus, 
                                           lastUsedIRIndex, 
                                           switchOperationStatusRCNIB, 
                                           switchDrainStatusRCNIB, 
                                           switchTargetDrainStatusRCNIB, 
                                           switchesToBeUpdated, 
                                           switchIRStatusRCNIB, 
                                           switchDrainStatusDRNIB, 
                                           switchTargetDrainStatusDRNIB, 
                                           switchOperationStatusOFC, 
                                           switchIRStatusTCAM, isFinished, 
                                           nonFirstStep, swToBeDrained, 
                                           swToBeUpdated, 
                                           switchesToBeDrainedLocal, 
                                           switchesToBeUpdatedLocal, 
                                           nextSWToUpdate_, nextSWToUpdate, 
                                           DONEIRSet, failedSwitchSet >>

UpdateSwitchDrainStatusRCNIB(self) == /\ pc[self] = "UpdateSwitchDrainStatusRCNIB"
                                      /\ switchDrainStatusRCNIB' = [sw \in NONTOR_SW |-> IF sw \in switchesToBeDrained
                                                                                      THEN DR_DRAINED
                                                                                      ELSE switchDrainStatusRCNIB[sw]]
                                      /\ pc' = [pc EXCEPT ![self] = "UpdateDrainStatus"]
                                      /\ UNCHANGED << topology, 
                                                      finalDrainStatus, 
                                                      lastUsedIRIndex, 
                                                      switchOperationStatusRCNIB, 
                                                      switchTargetDrainStatusRCNIB, 
                                                      switchesToBeDrained, 
                                                      switchesToBeUpdated, 
                                                      switchIRStatusRCNIB, 
                                                      switchDrainStatusDRNIB, 
                                                      switchTargetDrainStatusDRNIB, 
                                                      switchOperationStatusOFC, 
                                                      switchIRStatusTCAM, 
                                                      isFinished, nonFirstStep, 
                                                      swToBeDrained, 
                                                      swToBeUpdated, 
                                                      switchesToBeDrainedLocal, 
                                                      switchesToBeUpdatedLocal, 
                                                      nextSWToUpdate_, 
                                                      nextSWToUpdate, 
                                                      DONEIRSet, 
                                                      failedSwitchSet >>

routingControllerUpstream(self) == UpdateDrainStatus(self)
                                      \/ UpdateSwitchDrainStatusRCNIB(self)

OFCDownstream_(self) == /\ pc[self] = "OFCDownstream_"
                        /\ IF ~isFinished
                              THEN /\ pc' = [pc EXCEPT ![self] = "OFCReadNIB"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << topology, finalDrainStatus, 
                                        lastUsedIRIndex, 
                                        switchOperationStatusRCNIB, 
                                        switchDrainStatusRCNIB, 
                                        switchTargetDrainStatusRCNIB, 
                                        switchesToBeDrained, 
                                        switchesToBeUpdated, 
                                        switchIRStatusRCNIB, 
                                        switchDrainStatusDRNIB, 
                                        switchTargetDrainStatusDRNIB, 
                                        switchOperationStatusOFC, 
                                        switchIRStatusTCAM, isFinished, 
                                        nonFirstStep, swToBeDrained, 
                                        swToBeUpdated, 
                                        switchesToBeDrainedLocal, 
                                        switchesToBeUpdatedLocal, 
                                        nextSWToUpdate_, nextSWToUpdate, 
                                        DONEIRSet, failedSwitchSet >>

OFCReadNIB(self) == /\ pc[self] = "OFCReadNIB"
                    /\ Cardinality(ReadyIRSetInRC) > 0
                    /\ nextSWToUpdate_' = [nextSWToUpdate_ EXCEPT ![self] = CHOOSE sw \in ReadyIRSetInRC: TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "OFCWriteNIB"]
                    /\ UNCHANGED << topology, finalDrainStatus, 
                                    lastUsedIRIndex, 
                                    switchOperationStatusRCNIB, 
                                    switchDrainStatusRCNIB, 
                                    switchTargetDrainStatusRCNIB, 
                                    switchesToBeDrained, switchesToBeUpdated, 
                                    switchIRStatusRCNIB, 
                                    switchDrainStatusDRNIB, 
                                    switchTargetDrainStatusDRNIB, 
                                    switchOperationStatusOFC, 
                                    switchIRStatusTCAM, isFinished, 
                                    nonFirstStep, swToBeDrained, swToBeUpdated, 
                                    switchesToBeDrainedLocal, 
                                    switchesToBeUpdatedLocal, nextSWToUpdate, 
                                    DONEIRSet, failedSwitchSet >>

OFCWriteNIB(self) == /\ pc[self] = "OFCWriteNIB"
                     /\ IF switchOperationStatusOFC[nextSWToUpdate_[self]] = SW_RUN
                           THEN /\ switchIRStatusRCNIB' = [switchIRStatusRCNIB EXCEPT ![nextSWToUpdate_[self]][2] = IR_SENT]
                           ELSE /\ TRUE
                                /\ UNCHANGED switchIRStatusRCNIB
                     /\ pc' = [pc EXCEPT ![self] = "OFCDownstream_"]
                     /\ UNCHANGED << topology, finalDrainStatus, 
                                     lastUsedIRIndex, 
                                     switchOperationStatusRCNIB, 
                                     switchDrainStatusRCNIB, 
                                     switchTargetDrainStatusRCNIB, 
                                     switchesToBeDrained, switchesToBeUpdated, 
                                     switchDrainStatusDRNIB, 
                                     switchTargetDrainStatusDRNIB, 
                                     switchOperationStatusOFC, 
                                     switchIRStatusTCAM, isFinished, 
                                     nonFirstStep, swToBeDrained, 
                                     swToBeUpdated, switchesToBeDrainedLocal, 
                                     switchesToBeUpdatedLocal, nextSWToUpdate_, 
                                     nextSWToUpdate, DONEIRSet, 
                                     failedSwitchSet >>

OFCDownstream(self) == OFCDownstream_(self) \/ OFCReadNIB(self)
                          \/ OFCWriteNIB(self)

OFCUpstream_(self) == /\ pc[self] = "OFCUpstream_"
                      /\ IF ~isFinished
                            THEN /\ Cardinality(DoneIRSetInSwitch) > 0
                                 /\ switchIRStatusRCNIB' = [sw \in DOMAIN switchIRStatusRCNIB |-> IF sw \in DoneIRSetInSwitch
                                                                                                  THEN <<switchIRStatusRCNIB[sw][1], IR_DONE>>
                                                                                                  ELSE switchIRStatusRCNIB[sw]]
                                 /\ pc' = [pc EXCEPT ![self] = "OFCUpstream_"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED switchIRStatusRCNIB
                      /\ UNCHANGED << topology, finalDrainStatus, 
                                      lastUsedIRIndex, 
                                      switchOperationStatusRCNIB, 
                                      switchDrainStatusRCNIB, 
                                      switchTargetDrainStatusRCNIB, 
                                      switchesToBeDrained, switchesToBeUpdated, 
                                      switchDrainStatusDRNIB, 
                                      switchTargetDrainStatusDRNIB, 
                                      switchOperationStatusOFC, 
                                      switchIRStatusTCAM, isFinished, 
                                      nonFirstStep, swToBeDrained, 
                                      swToBeUpdated, switchesToBeDrainedLocal, 
                                      switchesToBeUpdatedLocal, 
                                      nextSWToUpdate_, nextSWToUpdate, 
                                      DONEIRSet, failedSwitchSet >>

OFCUpstream(self) == OFCUpstream_(self)

OFCFailureDetection(self) == /\ pc[self] = "OFCFailureDetection"
                             /\ IF ~isFinished
                                   THEN /\ switchOperationStatusOFC[self[1]] = SW_FAIL
                                        /\ switchOperationStatusRCNIB' = [switchOperationStatusRCNIB EXCEPT ![self[1]] = SW_FAIL]
                                        /\ pc' = [pc EXCEPT ![self] = "OFCFailureDetection"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED switchOperationStatusRCNIB
                             /\ UNCHANGED << topology, finalDrainStatus, 
                                             lastUsedIRIndex, 
                                             switchDrainStatusRCNIB, 
                                             switchTargetDrainStatusRCNIB, 
                                             switchesToBeDrained, 
                                             switchesToBeUpdated, 
                                             switchIRStatusRCNIB, 
                                             switchDrainStatusDRNIB, 
                                             switchTargetDrainStatusDRNIB, 
                                             switchOperationStatusOFC, 
                                             switchIRStatusTCAM, isFinished, 
                                             nonFirstStep, swToBeDrained, 
                                             swToBeUpdated, 
                                             switchesToBeDrainedLocal, 
                                             switchesToBeUpdatedLocal, 
                                             nextSWToUpdate_, nextSWToUpdate, 
                                             DONEIRSet, failedSwitchSet >>

OFCSwitchConn(self) == OFCFailureDetection(self)

switch(self) == /\ pc[self] = "switch"
                /\ IF ~isFinished
                      THEN /\ SwitchReachable(self[1])
                           /\ switchIRStatusRCNIB[self[1]][2] = IR_SENT
                           /\ switchIRStatusTCAM' = [switchIRStatusTCAM EXCEPT ![self[1]] = switchIRStatusRCNIB[self[1]],
                                                                               ![self[1]][2] = IR_DONE]
                           /\ pc' = [pc EXCEPT ![self] = "switch"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED switchIRStatusTCAM
                /\ UNCHANGED << topology, finalDrainStatus, lastUsedIRIndex, 
                                switchOperationStatusRCNIB, 
                                switchDrainStatusRCNIB, 
                                switchTargetDrainStatusRCNIB, 
                                switchesToBeDrained, switchesToBeUpdated, 
                                switchIRStatusRCNIB, switchDrainStatusDRNIB, 
                                switchTargetDrainStatusDRNIB, 
                                switchOperationStatusOFC, isFinished, 
                                nonFirstStep, swToBeDrained, swToBeUpdated, 
                                switchesToBeDrainedLocal, 
                                switchesToBeUpdatedLocal, nextSWToUpdate_, 
                                nextSWToUpdate, DONEIRSet, failedSwitchSet >>

switchPC(self) == switch(self)

GenerateFailures(self) == /\ pc[self] = "GenerateFailures"
                          /\ \E failures \in { {sw1, sw2} }:
                               failedSwitchSet' = [failedSwitchSet EXCEPT ![self] = failures]
                          /\ pc' = [pc EXCEPT ![self] = "FailSwitches"]
                          /\ UNCHANGED << topology, finalDrainStatus, 
                                          lastUsedIRIndex, 
                                          switchOperationStatusRCNIB, 
                                          switchDrainStatusRCNIB, 
                                          switchTargetDrainStatusRCNIB, 
                                          switchesToBeDrained, 
                                          switchesToBeUpdated, 
                                          switchIRStatusRCNIB, 
                                          switchDrainStatusDRNIB, 
                                          switchTargetDrainStatusDRNIB, 
                                          switchOperationStatusOFC, 
                                          switchIRStatusTCAM, isFinished, 
                                          nonFirstStep, swToBeDrained, 
                                          swToBeUpdated, 
                                          switchesToBeDrainedLocal, 
                                          switchesToBeUpdatedLocal, 
                                          nextSWToUpdate_, nextSWToUpdate, 
                                          DONEIRSet >>

FailSwitches(self) == /\ pc[self] = "FailSwitches"
                      /\ switchOperationStatusOFC' = [sw \in NONTOR_SW |-> IF sw \in failedSwitchSet[self]
                                                                              THEN SW_FAIL
                                                                              ELSE switchOperationStatusOFC[sw]]
                      /\ switchIRStatusTCAM' = [sw \in NONTOR_SW |-> IF sw \in failedSwitchSet[self]
                                                                     THEN <<-1, IR_NONE>>
                                                                     ELSE switchIRStatusTCAM[sw]]
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << topology, finalDrainStatus, 
                                      lastUsedIRIndex, 
                                      switchOperationStatusRCNIB, 
                                      switchDrainStatusRCNIB, 
                                      switchTargetDrainStatusRCNIB, 
                                      switchesToBeDrained, switchesToBeUpdated, 
                                      switchIRStatusRCNIB, 
                                      switchDrainStatusDRNIB, 
                                      switchTargetDrainStatusDRNIB, isFinished, 
                                      nonFirstStep, swToBeDrained, 
                                      swToBeUpdated, switchesToBeDrainedLocal, 
                                      switchesToBeUpdatedLocal, 
                                      nextSWToUpdate_, nextSWToUpdate, 
                                      DONEIRSet, failedSwitchSet >>

FailureGenerator(self) == GenerateFailures(self) \/ FailSwitches(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ({"drainer"} \X {Drainer}): drainer(self))
           \/ (\E self \in ({"RCDownstream"} \X {RoutingController}): routingControllerDownstream(self))
           \/ (\E self \in ({"RCUpstream"} \X {RoutingController}): routingControllerUpstream(self))
           \/ (\E self \in ({"OFCDownstream"} \X {OFC}): OFCDownstream(self))
           \/ (\E self \in ({"OFCUpstream"} \X {OFC}): OFCUpstream(self))
           \/ (\E self \in (NONTOR_SW \X {OFCSwitchConnection}): OFCSwitchConn(self))
           \/ (\E self \in (NONTOR_SW \X {Switch}): switchPC(self))
           \/ (\E self \in {<<"FailureGenerator", "FailureGenerator">>}: FailureGenerator(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({"drainer"} \X {Drainer}) : WF_vars(drainer(self))
        /\ \A self \in ({"RCDownstream"} \X {RoutingController}) : WF_vars(routingControllerDownstream(self))
        /\ \A self \in ({"RCUpstream"} \X {RoutingController}) : WF_vars(routingControllerUpstream(self))
        /\ \A self \in ({"OFCDownstream"} \X {OFC}) : WF_vars(OFCDownstream(self))
        /\ \A self \in ({"OFCUpstream"} \X {OFC}) : WF_vars(OFCUpstream(self))
        /\ \A self \in (NONTOR_SW \X {OFCSwitchConnection}) : WF_vars(OFCSwitchConn(self))
        /\ \A self \in (NONTOR_SW \X {Switch}) : WF_vars(switchPC(self))
        /\ \A self \in {<<"FailureGenerator", "FailureGenerator">>} : WF_vars(FailureGenerator(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3a27bbdfc83b1c9f8ba493d57a566925

DrainSucceed == <>(finalDrainStatus = DR_SUCCESS /\ isFinished = TRUE)

=============================================================================
\* Modification History
\* Last modified Sun Oct 25 23:22:23 PDT 2020 by zmy
\* Created Sun Oct 18 13:36:59 PDT 2020 by zmy

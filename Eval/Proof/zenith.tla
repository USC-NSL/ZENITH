------------------- MODULE zenith -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

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

INSTALLABLE_IR_SET == 1..MaxNumIRs
SCHEDULABLE_IR_SET == 1..2*MaxNumIRs
ALL_IR_SET == 0..2*MaxNumIRs
DAG_ID_SET == 1..MaxDAGID

ExistsItemWithTag(queue, tag) == \E x \in DOMAIN queue: queue[x].tag = tag
GetFirstItemIndexWithTag(queue, tag) == 
    CHOOSE x \in DOMAIN queue: /\ queue[x].tag = tag
                               /\ ~\E y \in DOMAIN queue: /\ y < x
                                                          /\ queue[y].tag = tag
GetFirstUntaggedItemIndex(queue) == GetFirstItemIndexWithTag(queue, NADIR_NULL)
RemoveFromSequenceByIndex(seq, index) == [j \in 1..(Len(seq) - 1) |-> IF j < index THEN seq[j] ELSE seq[j+1]]
GetItemIndexWithTag(queue, tag) == IF ~ExistsItemWithTag(queue, tag)
                                    THEN GetFirstUntaggedItemIndex(queue)
                                    ELSE GetFirstItemIndexWithTag(queue, tag)

(*--fair algorithm zenith
    variables 
        (* Switch variables *)
        sw_fail_ordering_var = SW_FAIL_ORDERING,
        switchStatus = [
            x \in SW |-> [
                cpu |-> NotFailed, 
                nicAsic |-> NotFailed, 
                ofa |-> NotFailed, 
                installer |-> NotFailed
            ]
        ],  
        installedIRs = <<>>,
        TCAM = [x \in SW |-> {}], 
        controlMsgCounter = [x \in SW |-> 0],
        RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]],
        \* Previously local variable of `swProcess`
        ingressPkt = NADIR_NULL,
        \* Previously local variable of `swFailureProc`
        statusMsg = NADIR_NULL, 
        switchObject = NADIR_NULL,
        \* Previously local variable of `swResolveFailure`
        statusResolveMsg = NADIR_NULL,
        (* Zenith variables *)
        swSeqChangedStatus = <<>>,
        controller2Switch = [x \in SW |-> <<>>],
        switch2Controller = <<>>,
        TEEventQueue = <<>>,
        DAGEventQueue = <<>>,
        DAGQueue = <<>>,
        IRQueueNIB = <<>>,
        RCNIBEventQueue = <<>>,
        DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
        RCSwSuspensionStatus = [y \in SW |-> SW_RUN],
        RCIRStatus = [y \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]],
        NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]],
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        ScheduledIRs = [x \in 1..2*MaxNumIRs |-> FALSE],
        seqWorkerIsBusy = FALSE,
        \* Previously local variable(s) of `RCNibEventHandler`
        nibEvent = NADIR_NULL,
        \* Previously local variable(s) of `ControllerTrafficEngineering`
        topoChangeEvent = NADIR_NULL, 
        currSetDownSw = {}, 
        prev_dag_id = NADIR_NULL, 
        init = TRUE,
        DAGID = NADIR_NULL, 
        nxtDAG = NADIR_NULL, 
        nxtDAGVertices = {}, 
        setRemovableIRs = {},
        irsToUnschedule = {}, 
        unschedule = NADIR_NULL,
        irToRemove = NADIR_NULL,
        irToAdd = NADIR_NULL,
        irsToConnect = {},
        irToConnect = NADIR_NULL,
        \* Previously local variable(s) of `ControllerBossSequencer`
        seqEvent = NADIR_NULL,
        \* Previously local variable(s) of `ControllerSequencer`
        toBeScheduledIRs = {}, 
        nextIR = NADIR_NULL, 
        currDAG = NADIR_NULL, 
        IRDoneSet = {},    
        irSet = {}, 
        pickedIR = NADIR_NULL,       
        \* Previously local variable(s) of `ControllerWorkerThreads`
        nextIRObjectToSend = NADIR_NULL, 
        index = 0,
        \* Previously local variable(s) of `ControllerEventHandler`
        monitoringEvent = NADIR_NULL, 
        setIRsToReset = {}, 
        resetIR = NADIR_NULL,
        \* Previously local variable(s) of `ControllerMonitoringServer`
        msg = NADIR_NULL, 
        currentIRID = NADIR_NULL,

    define
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
        
        swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed 
        swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                                  /\ switchStatus[sw].ofa = NotFailed
        
        existMatchingEntryTCAM(swID, flowID) == flowID \in TCAM[swID]
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
        
        returnSwitchElementsNotFailed(sw) == {
            x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                           /\ x = "nicAsic"
        }
        returnSwitchFailedElements(sw) == {
            x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                           /\ \/ switchStatus[sw].cpu = NotFailed
                                              \/ x \notin {"ofa", "installer"}
        }
        getInstallerStatus(stat) == IF stat = NotFailed 
                                    THEN INSTALLER_UP
                                    ELSE INSTALLER_DOWN     

        isPrimary(ir) == IF ir \leq MaxNumIRs THEN TRUE ELSE FALSE
        getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN (ir + MaxNumIRs)
                                                ELSE (ir - MaxNumIRs)
        getPrimaryOfIR(ir) == IF ir \leq MaxNumIRs THEN ir 
                                                   ELSE (ir - MaxNumIRs)
        getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
        isClearIR(idID) == IF idID = 0 THEN TRUE ELSE FALSE
        getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW
                                                  ELSE DELETE_FLOW
        getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                             ELSE (flowID + MaxNumIRs)
        
        getNIBIRState(irID) == IF isPrimary(irID) THEN NIBIRStatus[irID].primary
                                                  ELSE NIBIRStatus[getPrimaryOfIR(irID)].dual
        getRCIRState(irID) == IF isPrimary(irID) THEN RCIRStatus[irID].primary
                                                 ELSE RCIRStatus[getPrimaryOfIR(irID)].dual
        
        getSetUnschedulableIRs(nxtDAGV) == {x \in nxtDAGV: getRCIRState(x) # IR_NONE}
        getSetRemovableIRs(swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ getRCIRState(x) # IR_NONE
                                                                      \/ ScheduledIRs[x] = TRUE
                                                                   /\ x \notin nxtDAGV
                                                                   /\ getSwitchForIR(x) \in swSet}
        getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: getSwitchForIR(x) = swID}
        isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                           /\ getRCIRState(y) # IR_DONE
        getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ getRCIRState(x) = IR_NONE
                                                           /\ isDependencySatisfied(DAG, x)
                                                           /\ RCSwSuspensionStatus[getSwitchForIR(x)] = SW_RUN
                                                           /\ ScheduledIRs[x] = FALSE}
        allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: getRCIRState(y) # IR_DONE
        isDAGStale(id) == DAGState[id] # DAG_SUBMIT
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                        /\ swSeqChangedStatus[x].num > monEvent.num
                                                                                        /\ swSeqChangedStatus[x].type # CLEARED_TCAM_SUCCESSFULLY
        
        shouldSuspendRunningSw(monEvent) == /\ \/ monEvent.type = OFA_DOWN
                                               \/ monEvent.type = NIC_ASIC_DOWN
                                               \/ /\ monEvent.type = KEEP_ALIVE
                                                  /\ monEvent.installerStatus = INSTALLER_DOWN
                                            /\ SwSuspensionStatus[monEvent.swID] = SW_RUN
        
        shouldClearSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                            /\ monEvent.installerStatus = INSTALLER_UP
                                            /\ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND
        
        shouldFreeSuspendedSw(monEvent) == /\ monEvent.type = CLEARED_TCAM_SUCCESSFULLY
                                           /\ monEvent.installerStatus = INSTALLER_UP 
                                           /\ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND 
                                        
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ getSwitchForIR(x) = SID
                                                     /\ getNIBIRState(x) # IR_NONE}
    
        isFinished == \A x \in 1..MaxNumIRs: getNIBIRState(x) = IR_DONE
        allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getRCIRState(y) = IR_DONE
                                                      /\ \/ getRCIRState(getDualOfIR(y)) # IR_NONE
                                                         \/ ScheduledIRs[getDualOfIR(y)] = TRUE
        dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag)
                                                    /\ ~isDAGStale(dagObject.id)
                                                 \/ ~allIRsInDAGAreStable(dagObject.dag)
    end define

    macro removeFromSeqSet(SeqSet, obj)
    begin
        if Cardinality(Head(SeqSet)) = 1 then
            SeqSet := Tail(SeqSet);
        else
            SeqSet := <<(Head(SeqSet)\{obj})>> \o Tail(SeqSet);
        end if; 
    end macro

    macro completeFailure()
    begin
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusMsg := [type |-> NIC_ASIC_DOWN, 
                            swID |-> self[2],
                            num |-> controlMsgCounter[self[2]]];
            switch2Controller := Append(switch2Controller, statusMsg);
        end if;
        
        switchStatus[self[2]] := [cpu |-> Failed, nicAsic |-> Failed, 
                                    ofa |-> Failed, installer |-> Failed];
        TCAM[self[2]] := {};
        controller2Switch[self[2]] := <<>>;
    end macro;

    macro resolveCompleteFailure()
    begin
        switchStatus[self[2]] := [cpu |-> NotFailed, nicAsic |-> NotFailed, 
                                    ofa |-> NotFailed, installer |-> NotFailed];
        TCAM[self[2]] := {};
        controller2Switch[self[2]] := <<>>;
        
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
        statusResolveMsg := [
            type |-> KEEP_ALIVE, 
            swID |-> self[2],
            num |-> controlMsgCounter[self[2]],
            installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
        ];
        switch2Controller := Append(switch2Controller, statusResolveMsg);
    end macro;

    macro installToTCAM(newFlow)
    begin
        installedIRs := Append(installedIRs, newFlow);
        TCAM[self[2]] := TCAM[self[2]] \cup {newFlow};
    end macro

    macro removeFromTCAM(flowID)
    begin
        if existMatchingEntryTCAM(self[2], flowID) then
            TCAM[self[2]] := TCAM[self[2]] \ {flowID};
        end if;
    end macro

    macro clearTCAM() begin
        TCAM[self[2]] := {};
    end macro;

    macro switchSend(msg)
    begin
        switch2Controller := Append(switch2Controller, msg);
    end macro

    macro sendConfirmation(controllerID, flowID, statusType)
    begin
        switchSend([
            type |-> statusType, 
            from |-> self[2], 
            to |-> controllerID,
            flow |-> flowID
        ]);
    end macro

    macro sendClearConfirmation() begin
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
        switch2Controller := Append(
            switch2Controller, 
            [
                type |-> CLEARED_TCAM_SUCCESSFULLY, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]],
                installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
            ]
        );
    end macro;

    macro NadirFIFOPeek(queue, message)
    begin
        await Len(queue) > 0;
        message := Head(queue);
    end macro;

    macro NadirFIFOPeekWithTimeout(queue, message)
    begin
        if Len(queue) > 0 then
            message := Head(queue);
        else
            message := NADIR_NULL;
        end if;
    end macro;

    macro NadirFIFOPop(queue)
    begin
        queue := Tail(queue);
    end macro;

    macro NadirFIFOPut(queue, object)
    begin
        queue := Append(queue, object);
    end macro;

    macro NadirFIFOGet(queue, message)
    begin
        await Len(queue) > 0;
        message := Head(queue);
        queue := Tail(queue);
    end macro;

    macro NadirFanoutFIFOPut(queue, branch, object)
    begin
        queue[branch] := Append(queue[branch], object);
    end macro;

    macro NadirAckQueuePut(queue, object)
    begin
        queue := Append(queue, [data |-> object, tag |-> NADIR_NULL]);
    end macro;

    macro NadirAckQueueGet(queue, tag, index, message)
    begin
        await ExistsItemWithTag(queue, NADIR_NULL) \/ ExistsItemWithTag(queue, tag);
        index := GetItemIndexWithTag(queue, tag);
        message := queue[index].data;
        queue[index].tag := tag;
    end macro;

    macro NadirAckQueueAck(queue, tag, index)
    begin
        index := GetFirstItemIndexWithTag(queue, tag);
        queue := RemoveFromSequenceByIndex(queue, index);
    end macro;

    macro controllerSendIR(irObject)
    begin
        if isClearIR(irObject.IR) then
            NadirFanoutFIFOPut(
                controller2Switch,
                irObject.sw,
                [
                    type |-> CLEAR_TCAM, 
                    flow |-> 0, 
                    to |-> irObject.sw, 
                    from |-> self[1]
                ]
            );
        else
            NadirFanoutFIFOPut(
                controller2Switch,
                irObject.sw,
                [
                    type |-> getIRType(irObject.IR), 
                    flow |-> getPrimaryOfIR(irObject.IR), 
                    to |-> irObject.sw, 
                    from |-> self[1]
                ]
            );
        end if;
    end macro;

    macro getNextDAGID()
    begin
        if DAGID = NADIR_NULL then
            DAGID := 1
        else
            DAGID := (DAGID % MaxDAGID) + 1
        end if;
    end macro;

    macro setNIBIRState(irID, state) begin
        if (isPrimary(irID)) then
            if state = IR_DONE /\ NIBIRStatus[irID].dual = IR_DONE then
                NIBIRStatus[irID] := [primary |-> IR_DONE, dual |-> IR_NONE]
            else
                NIBIRStatus[irID].primary := state
            end if;
        else
            with primary = getPrimaryOfIR(irID) do
                if state = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE then
                    NIBIRStatus[primary] := [primary |-> IR_NONE, dual |-> IR_DONE]
                else
                    NIBIRStatus[primary].dual := state
                end if;
            end with;
        end if;
    end macro;

    macro setRCIRState(irID, state) begin
        if (isPrimary(irID)) then
            if state = IR_DONE /\ RCIRStatus[irID].dual = IR_DONE then
                RCIRStatus[irID] := [primary |-> IR_DONE, dual |-> IR_NONE]
            else
                RCIRStatus[irID].primary := state
            end if;
        else
            with primary = getPrimaryOfIR(irID) do
                if state = IR_DONE /\ RCIRStatus[primary].primary = IR_DONE then
                    RCIRStatus[primary] := [primary |-> IR_NONE, dual |-> IR_DONE]
                else
                    RCIRStatus[primary].dual := state
                end if;
            end with;
        end if;
    end macro;

    fair process swProcess \in ({SW_SIMPLE_ID} \X SW)
    begin
    SwitchSimpleProcess:
    while TRUE do
        await swCanReceivePackets(self[2]);         
        await Len(controller2Switch[self[2]]) > 0;
        ingressPkt := Head(controller2Switch[self[2]]);
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        if ingressPkt.type = INSTALL_FLOW then
            installToTCAM(ingressPkt.flow);
            sendConfirmation(ingressPkt.from, ingressPkt.flow, INSTALLED_SUCCESSFULLY);
        elsif ingressPkt.type = DELETE_FLOW then
            removeFromTCAM(ingressPkt.flow);
            sendConfirmation(ingressPkt.from, ingressPkt.flow, DELETED_SUCCESSFULLY);
        elsif ingressPkt.type = CLEAR_TCAM then
            clearTCAM();
            sendClearConfirmation();
        end if;
    end while;
    end process;

    fair process swFailureProc \in ({SW_FAILURE_PROC} \X SW)
    begin
    SwitchFailure:
    while TRUE do
        await sw_fail_ordering_var # <<>>;
        await \E x \in Head(sw_fail_ordering_var): x.sw = self[2];
        switchObject := CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2];
        RecoveryStatus[self[2]].transient := switchObject.transient || RecoveryStatus[self[2]].partial := switchObject.partial;
        removeFromSeqSet(sw_fail_ordering_var, switchObject);
        completeFailure();
    end while
    end process

    fair process swResolveFailure \in ({SW_RESOLVE_PROC} \X SW)
    begin
    SwitchResolveFailure:
    while TRUE do
        await RecoveryStatus[self[2]].transient = 1;
        resolveCompleteFailure();  
        RecoveryStatus[self[2]] := [transient |-> 0, partial |-> 0];
    end while
    end process

    fair process rcNibEventHandler \in ({rc0} \X {NIB_EVENT_HANDLER})
    begin
    RCSNIBEventHndlerProc:
    while TRUE do
        NadirFIFOPeek(RCNIBEventQueue, nibEvent);
        if (nibEvent.type = TOPO_MOD) then
            if RCSwSuspensionStatus[nibEvent.sw] # nibEvent.state then    
                RCSwSuspensionStatus[nibEvent.sw] := nibEvent.state;
                NadirFIFOPut(TEEventQueue, nibEvent);
            end if;
        elsif (nibEvent.type = IR_MOD) then
            if getRCIRState(nibEvent.IR) # nibEvent.state then
                setRCIRState(nibEvent.IR, nibEvent.state);
                ScheduledIRs[nibEvent.IR] := FALSE;
            end if;
        elsif (nibEvent.type = IR_FAILED) then
            ScheduledIRs[nibEvent.IR] := FALSE;
        end if;
        NadirFIFOPop(RCNIBEventQueue);
    end while;
    end process

    fair process controllerTrafficEngineering \in ({rc0} \X {CONT_TE})
    begin
    ControllerTEProc:
    while TRUE do
        if init = TRUE then
            goto ControllerTEComputeDagBasedOnTopo;
        else
            NadirFIFOPeek(TEEventQueue, topoChangeEvent);
        end if;
        
        ControllerTEEventProcessing:
        while init # TRUE do
            if topoChangeEvent = NADIR_NULL then
                NadirFIFOPeekWithTimeout(TEEventQueue, topoChangeEvent);
                if topoChangeEvent = NADIR_NULL then
                    goto ControllerTEComputeDagBasedOnTopo;
                end if;
            else
                if topoChangeEvent.state = SW_SUSPEND then
                    currSetDownSw := currSetDownSw \cup {topoChangeEvent.sw};
                else
                    currSetDownSw := currSetDownSw \ {topoChangeEvent.sw};
                end if; 
                NadirFIFOPop(TEEventQueue);
                topoChangeEvent := NADIR_NULL;
            end if;
        end while;
        
        ControllerTEComputeDagBasedOnTopo:
            getNextDAGID();
            nxtDAG := [id |-> DAGID, dag |-> TOPO_DAG_MAPPING[currSetDownSw]];
            nxtDAGVertices := nxtDAG.dag.v;
            if init = FALSE then
                DAGState[prev_dag_id] := DAG_STALE;
                NadirFIFOPut(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id]);
            
                ControllerTEWaitForStaleDAGToBeRemoved:
                    await DAGState[prev_dag_id] = DAG_NONE;
                    prev_dag_id := DAGID;
                    setRemovableIRs := getSetRemovableIRs(SW \ currSetDownSw, nxtDAGVertices);
            else
                init := FALSE;
                prev_dag_id := DAGID;
            end if;
            
        ControllerTERemoveUnnecessaryIRs:
            while Cardinality(setRemovableIRs) > 0 do
                irToRemove := CHOOSE x \in setRemovableIRs: TRUE;
                setRemovableIRs := setRemovableIRs \ {irToRemove};
                irToAdd := getDualOfIR(irToRemove);
                irsToConnect := getSetIRsForSwitchInDAG(getSwitchForIR(irToRemove), nxtDAG.dag.v);
                nxtDAG.dag.v := nxtDAG.dag.v \cup {irToAdd};
                
                ConnectEdges:
                while Cardinality(irsToConnect) > 0 do
                    irToConnect := CHOOSE x \in irsToConnect: TRUE;
                    irsToConnect := irsToConnect \ {irToConnect};
                    nxtDAG.dag.e := nxtDAG.dag.e \cup {<<irToAdd, irToConnect>>};
                end while;
            end while;

            irsToUnschedule := nxtDAG.dag.v;
            ControllerUnscheduleIRsInDAG:
                while Cardinality(irsToUnschedule) > 0 do
                    unschedule := CHOOSE x \in irsToUnschedule: TRUE;
                    if (getRCIRState(unschedule) # IR_NONE) then
                        ScheduledIRs[unschedule] := FALSE;
                    end if;
                    irsToUnschedule := irsToUnschedule \ {unschedule};
                end while;
            
        ControllerTESubmitNewDAG:
            DAGState[nxtDAG.id] := DAG_SUBMIT;
            NadirFIFOPut(DAGEventQueue, [type |-> DAG_NEW, dag_obj |-> nxtDAG]);
    end while;
    end process

    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    begin
    ControllerBossSeqProc:
    while TRUE do
        NadirFIFOGet(DAGEventQueue, seqEvent);
        if seqEvent.type = DAG_NEW then
            NadirFIFOPut(DAGQueue, seqEvent.dag_obj);
        else
            if seqWorkerIsBusy # FALSE then
                WaitForRCSeqWorkerTerminate:
                    await seqWorkerIsBusy = FALSE;
                    DAGState[seqEvent.id] := DAG_NONE;
            else
                DAGState[seqEvent.id] := DAG_NONE;
            end if;
        end if;
    end while;
    end process

    fair process controllerSequencer \in ({rc0} \X {CONT_WORKER_SEQ})
    begin
    ControllerWorkerSeqProc:
    while TRUE do
        NadirFIFOPeek(DAGQueue, currDAG);
        seqWorkerIsBusy := TRUE;
        
        ControllerWorkerSeqScheduleDAG:
            while dagObjectShouldBeProcessed(currDAG) do
                toBeScheduledIRs := getSetIRsCanBeScheduledNext(currDAG.dag);
                await toBeScheduledIRs # {};

                SchedulerMechanism:
                while TRUE do
                    if toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then
                        goto ControllerWorkerSeqScheduleDAG;
                    else
                        nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                        with destination = getSwitchForIR(nextIR) do
                            ScheduledIRs[nextIR] := TRUE;
                            
                            if getIRType(nextIR) = INSTALL_FLOW then
                                IRDoneSet := IRDoneSet \cup {nextIR};
                            else
                                IRDoneSet := IRDoneSet \ {getDualOfIR(nextIR)}
                            end if;

                            NadirAckQueuePut(IRQueueNIB, [IR |-> nextIR, sw |-> destination]);
                            toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                        end with;
                    end if;
                end while;                                                
            end while;

            seqWorkerIsBusy := FALSE;
            irSet := currDAG.dag.v;
            if allIRsInDAGInstalled(currDAG.dag) then
                AddDeleteDAGIRDoneSet:
                while Cardinality(irSet) > 0 do
                    pickedIR := CHOOSE x \in irSet: TRUE;
                    if (getIRType(pickedIR) = INSTALL_FLOW) then
                        IRDoneSet := IRDoneSet \cup {pickedIR};
                    else
                        IRDoneSet := IRDoneSet \ {pickedIR};
                    end if;
                    irSet := irSet \ {pickedIR};
                end while;
            end if;
            RemoveDagFromQueue:
                NadirFIFOPop(DAGQueue);
    end while;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    begin
    ControllerThread:
    while TRUE do
        NadirAckQueueGet(IRQueueNIB, self, index, nextIRObjectToSend);

        ControllerThreadSendIR:        
            if isClearIR(nextIRObjectToSend.IR) then
                if isSwitchSuspended(nextIRObjectToSend.sw) then
                    controllerSendIR(nextIRObjectToSend);
                end if;
            elsif getNIBIRState(nextIRObjectToSend.IR) \in {IR_NONE, IR_SENT} then
                if isSwitchSuspended(nextIRObjectToSend.sw) then
                    NadirFIFOPut(RCNIBEventQueue, [type |-> IR_FAILED, IR |-> nextIRObjectToSend.IR, state |-> IR_NONE]);
                else
                    setNIBIRState(nextIRObjectToSend.IR, IR_SENT);
                    NadirFIFOPut(RCNIBEventQueue, [type |-> IR_MOD, IR |-> nextIRObjectToSend.IR, state |-> IR_SENT]);

                    ControllerThreadForwardIR:
                        controllerSendIR(nextIRObjectToSend);
                end if;
            end if;
        
        ControllerThreadRemoveIRFromQueue:
            NadirAckQueueAck(IRQueueNIB, self, index);
    end while;
    end process

    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    begin
    ControllerEventHandlerProc:
    while TRUE do 
        NadirFIFOPeek(swSeqChangedStatus, monitoringEvent);

        if shouldSuspendRunningSw(monitoringEvent) then
            ControllerSuspendSW:
                SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]
                );
        
        elsif shouldClearSuspendedSw(monitoringEvent) then
            ControllerRequestTCAMClear:
                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    NadirAckQueuePut(IRQueueNIB, [IR |-> 0, sw |-> monitoringEvent.swID]);
                end if;

        elsif shouldFreeSuspendedSw(monitoringEvent) then
            ControllerCheckIfThisIsLastEvent:
                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    getIRsToBeChecked:
                        setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                        if (setIRsToReset = {}) then
                            goto ControllerFreeSuspendedSW;
                        end if;

                    ResetAllIRs:
                        while TRUE do
                            resetIR := CHOOSE x \in setIRsToReset: TRUE;
                            setIRsToReset := setIRsToReset \ {resetIR};
                            
                            setNIBIRState(resetIR, IR_NONE);
                            NadirFIFOPut(
                                RCNIBEventQueue,
                                [type |-> IR_MOD, IR |-> resetIR, state |-> IR_NONE]
                            );
                            if setIRsToReset = {} then
                                goto ControllerFreeSuspendedSW;
                            end if;
                        end while;
                end if;

            ControllerFreeSuspendedSW: 
                SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]
                );
        end if;

        ControllerEvenHanlderRemoveEventFromQueue:
            NadirFIFOPop(swSeqChangedStatus);
    end while;
    end process

    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        NadirFIFOPeek(switch2Controller, msg);
        
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            ControllerProcessIRMod:
                currentIRID := getIRIDForFlow(msg.flow, msg.type);
                setNIBIRState(currentIRID, IR_DONE);
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> IR_MOD, IR |-> currentIRID, state |-> IR_DONE]
                );
        else
            ForwardToEH:
                NadirFIFOPut(swSeqChangedStatus, msg);
        end if;

        MonitoringServerRemoveFromQueue:
            NadirFIFOPop(switch2Controller);
    end while
    end process
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "c8e87574" /\ chksum(tla) = "38f36060")
VARIABLES sw_fail_ordering_var, switchStatus, installedIRs, TCAM, 
          controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, 
          switchObject, statusResolveMsg, swSeqChangedStatus, 
          controller2Switch, switch2Controller, TEEventQueue, DAGEventQueue, 
          DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, 
          RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, 
          ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, 
          currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, 
          setRemovableIRs, irsToUnschedule, unschedule, irToRemove, irToAdd, 
          irsToConnect, irToConnect, seqEvent, toBeScheduledIRs, nextIR, 
          currDAG, IRDoneSet, irSet, pickedIR, nextIRObjectToSend, index, 
          monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, pc

(* define statement *)
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]

swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed
swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed

existMatchingEntryTCAM(swID, flowID) == flowID \in TCAM[swID]
swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed

returnSwitchElementsNotFailed(sw) == {
    x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                   /\ x = "nicAsic"
}
returnSwitchFailedElements(sw) == {
    x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                   /\ \/ switchStatus[sw].cpu = NotFailed
                                      \/ x \notin {"ofa", "installer"}
}
getInstallerStatus(stat) == IF stat = NotFailed
                            THEN INSTALLER_UP
                            ELSE INSTALLER_DOWN

isPrimary(ir) == IF ir \leq MaxNumIRs THEN TRUE ELSE FALSE
getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN (ir + MaxNumIRs)
                                        ELSE (ir - MaxNumIRs)
getPrimaryOfIR(ir) == IF ir \leq MaxNumIRs THEN ir
                                           ELSE (ir - MaxNumIRs)
getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
isClearIR(idID) == IF idID = 0 THEN TRUE ELSE FALSE
getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW
                                          ELSE DELETE_FLOW
getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                     ELSE (flowID + MaxNumIRs)

getNIBIRState(irID) == IF isPrimary(irID) THEN NIBIRStatus[irID].primary
                                          ELSE NIBIRStatus[getPrimaryOfIR(irID)].dual
getRCIRState(irID) == IF isPrimary(irID) THEN RCIRStatus[irID].primary
                                         ELSE RCIRStatus[getPrimaryOfIR(irID)].dual

getSetUnschedulableIRs(nxtDAGV) == {x \in nxtDAGV: getRCIRState(x) # IR_NONE}
getSetRemovableIRs(swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ getRCIRState(x) # IR_NONE
                                                              \/ ScheduledIRs[x] = TRUE
                                                           /\ x \notin nxtDAGV
                                                           /\ getSwitchForIR(x) \in swSet}
getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: getSwitchForIR(x) = swID}
isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                   /\ getRCIRState(y) # IR_DONE
getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ getRCIRState(x) = IR_NONE
                                                   /\ isDependencySatisfied(DAG, x)
                                                   /\ RCSwSuspensionStatus[getSwitchForIR(x)] = SW_RUN
                                                   /\ ScheduledIRs[x] = FALSE}
allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: getRCIRState(y) # IR_DONE
isDAGStale(id) == DAGState[id] # DAG_SUBMIT
isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                /\ swSeqChangedStatus[x].num > monEvent.num
                                                                                /\ swSeqChangedStatus[x].type # CLEARED_TCAM_SUCCESSFULLY

shouldSuspendRunningSw(monEvent) == /\ \/ monEvent.type = OFA_DOWN
                                       \/ monEvent.type = NIC_ASIC_DOWN
                                       \/ /\ monEvent.type = KEEP_ALIVE
                                          /\ monEvent.installerStatus = INSTALLER_DOWN
                                    /\ SwSuspensionStatus[monEvent.swID] = SW_RUN

shouldClearSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                    /\ monEvent.installerStatus = INSTALLER_UP
                                    /\ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND

shouldFreeSuspendedSw(monEvent) == /\ monEvent.type = CLEARED_TCAM_SUCCESSFULLY
                                   /\ monEvent.installerStatus = INSTALLER_UP
                                   /\ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND

getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ getSwitchForIR(x) = SID
                                             /\ getNIBIRState(x) # IR_NONE}

isFinished == \A x \in 1..MaxNumIRs: getNIBIRState(x) = IR_DONE
allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getRCIRState(y) = IR_DONE
                                              /\ \/ getRCIRState(getDualOfIR(y)) # IR_NONE
                                                 \/ ScheduledIRs[getDualOfIR(y)] = TRUE
dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag)
                                            /\ ~isDAGStale(dagObject.id)
                                         \/ ~allIRsInDAGAreStable(dagObject.dag)


vars == << sw_fail_ordering_var, switchStatus, installedIRs, TCAM, 
           controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, 
           switchObject, statusResolveMsg, swSeqChangedStatus, 
           controller2Switch, switch2Controller, TEEventQueue, DAGEventQueue, 
           DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, 
           RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, 
           ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, 
           currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, 
           setRemovableIRs, irsToUnschedule, unschedule, irToRemove, irToAdd, 
           irsToConnect, irToConnect, seqEvent, toBeScheduledIRs, nextIR, 
           currDAG, IRDoneSet, irSet, pickedIR, nextIRObjectToSend, index, 
           monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, pc >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))

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
        /\ ingressPkt = NADIR_NULL
        /\ statusMsg = NADIR_NULL
        /\ switchObject = NADIR_NULL
        /\ statusResolveMsg = NADIR_NULL
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
        /\ irToRemove = NADIR_NULL
        /\ irToAdd = NADIR_NULL
        /\ irsToConnect = {}
        /\ irToConnect = NADIR_NULL
        /\ seqEvent = NADIR_NULL
        /\ toBeScheduledIRs = {}
        /\ nextIR = NADIR_NULL
        /\ currDAG = NADIR_NULL
        /\ IRDoneSet = {}
        /\ irSet = {}
        /\ pickedIR = NADIR_NULL
        /\ nextIRObjectToSend = NADIR_NULL
        /\ index = 0
        /\ monitoringEvent = NADIR_NULL
        /\ setIRsToReset = {}
        /\ resetIR = NADIR_NULL
        /\ msg = NADIR_NULL
        /\ currentIRID = NADIR_NULL
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

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ swCanReceivePackets(self[2])
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ ingressPkt' = Head(controller2Switch[self[2]])
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ IF ingressPkt'.type = INSTALL_FLOW
                                   THEN /\ installedIRs' = Append(installedIRs, (ingressPkt'.flow))
                                        /\ TCAM' = [TCAM EXCEPT ![self[2]] = TCAM[self[2]] \cup {(ingressPkt'.flow)}]
                                        /\ switch2Controller' = Append(switch2Controller, (           [
                                                                    type |-> INSTALLED_SUCCESSFULLY,
                                                                    from |-> self[2],
                                                                    to |-> (ingressPkt'.from),
                                                                    flow |-> (ingressPkt'.flow)
                                                                ]))
                                        /\ UNCHANGED controlMsgCounter
                                   ELSE /\ IF ingressPkt'.type = DELETE_FLOW
                                              THEN /\ IF existMatchingEntryTCAM(self[2], (ingressPkt'.flow))
                                                         THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = TCAM[self[2]] \ {(ingressPkt'.flow)}]
                                                         ELSE /\ TRUE
                                                              /\ TCAM' = TCAM
                                                   /\ switch2Controller' = Append(switch2Controller, (           [
                                                                               type |-> DELETED_SUCCESSFULLY,
                                                                               from |-> self[2],
                                                                               to |-> (ingressPkt'.from),
                                                                               flow |-> (ingressPkt'.flow)
                                                                           ]))
                                                   /\ UNCHANGED controlMsgCounter
                                              ELSE /\ IF ingressPkt'.type = CLEAR_TCAM
                                                         THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                              /\ switch2Controller' =                      Append(
                                                                                          switch2Controller,
                                                                                          [
                                                                                              type |-> CLEARED_TCAM_SUCCESSFULLY,
                                                                                              swID |-> self[2],
                                                                                              num |-> controlMsgCounter'[self[2]],
                                                                                              installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                                                                                          ]
                                                                                      )
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << TCAM, 
                                                                              controlMsgCounter, 
                                                                              switch2Controller >>
                                        /\ UNCHANGED installedIRs
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << sw_fail_ordering_var, 
                                             switchStatus, RecoveryStatus, 
                                             statusMsg, switchObject, 
                                             statusResolveMsg, 
                                             swSeqChangedStatus, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, RCNIBEventQueue, 
                                             DAGState, RCSwSuspensionStatus, 
                                             RCIRStatus, NIBIRStatus, 
                                             SwSuspensionStatus, ScheduledIRs, 
                                             seqWorkerIsBusy, nibEvent, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, nxtDAG, 
                                             nxtDAGVertices, setRemovableIRs, 
                                             irsToUnschedule, unschedule, 
                                             irToRemove, irToAdd, irsToConnect, 
                                             irToConnect, seqEvent, 
                                             toBeScheduledIRs, nextIR, currDAG, 
                                             IRDoneSet, irSet, pickedIR, 
                                             nextIRObjectToSend, index, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, currentIRID >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ sw_fail_ordering_var # <<>>
                       /\ \E x \in Head(sw_fail_ordering_var): x.sw = self[2]
                       /\ switchObject' = (CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2])
                       /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]].transient = switchObject'.transient,
                                                                   ![self[2]].partial = switchObject'.partial]
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{switchObject'})>> \o Tail(sw_fail_ordering_var)
                       /\ IF switchStatus[self[2]].nicAsic = NotFailed
                             THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                  /\ statusMsg' = [type |-> NIC_ASIC_DOWN,
                                                     swID |-> self[2],
                                                     num |-> controlMsgCounter'[self[2]]]
                                  /\ switch2Controller' = Append(switch2Controller, statusMsg')
                             ELSE /\ TRUE
                                  /\ UNCHANGED << controlMsgCounter, statusMsg, 
                                                  switch2Controller >>
                       /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> Failed, nicAsic |-> Failed,
                                                                               ofa |-> Failed, installer |-> Failed]]
                       /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                       /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                       /\ UNCHANGED << installedIRs, ingressPkt, 
                                       statusResolveMsg, swSeqChangedStatus, 
                                       TEEventQueue, DAGEventQueue, DAGQueue, 
                                       IRQueueNIB, RCNIBEventQueue, DAGState, 
                                       RCSwSuspensionStatus, RCIRStatus, 
                                       NIBIRStatus, SwSuspensionStatus, 
                                       ScheduledIRs, seqWorkerIsBusy, nibEvent, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, DAGID, nxtDAG, 
                                       nxtDAGVertices, setRemovableIRs, 
                                       irsToUnschedule, unschedule, irToRemove, 
                                       irToAdd, irsToConnect, irToConnect, 
                                       seqEvent, toBeScheduledIRs, nextIR, 
                                       currDAG, IRDoneSet, irSet, pickedIR, 
                                       nextIRObjectToSend, index, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       msg, currentIRID >>

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ RecoveryStatus[self[2]].transient = 1
                              /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> NotFailed, nicAsic |-> NotFailed,
                                                                                      ofa |-> NotFailed, installer |-> NotFailed]]
                              /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                              /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                              /\ statusResolveMsg' =                     [
                                                         type |-> KEEP_ALIVE,
                                                         swID |-> self[2],
                                                         num |-> controlMsgCounter'[self[2]],
                                                         installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                     ]
                              /\ switch2Controller' = Append(switch2Controller, statusResolveMsg')
                              /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]] = [transient |-> 0, partial |-> 0]]
                              /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                              /\ UNCHANGED << sw_fail_ordering_var, 
                                              installedIRs, ingressPkt, 
                                              statusMsg, switchObject, 
                                              swSeqChangedStatus, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, 
                                              IRQueueNIB, RCNIBEventQueue, 
                                              DAGState, RCSwSuspensionStatus, 
                                              RCIRStatus, NIBIRStatus, 
                                              SwSuspensionStatus, ScheduledIRs, 
                                              seqWorkerIsBusy, nibEvent, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, DAGID, nxtDAG, 
                                              nxtDAGVertices, setRemovableIRs, 
                                              irsToUnschedule, unschedule, 
                                              irToRemove, irToAdd, 
                                              irsToConnect, irToConnect, 
                                              seqEvent, toBeScheduledIRs, 
                                              nextIR, currDAG, IRDoneSet, 
                                              irSet, pickedIR, 
                                              nextIRObjectToSend, index, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, msg, currentIRID >>

swResolveFailure(self) == SwitchResolveFailure(self)

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ Len(RCNIBEventQueue) > 0
                               /\ nibEvent' = Head(RCNIBEventQueue)
                               /\ IF (nibEvent'.type = TOPO_MOD)
                                     THEN /\ IF RCSwSuspensionStatus[nibEvent'.sw] # nibEvent'.state
                                                THEN /\ RCSwSuspensionStatus' = [RCSwSuspensionStatus EXCEPT ![nibEvent'.sw] = nibEvent'.state]
                                                     /\ TEEventQueue' = Append(TEEventQueue, nibEvent')
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << TEEventQueue, 
                                                                     RCSwSuspensionStatus >>
                                          /\ UNCHANGED << RCIRStatus, 
                                                          ScheduledIRs >>
                                     ELSE /\ IF (nibEvent'.type = IR_MOD)
                                                THEN /\ IF getRCIRState(nibEvent'.IR) # nibEvent'.state
                                                           THEN /\ IF (isPrimary((nibEvent'.IR)))
                                                                      THEN /\ IF (nibEvent'.state) = IR_DONE /\ RCIRStatus[(nibEvent'.IR)].dual = IR_DONE
                                                                                 THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![(nibEvent'.IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                 ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![(nibEvent'.IR)].primary = nibEvent'.state]
                                                                      ELSE /\ LET primary == getPrimaryOfIR((nibEvent'.IR)) IN
                                                                                IF (nibEvent'.state) = IR_DONE /\ RCIRStatus[primary].primary = IR_DONE
                                                                                   THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                   ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![primary].dual = nibEvent'.state]
                                                                /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![nibEvent'.IR] = FALSE]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << RCIRStatus, 
                                                                                ScheduledIRs >>
                                                ELSE /\ IF (nibEvent'.type = IR_FAILED)
                                                           THEN /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![nibEvent'.IR] = FALSE]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED ScheduledIRs
                                                     /\ UNCHANGED RCIRStatus
                                          /\ UNCHANGED << TEEventQueue, 
                                                          RCSwSuspensionStatus >>
                               /\ RCNIBEventQueue' = Tail(RCNIBEventQueue)
                               /\ pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]
                               /\ UNCHANGED << sw_fail_ordering_var, 
                                               switchStatus, installedIRs, 
                                               TCAM, controlMsgCounter, 
                                               RecoveryStatus, ingressPkt, 
                                               statusMsg, switchObject, 
                                               statusResolveMsg, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, DAGState, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               seqWorkerIsBusy, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, nxtDAGVertices, 
                                               setRemovableIRs, 
                                               irsToUnschedule, unschedule, 
                                               irToRemove, irToAdd, 
                                               irsToConnect, irToConnect, 
                                               seqEvent, toBeScheduledIRs, 
                                               nextIR, currDAG, IRDoneSet, 
                                               irSet, pickedIR, 
                                               nextIRObjectToSend, index, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, currentIRID >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ IF init = TRUE
                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                     /\ UNCHANGED topoChangeEvent
                                ELSE /\ Len(TEEventQueue) > 0
                                     /\ topoChangeEvent' = Head(TEEventQueue)
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                          installedIRs, TCAM, 
                                          controlMsgCounter, RecoveryStatus, 
                                          ingressPkt, statusMsg, switchObject, 
                                          statusResolveMsg, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, IRQueueNIB, 
                                          RCNIBEventQueue, DAGState, 
                                          RCSwSuspensionStatus, RCIRStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          ScheduledIRs, seqWorkerIsBusy, 
                                          nibEvent, currSetDownSw, prev_dag_id, 
                                          init, DAGID, nxtDAG, nxtDAGVertices, 
                                          setRemovableIRs, irsToUnschedule, 
                                          unschedule, irToRemove, irToAdd, 
                                          irsToConnect, irToConnect, seqEvent, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRDoneSet, irSet, pickedIR, 
                                          nextIRObjectToSend, index, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, msg, currentIRID >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF init # TRUE
                                           THEN /\ IF topoChangeEvent = NADIR_NULL
                                                      THEN /\ IF Len(TEEventQueue) > 0
                                                                 THEN /\ topoChangeEvent' = Head(TEEventQueue)
                                                                 ELSE /\ topoChangeEvent' = NADIR_NULL
                                                           /\ IF topoChangeEvent' = NADIR_NULL
                                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                                           /\ UNCHANGED << TEEventQueue, 
                                                                           currSetDownSw >>
                                                      ELSE /\ IF topoChangeEvent.state = SW_SUSPEND
                                                                 THEN /\ currSetDownSw' = (currSetDownSw \cup {topoChangeEvent.sw})
                                                                 ELSE /\ currSetDownSw' = currSetDownSw \ {topoChangeEvent.sw}
                                                           /\ TEEventQueue' = Tail(TEEventQueue)
                                                           /\ topoChangeEvent' = NADIR_NULL
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                /\ UNCHANGED << TEEventQueue, 
                                                                topoChangeEvent, 
                                                                currSetDownSw >>
                                     /\ UNCHANGED << sw_fail_ordering_var, 
                                                     switchStatus, 
                                                     installedIRs, TCAM, 
                                                     controlMsgCounter, 
                                                     RecoveryStatus, 
                                                     ingressPkt, statusMsg, 
                                                     switchObject, 
                                                     statusResolveMsg, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     DAGEventQueue, DAGQueue, 
                                                     IRQueueNIB, 
                                                     RCNIBEventQueue, DAGState, 
                                                     RCSwSuspensionStatus, 
                                                     RCIRStatus, NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     ScheduledIRs, 
                                                     seqWorkerIsBusy, nibEvent, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, nxtDAGVertices, 
                                                     setRemovableIRs, 
                                                     irsToUnschedule, 
                                                     unschedule, irToRemove, 
                                                     irToAdd, irsToConnect, 
                                                     irToConnect, seqEvent, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRDoneSet, irSet, 
                                                     pickedIR, 
                                                     nextIRObjectToSend, index, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, currentIRID >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ IF DAGID = NADIR_NULL
                                                 THEN /\ DAGID' = 1
                                                 ELSE /\ DAGID' = (DAGID % MaxDAGID) + 1
                                           /\ nxtDAG' = [id |-> DAGID', dag |-> TOPO_DAG_MAPPING[currSetDownSw]]
                                           /\ nxtDAGVertices' = nxtDAG'.dag.v
                                           /\ IF init = FALSE
                                                 THEN /\ DAGState' = [DAGState EXCEPT ![prev_dag_id] = DAG_STALE]
                                                      /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_STALE, id |-> prev_dag_id]))
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                                      /\ UNCHANGED << prev_dag_id, 
                                                                      init >>
                                                 ELSE /\ init' = FALSE
                                                      /\ prev_dag_id' = DAGID'
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                      /\ UNCHANGED << DAGEventQueue, 
                                                                      DAGState >>
                                           /\ UNCHANGED << sw_fail_ordering_var, 
                                                           switchStatus, 
                                                           installedIRs, TCAM, 
                                                           controlMsgCounter, 
                                                           RecoveryStatus, 
                                                           ingressPkt, 
                                                           statusMsg, 
                                                           switchObject, 
                                                           statusResolveMsg, 
                                                           swSeqChangedStatus, 
                                                           controller2Switch, 
                                                           switch2Controller, 
                                                           TEEventQueue, 
                                                           DAGQueue, 
                                                           IRQueueNIB, 
                                                           RCNIBEventQueue, 
                                                           RCSwSuspensionStatus, 
                                                           RCIRStatus, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           ScheduledIRs, 
                                                           seqWorkerIsBusy, 
                                                           nibEvent, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           setRemovableIRs, 
                                                           irsToUnschedule, 
                                                           unschedule, 
                                                           irToRemove, irToAdd, 
                                                           irsToConnect, 
                                                           irToConnect, 
                                                           seqEvent, 
                                                           toBeScheduledIRs, 
                                                           nextIR, currDAG, 
                                                           IRDoneSet, irSet, 
                                                           pickedIR, 
                                                           nextIRObjectToSend, 
                                                           index, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, msg, 
                                                           currentIRID >>

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ DAGState[prev_dag_id] = DAG_NONE
                                                /\ prev_dag_id' = DAGID
                                                /\ setRemovableIRs' = getSetRemovableIRs(SW \ currSetDownSw, nxtDAGVertices)
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                /\ UNCHANGED << sw_fail_ordering_var, 
                                                                switchStatus, 
                                                                installedIRs, 
                                                                TCAM, 
                                                                controlMsgCounter, 
                                                                RecoveryStatus, 
                                                                ingressPkt, 
                                                                statusMsg, 
                                                                switchObject, 
                                                                statusResolveMsg, 
                                                                swSeqChangedStatus, 
                                                                controller2Switch, 
                                                                switch2Controller, 
                                                                TEEventQueue, 
                                                                DAGEventQueue, 
                                                                DAGQueue, 
                                                                IRQueueNIB, 
                                                                RCNIBEventQueue, 
                                                                DAGState, 
                                                                RCSwSuspensionStatus, 
                                                                RCIRStatus, 
                                                                NIBIRStatus, 
                                                                SwSuspensionStatus, 
                                                                ScheduledIRs, 
                                                                seqWorkerIsBusy, 
                                                                nibEvent, 
                                                                topoChangeEvent, 
                                                                currSetDownSw, 
                                                                init, DAGID, 
                                                                nxtDAG, 
                                                                nxtDAGVertices, 
                                                                irsToUnschedule, 
                                                                unschedule, 
                                                                irToRemove, 
                                                                irToAdd, 
                                                                irsToConnect, 
                                                                irToConnect, 
                                                                seqEvent, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                currDAG, 
                                                                IRDoneSet, 
                                                                irSet, 
                                                                pickedIR, 
                                                                nextIRObjectToSend, 
                                                                index, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, msg, 
                                                                currentIRID >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF Cardinality(setRemovableIRs) > 0
                                                THEN /\ irToRemove' = (CHOOSE x \in setRemovableIRs: TRUE)
                                                     /\ setRemovableIRs' = setRemovableIRs \ {irToRemove'}
                                                     /\ irToAdd' = getDualOfIR(irToRemove')
                                                     /\ irsToConnect' = getSetIRsForSwitchInDAG(getSwitchForIR(irToRemove'), nxtDAG.dag.v)
                                                     /\ nxtDAG' = [nxtDAG EXCEPT !.dag.v = nxtDAG.dag.v \cup {irToAdd'}]
                                                     /\ pc' = [pc EXCEPT ![self] = "ConnectEdges"]
                                                     /\ UNCHANGED irsToUnschedule
                                                ELSE /\ irsToUnschedule' = nxtDAG.dag.v
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerUnscheduleIRsInDAG"]
                                                     /\ UNCHANGED << nxtDAG, 
                                                                     setRemovableIRs, 
                                                                     irToRemove, 
                                                                     irToAdd, 
                                                                     irsToConnect >>
                                          /\ UNCHANGED << sw_fail_ordering_var, 
                                                          switchStatus, 
                                                          installedIRs, TCAM, 
                                                          controlMsgCounter, 
                                                          RecoveryStatus, 
                                                          ingressPkt, 
                                                          statusMsg, 
                                                          switchObject, 
                                                          statusResolveMsg, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          DAGState, 
                                                          RCSwSuspensionStatus, 
                                                          RCIRStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          ScheduledIRs, 
                                                          seqWorkerIsBusy, 
                                                          nibEvent, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, 
                                                          nxtDAGVertices, 
                                                          unschedule, 
                                                          irToConnect, 
                                                          seqEvent, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRDoneSet, irSet, 
                                                          pickedIR, 
                                                          nextIRObjectToSend, 
                                                          index, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, 
                                                          currentIRID >>

ConnectEdges(self) == /\ pc[self] = "ConnectEdges"
                      /\ IF Cardinality(irsToConnect) > 0
                            THEN /\ irToConnect' = (CHOOSE x \in irsToConnect: TRUE)
                                 /\ irsToConnect' = irsToConnect \ {irToConnect'}
                                 /\ nxtDAG' = [nxtDAG EXCEPT !.dag.e = nxtDAG.dag.e \cup {<<irToAdd, irToConnect'>>}]
                                 /\ pc' = [pc EXCEPT ![self] = "ConnectEdges"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                 /\ UNCHANGED << nxtDAG, irsToConnect, 
                                                 irToConnect >>
                      /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                      installedIRs, TCAM, controlMsgCounter, 
                                      RecoveryStatus, ingressPkt, statusMsg, 
                                      switchObject, statusResolveMsg, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, IRQueueNIB, 
                                      RCNIBEventQueue, DAGState, 
                                      RCSwSuspensionStatus, RCIRStatus, 
                                      NIBIRStatus, SwSuspensionStatus, 
                                      ScheduledIRs, seqWorkerIsBusy, nibEvent, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, DAGID, nxtDAGVertices, 
                                      setRemovableIRs, irsToUnschedule, 
                                      unschedule, irToRemove, irToAdd, 
                                      seqEvent, toBeScheduledIRs, nextIR, 
                                      currDAG, IRDoneSet, irSet, pickedIR, 
                                      nextIRObjectToSend, index, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      msg, currentIRID >>

ControllerUnscheduleIRsInDAG(self) == /\ pc[self] = "ControllerUnscheduleIRsInDAG"
                                      /\ IF Cardinality(irsToUnschedule) > 0
                                            THEN /\ unschedule' = (CHOOSE x \in irsToUnschedule: TRUE)
                                                 /\ IF (getRCIRState(unschedule') # IR_NONE)
                                                       THEN /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![unschedule'] = FALSE]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED ScheduledIRs
                                                 /\ irsToUnschedule' = irsToUnschedule \ {unschedule'}
                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerUnscheduleIRsInDAG"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                                 /\ UNCHANGED << ScheduledIRs, 
                                                                 irsToUnschedule, 
                                                                 unschedule >>
                                      /\ UNCHANGED << sw_fail_ordering_var, 
                                                      switchStatus, 
                                                      installedIRs, TCAM, 
                                                      controlMsgCounter, 
                                                      RecoveryStatus, 
                                                      ingressPkt, statusMsg, 
                                                      switchObject, 
                                                      statusResolveMsg, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      IRQueueNIB, 
                                                      RCNIBEventQueue, 
                                                      DAGState, 
                                                      RCSwSuspensionStatus, 
                                                      RCIRStatus, NIBIRStatus, 
                                                      SwSuspensionStatus, 
                                                      seqWorkerIsBusy, 
                                                      nibEvent, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, DAGID, 
                                                      nxtDAG, nxtDAGVertices, 
                                                      setRemovableIRs, 
                                                      irToRemove, irToAdd, 
                                                      irsToConnect, 
                                                      irToConnect, seqEvent, 
                                                      toBeScheduledIRs, nextIR, 
                                                      currDAG, IRDoneSet, 
                                                      irSet, pickedIR, 
                                                      nextIRObjectToSend, 
                                                      index, monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      msg, currentIRID >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG.id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_NEW, dag_obj |-> nxtDAG]))
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                  /\ UNCHANGED << sw_fail_ordering_var, 
                                                  switchStatus, installedIRs, 
                                                  TCAM, controlMsgCounter, 
                                                  RecoveryStatus, ingressPkt, 
                                                  statusMsg, switchObject, 
                                                  statusResolveMsg, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  TEEventQueue, DAGQueue, 
                                                  IRQueueNIB, RCNIBEventQueue, 
                                                  RCSwSuspensionStatus, 
                                                  RCIRStatus, NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  ScheduledIRs, 
                                                  seqWorkerIsBusy, nibEvent, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  nxtDAGVertices, 
                                                  setRemovableIRs, 
                                                  irsToUnschedule, unschedule, 
                                                  irToRemove, irToAdd, 
                                                  irsToConnect, irToConnect, 
                                                  seqEvent, toBeScheduledIRs, 
                                                  nextIR, currDAG, IRDoneSet, 
                                                  irSet, pickedIR, 
                                                  nextIRObjectToSend, index, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, msg, 
                                                  currentIRID >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ConnectEdges(self)
                                         \/ ControllerUnscheduleIRsInDAG(self)
                                         \/ ControllerTESubmitNewDAG(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ Len(DAGEventQueue) > 0
                               /\ seqEvent' = Head(DAGEventQueue)
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ IF seqEvent'.type = DAG_NEW
                                     THEN /\ DAGQueue' = Append(DAGQueue, (seqEvent'.dag_obj))
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                          /\ UNCHANGED DAGState
                                     ELSE /\ IF seqWorkerIsBusy # FALSE
                                                THEN /\ pc' = [pc EXCEPT ![self] = "WaitForRCSeqWorkerTerminate"]
                                                     /\ UNCHANGED DAGState
                                                ELSE /\ DAGState' = [DAGState EXCEPT ![seqEvent'.id] = DAG_NONE]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                          /\ UNCHANGED DAGQueue
                               /\ UNCHANGED << sw_fail_ordering_var, 
                                               switchStatus, installedIRs, 
                                               TCAM, controlMsgCounter, 
                                               RecoveryStatus, ingressPkt, 
                                               statusMsg, switchObject, 
                                               statusResolveMsg, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               IRQueueNIB, RCNIBEventQueue, 
                                               RCSwSuspensionStatus, 
                                               RCIRStatus, NIBIRStatus, 
                                               SwSuspensionStatus, 
                                               ScheduledIRs, seqWorkerIsBusy, 
                                               nibEvent, topoChangeEvent, 
                                               currSetDownSw, prev_dag_id, 
                                               init, DAGID, nxtDAG, 
                                               nxtDAGVertices, setRemovableIRs, 
                                               irsToUnschedule, unschedule, 
                                               irToRemove, irToAdd, 
                                               irsToConnect, irToConnect, 
                                               toBeScheduledIRs, nextIR, 
                                               currDAG, IRDoneSet, irSet, 
                                               pickedIR, nextIRObjectToSend, 
                                               index, monitoringEvent, 
                                               setIRsToReset, resetIR, msg, 
                                               currentIRID >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ seqWorkerIsBusy = FALSE
                                     /\ DAGState' = [DAGState EXCEPT ![seqEvent.id] = DAG_NONE]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                     /\ UNCHANGED << sw_fail_ordering_var, 
                                                     switchStatus, 
                                                     installedIRs, TCAM, 
                                                     controlMsgCounter, 
                                                     RecoveryStatus, 
                                                     ingressPkt, statusMsg, 
                                                     switchObject, 
                                                     statusResolveMsg, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     IRQueueNIB, 
                                                     RCNIBEventQueue, 
                                                     RCSwSuspensionStatus, 
                                                     RCIRStatus, NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     ScheduledIRs, 
                                                     seqWorkerIsBusy, nibEvent, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, nxtDAGVertices, 
                                                     setRemovableIRs, 
                                                     irsToUnschedule, 
                                                     unschedule, irToRemove, 
                                                     irToAdd, irsToConnect, 
                                                     irToConnect, seqEvent, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRDoneSet, irSet, 
                                                     pickedIR, 
                                                     nextIRObjectToSend, index, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, currentIRID >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ Len(DAGQueue) > 0
                                 /\ currDAG' = Head(DAGQueue)
                                 /\ seqWorkerIsBusy' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                 /\ UNCHANGED << sw_fail_ordering_var, 
                                                 switchStatus, installedIRs, 
                                                 TCAM, controlMsgCounter, 
                                                 RecoveryStatus, ingressPkt, 
                                                 statusMsg, switchObject, 
                                                 statusResolveMsg, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 TEEventQueue, DAGEventQueue, 
                                                 DAGQueue, IRQueueNIB, 
                                                 RCNIBEventQueue, DAGState, 
                                                 RCSwSuspensionStatus, 
                                                 RCIRStatus, NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 ScheduledIRs, nibEvent, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 nxtDAGVertices, 
                                                 setRemovableIRs, 
                                                 irsToUnschedule, unschedule, 
                                                 irToRemove, irToAdd, 
                                                 irsToConnect, irToConnect, 
                                                 seqEvent, toBeScheduledIRs, 
                                                 nextIR, IRDoneSet, irSet, 
                                                 pickedIR, nextIRObjectToSend, 
                                                 index, monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 currentIRID >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF dagObjectShouldBeProcessed(currDAG)
                                              THEN /\ toBeScheduledIRs' = getSetIRsCanBeScheduledNext(currDAG.dag)
                                                   /\ toBeScheduledIRs' # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                   /\ UNCHANGED << seqWorkerIsBusy, 
                                                                   irSet >>
                                              ELSE /\ seqWorkerIsBusy' = FALSE
                                                   /\ irSet' = currDAG.dag.v
                                                   /\ IF allIRsInDAGInstalled(currDAG.dag)
                                                         THEN /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]
                                                   /\ UNCHANGED toBeScheduledIRs
                                        /\ UNCHANGED << sw_fail_ordering_var, 
                                                        switchStatus, 
                                                        installedIRs, TCAM, 
                                                        controlMsgCounter, 
                                                        RecoveryStatus, 
                                                        ingressPkt, statusMsg, 
                                                        switchObject, 
                                                        statusResolveMsg, 
                                                        swSeqChangedStatus, 
                                                        controller2Switch, 
                                                        switch2Controller, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, IRQueueNIB, 
                                                        RCNIBEventQueue, 
                                                        DAGState, 
                                                        RCSwSuspensionStatus, 
                                                        RCIRStatus, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        ScheduledIRs, nibEvent, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        DAGID, nxtDAG, 
                                                        nxtDAGVertices, 
                                                        setRemovableIRs, 
                                                        irsToUnschedule, 
                                                        unschedule, irToRemove, 
                                                        irToAdd, irsToConnect, 
                                                        irToConnect, seqEvent, 
                                                        nextIR, currDAG, 
                                                        IRDoneSet, pickedIR, 
                                                        nextIRObjectToSend, 
                                                        index, monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        msg, currentIRID >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ IF toBeScheduledIRs = {} \/ isDAGStale(currDAG.id)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                       /\ UNCHANGED << IRQueueNIB, 
                                                       ScheduledIRs, 
                                                       toBeScheduledIRs, 
                                                       nextIR, IRDoneSet >>
                                  ELSE /\ nextIR' = (CHOOSE x \in toBeScheduledIRs: TRUE)
                                       /\ LET destination == getSwitchForIR(nextIR') IN
                                            /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![nextIR'] = TRUE]
                                            /\ IF getIRType(nextIR') = INSTALL_FLOW
                                                  THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR'})
                                                  ELSE /\ IRDoneSet' = IRDoneSet \ {getDualOfIR(nextIR')}
                                            /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> nextIR', sw |-> destination]), tag |-> NADIR_NULL])
                                            /\ toBeScheduledIRs' = (toBeScheduledIRs\{nextIR'})
                                       /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                            /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                            installedIRs, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            ingressPkt, statusMsg, 
                                            switchObject, statusResolveMsg, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, 
                                            RCNIBEventQueue, DAGState, 
                                            RCSwSuspensionStatus, RCIRStatus, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            seqWorkerIsBusy, nibEvent, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, DAGID, nxtDAG, 
                                            nxtDAGVertices, setRemovableIRs, 
                                            irsToUnschedule, unschedule, 
                                            irToRemove, irToAdd, irsToConnect, 
                                            irToConnect, seqEvent, currDAG, 
                                            irSet, pickedIR, 
                                            nextIRObjectToSend, index, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, msg, currentIRID >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF Cardinality(irSet) > 0
                                     THEN /\ pickedIR' = (CHOOSE x \in irSet: TRUE)
                                          /\ IF (getIRType(pickedIR') = INSTALL_FLOW)
                                                THEN /\ IRDoneSet' = (IRDoneSet \cup {pickedIR'})
                                                ELSE /\ IRDoneSet' = IRDoneSet \ {pickedIR'}
                                          /\ irSet' = irSet \ {pickedIR'}
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]
                                          /\ UNCHANGED << IRDoneSet, irSet, 
                                                          pickedIR >>
                               /\ UNCHANGED << sw_fail_ordering_var, 
                                               switchStatus, installedIRs, 
                                               TCAM, controlMsgCounter, 
                                               RecoveryStatus, ingressPkt, 
                                               statusMsg, switchObject, 
                                               statusResolveMsg, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, RCNIBEventQueue, 
                                               DAGState, RCSwSuspensionStatus, 
                                               RCIRStatus, NIBIRStatus, 
                                               SwSuspensionStatus, 
                                               ScheduledIRs, seqWorkerIsBusy, 
                                               nibEvent, topoChangeEvent, 
                                               currSetDownSw, prev_dag_id, 
                                               init, DAGID, nxtDAG, 
                                               nxtDAGVertices, setRemovableIRs, 
                                               irsToUnschedule, unschedule, 
                                               irToRemove, irToAdd, 
                                               irsToConnect, irToConnect, 
                                               seqEvent, toBeScheduledIRs, 
                                               nextIR, currDAG, 
                                               nextIRObjectToSend, index, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, currentIRID >>

RemoveDagFromQueue(self) == /\ pc[self] = "RemoveDagFromQueue"
                            /\ DAGQueue' = Tail(DAGQueue)
                            /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                            /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                            installedIRs, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            ingressPkt, statusMsg, 
                                            switchObject, statusResolveMsg, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, IRQueueNIB, 
                                            RCNIBEventQueue, DAGState, 
                                            RCSwSuspensionStatus, RCIRStatus, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            ScheduledIRs, seqWorkerIsBusy, 
                                            nibEvent, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            DAGID, nxtDAG, nxtDAGVertices, 
                                            setRemovableIRs, irsToUnschedule, 
                                            unschedule, irToRemove, irToAdd, 
                                            irsToConnect, irToConnect, 
                                            seqEvent, toBeScheduledIRs, nextIR, 
                                            currDAG, IRDoneSet, irSet, 
                                            pickedIR, nextIRObjectToSend, 
                                            index, monitoringEvent, 
                                            setIRsToReset, resetIR, msg, 
                                            currentIRID >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ RemoveDagFromQueue(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ ExistsItemWithTag(IRQueueNIB, NADIR_NULL) \/ ExistsItemWithTag(IRQueueNIB, self)
                          /\ index' = GetItemIndexWithTag(IRQueueNIB, self)
                          /\ nextIRObjectToSend' = IRQueueNIB[index'].data
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![index'].tag = self]
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                          /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                          installedIRs, TCAM, 
                                          controlMsgCounter, RecoveryStatus, 
                                          ingressPkt, statusMsg, switchObject, 
                                          statusResolveMsg, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, RCNIBEventQueue, DAGState, 
                                          RCSwSuspensionStatus, RCIRStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          ScheduledIRs, seqWorkerIsBusy, 
                                          nibEvent, topoChangeEvent, 
                                          currSetDownSw, prev_dag_id, init, 
                                          DAGID, nxtDAG, nxtDAGVertices, 
                                          setRemovableIRs, irsToUnschedule, 
                                          unschedule, irToRemove, irToAdd, 
                                          irsToConnect, irToConnect, seqEvent, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRDoneSet, irSet, pickedIR, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, msg, currentIRID >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ IF isClearIR(nextIRObjectToSend.IR)
                                      THEN /\ IF isSwitchSuspended(nextIRObjectToSend.sw)
                                                 THEN /\ IF isClearIR(nextIRObjectToSend.IR)
                                                            THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                                        type |-> CLEAR_TCAM,
                                                                                                                                                                                                        flow |-> 0,
                                                                                                                                                                                                        to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                                        from |-> self[1]
                                                                                                                                                                                                    ]))]
                                                            ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                                        type |-> getIRType(nextIRObjectToSend.IR),
                                                                                                                                                                                                        flow |-> getPrimaryOfIR(nextIRObjectToSend.IR),
                                                                                                                                                                                                        to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                                        from |-> self[1]
                                                                                                                                                                                                    ]))]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED controller2Switch
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                      ELSE /\ IF getNIBIRState(nextIRObjectToSend.IR) \in {IR_NONE, IR_SENT}
                                                 THEN /\ IF isSwitchSuspended(nextIRObjectToSend.sw)
                                                            THEN /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_FAILED, IR |-> nextIRObjectToSend.IR, state |-> IR_NONE]))
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                                                 /\ UNCHANGED NIBIRStatus
                                                            ELSE /\ IF (isPrimary((nextIRObjectToSend.IR)))
                                                                       THEN /\ IF IR_SENT = IR_DONE /\ NIBIRStatus[(nextIRObjectToSend.IR)].dual = IR_DONE
                                                                                  THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend.IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                  ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend.IR)].primary = IR_SENT]
                                                                       ELSE /\ LET primary == getPrimaryOfIR((nextIRObjectToSend.IR)) IN
                                                                                 IF IR_SENT = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                                                    THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                    ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_SENT]
                                                                 /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> nextIRObjectToSend.IR, state |-> IR_SENT]))
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                                      /\ UNCHANGED << RCNIBEventQueue, 
                                                                      NIBIRStatus >>
                                           /\ UNCHANGED controller2Switch
                                /\ UNCHANGED << sw_fail_ordering_var, 
                                                switchStatus, installedIRs, 
                                                TCAM, controlMsgCounter, 
                                                RecoveryStatus, ingressPkt, 
                                                statusMsg, switchObject, 
                                                statusResolveMsg, 
                                                swSeqChangedStatus, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, DAGState, 
                                                RCSwSuspensionStatus, 
                                                RCIRStatus, SwSuspensionStatus, 
                                                ScheduledIRs, seqWorkerIsBusy, 
                                                nibEvent, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, DAGID, nxtDAG, 
                                                nxtDAGVertices, 
                                                setRemovableIRs, 
                                                irsToUnschedule, unschedule, 
                                                irToRemove, irToAdd, 
                                                irsToConnect, irToConnect, 
                                                seqEvent, toBeScheduledIRs, 
                                                nextIR, currDAG, IRDoneSet, 
                                                irSet, pickedIR, 
                                                nextIRObjectToSend, index, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, msg, currentIRID >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ IF isClearIR(nextIRObjectToSend.IR)
                                         THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                     type |-> CLEAR_TCAM,
                                                                                                                                                                                     flow |-> 0,
                                                                                                                                                                                     to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                     from |-> self[1]
                                                                                                                                                                                 ]))]
                                         ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                     type |-> getIRType(nextIRObjectToSend.IR),
                                                                                                                                                                                     flow |-> getPrimaryOfIR(nextIRObjectToSend.IR),
                                                                                                                                                                                     to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                     from |-> self[1]
                                                                                                                                                                                 ]))]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                   /\ UNCHANGED << sw_fail_ordering_var, 
                                                   switchStatus, installedIRs, 
                                                   TCAM, controlMsgCounter, 
                                                   RecoveryStatus, ingressPkt, 
                                                   statusMsg, switchObject, 
                                                   statusResolveMsg, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   RCNIBEventQueue, DAGState, 
                                                   RCSwSuspensionStatus, 
                                                   RCIRStatus, NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   ScheduledIRs, 
                                                   seqWorkerIsBusy, nibEvent, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   nxtDAGVertices, 
                                                   setRemovableIRs, 
                                                   irsToUnschedule, unschedule, 
                                                   irToRemove, irToAdd, 
                                                   irsToConnect, irToConnect, 
                                                   seqEvent, toBeScheduledIRs, 
                                                   nextIR, currDAG, IRDoneSet, 
                                                   irSet, pickedIR, 
                                                   nextIRObjectToSend, index, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   currentIRID >>

ControllerThreadRemoveIRFromQueue(self) == /\ pc[self] = "ControllerThreadRemoveIRFromQueue"
                                           /\ index' = GetFirstItemIndexWithTag(IRQueueNIB, self)
                                           /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index')
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                           /\ UNCHANGED << sw_fail_ordering_var, 
                                                           switchStatus, 
                                                           installedIRs, TCAM, 
                                                           controlMsgCounter, 
                                                           RecoveryStatus, 
                                                           ingressPkt, 
                                                           statusMsg, 
                                                           switchObject, 
                                                           statusResolveMsg, 
                                                           swSeqChangedStatus, 
                                                           controller2Switch, 
                                                           switch2Controller, 
                                                           TEEventQueue, 
                                                           DAGEventQueue, 
                                                           DAGQueue, 
                                                           RCNIBEventQueue, 
                                                           DAGState, 
                                                           RCSwSuspensionStatus, 
                                                           RCIRStatus, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           ScheduledIRs, 
                                                           seqWorkerIsBusy, 
                                                           nibEvent, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           prev_dag_id, init, 
                                                           DAGID, nxtDAG, 
                                                           nxtDAGVertices, 
                                                           setRemovableIRs, 
                                                           irsToUnschedule, 
                                                           unschedule, 
                                                           irToRemove, irToAdd, 
                                                           irsToConnect, 
                                                           irToConnect, 
                                                           seqEvent, 
                                                           toBeScheduledIRs, 
                                                           nextIR, currDAG, 
                                                           IRDoneSet, irSet, 
                                                           pickedIR, 
                                                           nextIRObjectToSend, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, msg, 
                                                           currentIRID >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadRemoveIRFromQueue(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ Len(swSeqChangedStatus) > 0
                                    /\ monitoringEvent' = Head(swSeqChangedStatus)
                                    /\ IF shouldSuspendRunningSw(monitoringEvent')
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF shouldClearSuspendedSw(monitoringEvent')
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerRequestTCAMClear"]
                                                     ELSE /\ IF shouldFreeSuspendedSw(monitoringEvent')
                                                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << sw_fail_ordering_var, 
                                                    switchStatus, installedIRs, 
                                                    TCAM, controlMsgCounter, 
                                                    RecoveryStatus, ingressPkt, 
                                                    statusMsg, switchObject, 
                                                    statusResolveMsg, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    IRQueueNIB, 
                                                    RCNIBEventQueue, DAGState, 
                                                    RCSwSuspensionStatus, 
                                                    RCIRStatus, NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    ScheduledIRs, 
                                                    seqWorkerIsBusy, nibEvent, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    nxtDAGVertices, 
                                                    setRemovableIRs, 
                                                    irsToUnschedule, 
                                                    unschedule, irToRemove, 
                                                    irToAdd, irsToConnect, 
                                                    irToConnect, seqEvent, 
                                                    toBeScheduledIRs, nextIR, 
                                                    currDAG, IRDoneSet, irSet, 
                                                    pickedIR, 
                                                    nextIRObjectToSend, index, 
                                                    setIRsToReset, resetIR, 
                                                    msg, currentIRID >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << sw_fail_ordering_var, 
                                                                   switchStatus, 
                                                                   installedIRs, 
                                                                   TCAM, 
                                                                   controlMsgCounter, 
                                                                   RecoveryStatus, 
                                                                   ingressPkt, 
                                                                   statusMsg, 
                                                                   switchObject, 
                                                                   statusResolveMsg, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   IRQueueNIB, 
                                                                   RCNIBEventQueue, 
                                                                   DAGState, 
                                                                   RCSwSuspensionStatus, 
                                                                   RCIRStatus, 
                                                                   NIBIRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   ScheduledIRs, 
                                                                   seqWorkerIsBusy, 
                                                                   nibEvent, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, DAGID, 
                                                                   nxtDAG, 
                                                                   nxtDAGVertices, 
                                                                   setRemovableIRs, 
                                                                   irsToUnschedule, 
                                                                   unschedule, 
                                                                   irToRemove, 
                                                                   irToAdd, 
                                                                   irsToConnect, 
                                                                   irToConnect, 
                                                                   seqEvent, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   currDAG, 
                                                                   IRDoneSet, 
                                                                   irSet, 
                                                                   pickedIR, 
                                                                   nextIRObjectToSend, 
                                                                   index, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, 
                                                                   currentIRID >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent.swID] = SW_SUSPEND]
                             /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]))
                             /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                             /\ UNCHANGED << sw_fail_ordering_var, 
                                             switchStatus, installedIRs, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             ingressPkt, statusMsg, 
                                             switchObject, statusResolveMsg, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, DAGState, 
                                             RCSwSuspensionStatus, RCIRStatus, 
                                             NIBIRStatus, ScheduledIRs, 
                                             seqWorkerIsBusy, nibEvent, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, nxtDAG, 
                                             nxtDAGVertices, setRemovableIRs, 
                                             irsToUnschedule, unschedule, 
                                             irToRemove, irToAdd, irsToConnect, 
                                             irToConnect, seqEvent, 
                                             toBeScheduledIRs, nextIR, currDAG, 
                                             IRDoneSet, irSet, pickedIR, 
                                             nextIRObjectToSend, index, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, currentIRID >>

ControllerRequestTCAMClear(self) == /\ pc[self] = "ControllerRequestTCAMClear"
                                    /\ IF ~existsMonitoringEventHigherNum(monitoringEvent)
                                          THEN /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> 0, sw |-> monitoringEvent.swID]), tag |-> NADIR_NULL])
                                          ELSE /\ TRUE
                                               /\ UNCHANGED IRQueueNIB
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << sw_fail_ordering_var, 
                                                    switchStatus, installedIRs, 
                                                    TCAM, controlMsgCounter, 
                                                    RecoveryStatus, ingressPkt, 
                                                    statusMsg, switchObject, 
                                                    statusResolveMsg, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    RCNIBEventQueue, DAGState, 
                                                    RCSwSuspensionStatus, 
                                                    RCIRStatus, NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    ScheduledIRs, 
                                                    seqWorkerIsBusy, nibEvent, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    nxtDAGVertices, 
                                                    setRemovableIRs, 
                                                    irsToUnschedule, 
                                                    unschedule, irToRemove, 
                                                    irToAdd, irsToConnect, 
                                                    irToConnect, seqEvent, 
                                                    toBeScheduledIRs, nextIR, 
                                                    currDAG, IRDoneSet, irSet, 
                                                    pickedIR, 
                                                    nextIRObjectToSend, index, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    msg, currentIRID >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent)
                                                THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                          /\ UNCHANGED << sw_fail_ordering_var, 
                                                          switchStatus, 
                                                          installedIRs, TCAM, 
                                                          controlMsgCounter, 
                                                          RecoveryStatus, 
                                                          ingressPkt, 
                                                          statusMsg, 
                                                          switchObject, 
                                                          statusResolveMsg, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          DAGState, 
                                                          RCSwSuspensionStatus, 
                                                          RCIRStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          ScheduledIRs, 
                                                          seqWorkerIsBusy, 
                                                          nibEvent, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, nxtDAG, 
                                                          nxtDAGVertices, 
                                                          setRemovableIRs, 
                                                          irsToUnschedule, 
                                                          unschedule, 
                                                          irToRemove, irToAdd, 
                                                          irsToConnect, 
                                                          irToConnect, 
                                                          seqEvent, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRDoneSet, irSet, 
                                                          pickedIR, 
                                                          nextIRObjectToSend, 
                                                          index, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, 
                                                          currentIRID >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ setIRsToReset' = getIRSetToReset(monitoringEvent.swID)
                           /\ IF (setIRsToReset' = {})
                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                           installedIRs, TCAM, 
                                           controlMsgCounter, RecoveryStatus, 
                                           ingressPkt, statusMsg, switchObject, 
                                           statusResolveMsg, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, IRQueueNIB, 
                                           RCNIBEventQueue, DAGState, 
                                           RCSwSuspensionStatus, RCIRStatus, 
                                           NIBIRStatus, SwSuspensionStatus, 
                                           ScheduledIRs, seqWorkerIsBusy, 
                                           nibEvent, topoChangeEvent, 
                                           currSetDownSw, prev_dag_id, init, 
                                           DAGID, nxtDAG, nxtDAGVertices, 
                                           setRemovableIRs, irsToUnschedule, 
                                           unschedule, irToRemove, irToAdd, 
                                           irsToConnect, irToConnect, seqEvent, 
                                           toBeScheduledIRs, nextIR, currDAG, 
                                           IRDoneSet, irSet, pickedIR, 
                                           nextIRObjectToSend, index, 
                                           monitoringEvent, resetIR, msg, 
                                           currentIRID >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ resetIR' = (CHOOSE x \in setIRsToReset: TRUE)
                     /\ setIRsToReset' = setIRsToReset \ {resetIR'}
                     /\ IF (isPrimary(resetIR'))
                           THEN /\ IF IR_NONE = IR_DONE /\ NIBIRStatus[resetIR'].dual = IR_DONE
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                      ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'].primary = IR_NONE]
                           ELSE /\ LET primary == getPrimaryOfIR(resetIR') IN
                                     IF IR_NONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                        THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                        ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_NONE]
                     /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> resetIR', state |-> IR_NONE]))
                     /\ IF setIRsToReset' = {}
                           THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                     /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                     installedIRs, TCAM, controlMsgCounter, 
                                     RecoveryStatus, ingressPkt, statusMsg, 
                                     switchObject, statusResolveMsg, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, IRQueueNIB, 
                                     DAGState, RCSwSuspensionStatus, 
                                     RCIRStatus, SwSuspensionStatus, 
                                     ScheduledIRs, seqWorkerIsBusy, nibEvent, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     nxtDAGVertices, setRemovableIRs, 
                                     irsToUnschedule, unschedule, irToRemove, 
                                     irToAdd, irsToConnect, irToConnect, 
                                     seqEvent, toBeScheduledIRs, nextIR, 
                                     currDAG, IRDoneSet, irSet, pickedIR, 
                                     nextIRObjectToSend, index, 
                                     monitoringEvent, msg, currentIRID >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent.swID] = SW_RUN]
                                   /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]))
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   /\ UNCHANGED << sw_fail_ordering_var, 
                                                   switchStatus, installedIRs, 
                                                   TCAM, controlMsgCounter, 
                                                   RecoveryStatus, ingressPkt, 
                                                   statusMsg, switchObject, 
                                                   statusResolveMsg, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   DAGState, 
                                                   RCSwSuspensionStatus, 
                                                   RCIRStatus, NIBIRStatus, 
                                                   ScheduledIRs, 
                                                   seqWorkerIsBusy, nibEvent, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   nxtDAGVertices, 
                                                   setRemovableIRs, 
                                                   irsToUnschedule, unschedule, 
                                                   irToRemove, irToAdd, 
                                                   irsToConnect, irToConnect, 
                                                   seqEvent, toBeScheduledIRs, 
                                                   nextIR, currDAG, IRDoneSet, 
                                                   irSet, pickedIR, 
                                                   nextIRObjectToSend, index, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   currentIRID >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerRequestTCAMClear(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSW(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ Len(switch2Controller) > 0
                                       /\ msg' = Head(switch2Controller)
                                       /\ IF msg'.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerProcessIRMod"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ForwardToEH"]
                                       /\ UNCHANGED << sw_fail_ordering_var, 
                                                       switchStatus, 
                                                       installedIRs, TCAM, 
                                                       controlMsgCounter, 
                                                       RecoveryStatus, 
                                                       ingressPkt, statusMsg, 
                                                       switchObject, 
                                                       statusResolveMsg, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       TEEventQueue, 
                                                       DAGEventQueue, DAGQueue, 
                                                       IRQueueNIB, 
                                                       RCNIBEventQueue, 
                                                       DAGState, 
                                                       RCSwSuspensionStatus, 
                                                       RCIRStatus, NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       ScheduledIRs, 
                                                       seqWorkerIsBusy, 
                                                       nibEvent, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       DAGID, nxtDAG, 
                                                       nxtDAGVertices, 
                                                       setRemovableIRs, 
                                                       irsToUnschedule, 
                                                       unschedule, irToRemove, 
                                                       irToAdd, irsToConnect, 
                                                       irToConnect, seqEvent, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, 
                                                       IRDoneSet, irSet, 
                                                       pickedIR, 
                                                       nextIRObjectToSend, 
                                                       index, monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       currentIRID >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ switch2Controller' = Tail(switch2Controller)
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                         /\ UNCHANGED << sw_fail_ordering_var, 
                                                         switchStatus, 
                                                         installedIRs, TCAM, 
                                                         controlMsgCounter, 
                                                         RecoveryStatus, 
                                                         ingressPkt, statusMsg, 
                                                         switchObject, 
                                                         statusResolveMsg, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         RCNIBEventQueue, 
                                                         DAGState, 
                                                         RCSwSuspensionStatus, 
                                                         RCIRStatus, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         ScheduledIRs, 
                                                         seqWorkerIsBusy, 
                                                         nibEvent, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         DAGID, nxtDAG, 
                                                         nxtDAGVertices, 
                                                         setRemovableIRs, 
                                                         irsToUnschedule, 
                                                         unschedule, 
                                                         irToRemove, irToAdd, 
                                                         irsToConnect, 
                                                         irToConnect, seqEvent, 
                                                         toBeScheduledIRs, 
                                                         nextIR, currDAG, 
                                                         IRDoneSet, irSet, 
                                                         pickedIR, 
                                                         nextIRObjectToSend, 
                                                         index, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, 
                                                         currentIRID >>

ControllerProcessIRMod(self) == /\ pc[self] = "ControllerProcessIRMod"
                                /\ currentIRID' = getIRIDForFlow(msg.flow, msg.type)
                                /\ IF (isPrimary(currentIRID'))
                                      THEN /\ IF IR_DONE = IR_DONE /\ NIBIRStatus[currentIRID'].dual = IR_DONE
                                                 THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIRID'] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                 ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIRID'].primary = IR_DONE]
                                      ELSE /\ LET primary == getPrimaryOfIR(currentIRID') IN
                                                IF IR_DONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                   THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                   ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_DONE]
                                /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> currentIRID', state |-> IR_DONE]))
                                /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                /\ UNCHANGED << sw_fail_ordering_var, 
                                                switchStatus, installedIRs, 
                                                TCAM, controlMsgCounter, 
                                                RecoveryStatus, ingressPkt, 
                                                statusMsg, switchObject, 
                                                statusResolveMsg, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, DAGState, 
                                                RCSwSuspensionStatus, 
                                                RCIRStatus, SwSuspensionStatus, 
                                                ScheduledIRs, seqWorkerIsBusy, 
                                                nibEvent, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, DAGID, nxtDAG, 
                                                nxtDAGVertices, 
                                                setRemovableIRs, 
                                                irsToUnschedule, unschedule, 
                                                irToRemove, irToAdd, 
                                                irsToConnect, irToConnect, 
                                                seqEvent, toBeScheduledIRs, 
                                                nextIR, currDAG, IRDoneSet, 
                                                irSet, pickedIR, 
                                                nextIRObjectToSend, index, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, msg >>

ForwardToEH(self) == /\ pc[self] = "ForwardToEH"
                     /\ swSeqChangedStatus' = Append(swSeqChangedStatus, msg)
                     /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                     /\ UNCHANGED << sw_fail_ordering_var, switchStatus, 
                                     installedIRs, TCAM, controlMsgCounter, 
                                     RecoveryStatus, ingressPkt, statusMsg, 
                                     switchObject, statusResolveMsg, 
                                     controller2Switch, switch2Controller, 
                                     TEEventQueue, DAGEventQueue, DAGQueue, 
                                     IRQueueNIB, RCNIBEventQueue, DAGState, 
                                     RCSwSuspensionStatus, RCIRStatus, 
                                     NIBIRStatus, SwSuspensionStatus, 
                                     ScheduledIRs, seqWorkerIsBusy, nibEvent, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     nxtDAGVertices, setRemovableIRs, 
                                     irsToUnschedule, unschedule, irToRemove, 
                                     irToAdd, irsToConnect, irToConnect, 
                                     seqEvent, toBeScheduledIRs, nextIR, 
                                     currDAG, IRDoneSet, irSet, pickedIR, 
                                     nextIRObjectToSend, index, 
                                     monitoringEvent, setIRsToReset, resetIR, 
                                     msg, currentIRID >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerProcessIRMod(self)
                                       \/ ForwardToEH(self)

Next == (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
           \/ (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
           \/ (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
           \/ (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(swProcess(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(swResolveFailure(self))
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))

\* END TRANSLATION 

(* We rephrase the definitions of `Next` and `Spec` for simplicity *)

SwitchProcessStep == (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
SwitchFailureStep == (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
SwitchResolveStep == (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))

SwitchModuleActions == 
    \/ SwitchProcessStep
    \/ SwitchFailureStep
    \/ SwitchResolveStep

NIBEHStep == (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
TEStep == (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
BOSSStep == (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
SEQStep == (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))

RCModuleActions ==
    \/ NIBEHStep
    \/ TEStep
    \/ BOSSStep
    \/ SEQStep

WPStep == (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
EHStep == (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
MSStep == (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))

OFCModuleActions ==
    \/ WPStep
    \/ EHStep
    \/ MSStep

ModuleNext ==
    \/ SwitchModuleActions
    \/ RCModuleActions
    \/ OFCModuleActions

SWModuleFairness == 
    /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(swProcess(self))
    /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(swFailureProc(self))
    /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(swResolveFailure(self))

RCModuleFairness ==
    /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(rcNibEventHandler(self))
    /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
    /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(controllerBossSequencer(self))
    /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))

OFCModuleFairness ==
    /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
    /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
    /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))

ModuleSpec == 
    /\ Init /\ [][ModuleNext]_vars
    /\ WF_vars(ModuleNext)
    /\ SWModuleFairness
    /\ RCModuleFairness
    /\ OFCModuleFairness

ENUM_SET_INSTALLER_STATUS == {INSTALLER_DOWN, INSTALLER_UP}
ENUM_SET_OF_CMD == {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM}
ENUM_SET_OF_ACK == {INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY}
ENUM_SET_SW_STATE == {SW_SUSPEND, SW_RUN}
ENUM_SET_IR_STATE == {IR_NONE, IR_SENT, IR_DONE}
ENUM_SET_DAG_STATE == {DAG_SUBMIT, DAG_NONE, DAG_STALE}
ENUM_MODULE_STATE == {Failed, NotFailed}

STRUCT_SET_RC_DAG == [v: SUBSET SCHEDULABLE_IR_SET, e: SUBSET (SCHEDULABLE_IR_SET \X SCHEDULABLE_IR_SET)]
STRUCT_SET_DAG_OBJECT == [id: DAG_ID_SET, dag: STRUCT_SET_RC_DAG]
STRUCT_IR == [IR: ALL_IR_SET, sw: SW]
STRUCT_IR_PAIR == [primary: ENUM_SET_IR_STATE, dual: ENUM_SET_IR_STATE]
STRUCT_SET_NIB_TAGGED_IR == [data: STRUCT_IR, tag: ({ofc0} \X CONTROLLER_THREAD_POOL) \cup {NADIR_NULL}]

MSG_SET_TIMEOUT == [swID: SW, num: Nat, type: {NIC_ASIC_DOWN, OFA_DOWN}]
MSG_SET_KEEPALIVE == [swID: SW, num: Nat, type: {KEEP_ALIVE, CLEARED_TCAM_SUCCESSFULLY}, installerStatus: ENUM_SET_INSTALLER_STATUS]
MSG_SET_OF_CMD == [from: {ofc0}, type: ENUM_SET_OF_CMD, to: SW, flow: Nat]
MSG_SET_OF_ACK == [to: {ofc0}, type: ENUM_SET_OF_ACK, from: SW, flow: Nat]
MSG_SET_SWITCH_EVENT == (MSG_SET_OF_ACK \cup MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE)
MSG_SET_TOPO_MOD == [type: {TOPO_MOD}, sw: SW, state: ENUM_SET_SW_STATE]
MSG_SET_IR_MOD == [type: {IR_MOD}, state: ENUM_SET_IR_STATE, IR: SCHEDULABLE_IR_SET]
MSG_SET_IR_FAIL == [type: {IR_FAILED}, state: ENUM_SET_IR_STATE, IR: SCHEDULABLE_IR_SET]
MSG_SET_TE_EVENT == (MSG_SET_TOPO_MOD \cup MSG_SET_IR_MOD \cup MSG_SET_IR_FAIL)
MSG_SET_DAG_STALE_NOTIF == [type: {DAG_STALE}, id: DAG_ID_SET]
MSG_SET_DAG_NEW_NOTIF == [type: {DAG_NEW}, dag_obj: STRUCT_SET_DAG_OBJECT]
MSG_SET_DAG_EVENT == (MSG_SET_DAG_STALE_NOTIF \cup MSG_SET_DAG_NEW_NOTIF)

STRUCT_SET_SWITCH_OBJECT == [sw: SW, partial: {0, 1}, transient: {0, 1}]
STRUCT_SET_SWITCH_STATUS == [
    cpu: ENUM_MODULE_STATE, nicAsic: ENUM_MODULE_STATE, 
    ofa: ENUM_MODULE_STATE, installer: ENUM_MODULE_STATE
]
STRUCT_RECOVERY_STATUS == [transient: {0, 1}, partial: {0, 1}]

TypeOK ==  /\ sw_fail_ordering_var \in Seq(SUBSET STRUCT_SET_SWITCH_OBJECT)
           /\ switchStatus \in [SW -> STRUCT_SET_SWITCH_STATUS]
           /\ installedIRs \in Seq(INSTALLABLE_IR_SET)
           /\ TCAM \in [SW -> SUBSET INSTALLABLE_IR_SET]
           /\ controlMsgCounter \in [SW -> Nat]
           /\ RecoveryStatus \in [SW -> STRUCT_RECOVERY_STATUS]
           /\ ingressPkt \in (MSG_SET_OF_CMD \cup {NADIR_NULL})
           /\ statusMsg \in (MSG_SET_SWITCH_EVENT \cup {NADIR_NULL})
           /\ switchObject \in (STRUCT_SET_SWITCH_OBJECT \cup {NADIR_NULL})
           /\ statusResolveMsg \in (MSG_SET_SWITCH_EVENT \cup {NADIR_NULL})
           /\ swSeqChangedStatus \in Seq(MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE)
           /\ switch2Controller \in Seq(MSG_SET_SWITCH_EVENT)
           /\ TEEventQueue \in Seq(MSG_SET_TE_EVENT)
           /\ DAGEventQueue \in Seq(MSG_SET_DAG_EVENT)
           /\ DAGQueue \in Seq(STRUCT_SET_DAG_OBJECT)
           /\ RCNIBEventQueue \in Seq(MSG_SET_TE_EVENT)
           /\ IRQueueNIB \in Seq(STRUCT_SET_NIB_TAGGED_IR)
           /\ controller2Switch \in [SW -> Seq(MSG_SET_OF_CMD)]
           /\ DAGState \in [DAG_ID_SET -> ENUM_SET_DAG_STATE]
           /\ RCIRStatus \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]
           /\ NIBIRStatus \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]
           /\ RCSwSuspensionStatus \in [SW -> ENUM_SET_SW_STATE]
           /\ seqWorkerIsBusy \in BOOLEAN 
           /\ SwSuspensionStatus \in [SW -> ENUM_SET_SW_STATE]
           /\ ScheduledIRs \in [SCHEDULABLE_IR_SET -> BOOLEAN]
           /\ nibEvent \in (MSG_SET_TE_EVENT \cup {NADIR_NULL})
           /\ topoChangeEvent \in (MSG_SET_TE_EVENT \cup {NADIR_NULL})
           /\ currSetDownSw \in SUBSET SW
           /\ prev_dag_id \in (DAG_ID_SET \cup {NADIR_NULL})
           /\ DAGID \in (DAG_ID_SET \cup {NADIR_NULL})
           /\ init \in BOOLEAN
           /\ nxtDAG \in (STRUCT_SET_DAG_OBJECT \cup {NADIR_NULL})
           /\ setRemovableIRs \in SUBSET SCHEDULABLE_IR_SET
           /\ nxtDAGVertices \in SUBSET SCHEDULABLE_IR_SET
           /\ irsToUnschedule \in SUBSET SCHEDULABLE_IR_SET
           /\ unschedule \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
           /\ irToRemove \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
           /\ irToAdd \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
           /\ irsToConnect \in SUBSET SCHEDULABLE_IR_SET
           /\ irToConnect \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
           /\ seqEvent \in (MSG_SET_DAG_EVENT \cup {NADIR_NULL})
           /\ toBeScheduledIRs \in SUBSET SCHEDULABLE_IR_SET
           /\ nextIR \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
           /\ currDAG \in (STRUCT_SET_DAG_OBJECT \cup {NADIR_NULL})
           /\ IRDoneSet \in SUBSET SCHEDULABLE_IR_SET
           /\ irSet \in SUBSET SCHEDULABLE_IR_SET
           /\ pickedIR \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
           /\ nextIRObjectToSend \in (STRUCT_IR \cup {NADIR_NULL})
           /\ index \in Nat
           /\ monitoringEvent \in (MSG_SET_KEEPALIVE \cup MSG_SET_TIMEOUT \cup {NADIR_NULL})
           /\ setIRsToReset \in SUBSET SCHEDULABLE_IR_SET
           /\ resetIR \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
           /\ msg \in (MSG_SET_SWITCH_EVENT \cup {NADIR_NULL})
           /\ currentIRID \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})

ConstantAssumptions == /\ MaxDAGID \in Nat
                       /\ MaxNumIRs \in Nat
                       /\ IR2SW \in [INSTALLABLE_IR_SET -> SW]
                       /\ TOPO_DAG_MAPPING \in [SUBSET SW -> STRUCT_SET_RC_DAG]
                       /\ SW_FAIL_ORDERING \in Seq(SUBSET STRUCT_SET_SWITCH_OBJECT)

ASSUME ConstantAssumptions

\* Local variables
\* Only the associated process can change these variables ...
swProcessLocals == <<ingressPkt, installedIRs>>
swFailureProcLocals == <<statusMsg, switchObject, sw_fail_ordering_var>>
swResolveFailureLocals == <<statusResolveMsg>>
rcNibEventHandlerLocals == <<nibEvent, RCIRStatus, RCSwSuspensionStatus>>
controllerTrafficEngineeringLocals == <<topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, setRemovableIRs, irsToUnschedule, unschedule, irToRemove, irToAdd, irsToConnect, irToConnect>>
controllerBossSequencerLocals == <<seqEvent>>
controllerSequencerLocals == <<toBeScheduledIRs, nextIR, currDAG, IRDoneSet, irSet, pickedIR, seqWorkerIsBusy>>
controllerWorkerThreadsLocals == <<nextIRObjectToSend, index>>
controllerEventHandlerLocals == <<monitoringEvent, setIRsToReset, resetIR, SwSuspensionStatus>>
controllerMonitoringServerLocals == <<msg, currentIRID>>

\* Module variables
\* Only the associated module can change these variables ...
swModuleVariables == <<switchStatus, TCAM, controlMsgCounter, RecoveryStatus>>
rcModuleVariables == <<ScheduledIRs, DAGState>>
ofcModuleVariables == <<NIBIRStatus>>

\* Queues ...
\* A bunch of process can change each of these variables ...
\* swSeqChangedStatus = <<>>,
\* controller2Switch = [x \in SW |-> <<>>],
\* switch2Controller = <<>>,
\* TEEventQueue = <<>>,
\* DAGEventQueue = <<>>,
\* DAGQueue = <<>>,
\* IRQueueNIB = <<>>,
\* RCNIBEventQueue = <<>>,

=============================================================================

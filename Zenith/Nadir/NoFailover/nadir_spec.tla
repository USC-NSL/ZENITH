------------------- MODULE nadir_spec -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, NadirTypes, NadirAckQueue

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


(*--fair algorithm zenithOfNadir
    variables 
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
        SetScheduledIRs = [y \in SW |-> {}],
        seqWorkerIsBusy = FALSE,

        eventHandlerCheckpoint = FALSE,
        eventHandlerTCAMCleared = FALSE,
        eventHandlerLastIRToReset = NADIR_NULL,
    define
        isPrimary(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN TRUE ELSE FALSE
        getDualOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN IntegerAsNadirID(NadirIDAsInteger(ir) + MaxNumIRs)
                                                                  ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
        getPrimaryOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN ir 
                                                                     ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
        getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
        isClearIR(idID) == IF NadirIDAsInteger(idID) = 0 THEN TRUE ELSE FALSE
        getIRType(irID) == IF NadirIDAsInteger(irID) \leq MaxNumIRs THEN INSTALL_FLOW
                                                  ELSE DELETE_FLOW
        getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                             ELSE IntegerAsNadirID(NadirIDAsInteger(flowID) + MaxNumIRs)
        
        getNIBIRState(irID) == IF isPrimary(irID) THEN NIBIRStatus[irID].primary
                                                  ELSE NIBIRStatus[getPrimaryOfIR(irID)].dual
        getRCIRState(irID) == IF isPrimary(irID) THEN RCIRStatus[irID].primary
                                                 ELSE RCIRStatus[getPrimaryOfIR(irID)].dual
        
        getSetUnschedulableIRs(nxtDAGV) == {x \in nxtDAGV: getRCIRState(x) # IR_NONE}
        getSetRemovableIRs(swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ getRCIRState(x) # IR_NONE
                                                                      \/ x \in SetScheduledIRs[getSwitchForIR(x)]
                                                                   /\ x \notin nxtDAGV
                                                                   /\ getSwitchForIR(x) \in swSet}
        getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: getSwitchForIR(x) = swID}
        isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                           /\ getRCIRState(y) # IR_DONE
        getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ getRCIRState(x) = IR_NONE
                                                           /\ isDependencySatisfied(DAG, x)
                                                           /\ RCSwSuspensionStatus[getSwitchForIR(x)] = SW_RUN
                                                           /\ x \notin SetScheduledIRs[getSwitchForIR(x)]}
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
                                            /\ \/ eventHandlerCheckpoint = TRUE
                                               \/ SwSuspensionStatus[monEvent.swID] = SW_RUN
        
        shouldClearSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                            /\ monEvent.installerStatus = INSTALLER_UP
                                            /\ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND
        
        shouldFreeSuspendedSw(monEvent) == /\ monEvent.type = CLEARED_TCAM_SUCCESSFULLY
                                           /\ monEvent.installerStatus = INSTALLER_UP 
                                           /\ \/ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND 
                                              \/ eventHandlerCheckpoint = TRUE
                                        
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ getSwitchForIR(x) = SID
                                                     /\ getNIBIRState(x) # IR_NONE}
    
        isFinished == \A x \in 1..MaxNumIRs: getNIBIRState(x) = IR_DONE
        allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getRCIRState(y) = IR_DONE
                                                      /\ \/ getRCIRState(getDualOfIR(y)) # IR_NONE
                                                         \/ getDualOfIR(y) \in SetScheduledIRs[getSwitchForIR(y)]
        dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag)
                                                    /\ ~isDAGStale(dagObject.id)
                                                 \/ ~allIRsInDAGAreStable(dagObject.dag)
        
        RECURSIVE AddDeleteDAGIRDoneSet(_, _)
        AddDeleteDAGIRDoneSet(irSet, doneSet) ==
            IF Cardinality(irSet) = 0
                THEN doneSet
                ELSE LET pickedIR == CHOOSE x \in irSet: TRUE
                     IN IF getIRType(pickedIR) = INSTALL_FLOW
                            THEN AddDeleteDAGIRDoneSet(irSet \ {pickedIR}, doneSet \cup {pickedIR})
                            ELSE AddDeleteDAGIRDoneSet(irSet \ {pickedIR}, doneSet \ {pickedIR})
        
        RECURSIVE _GetDependencyEdges(_, _, _)
        _GetDependencyEdges(irToRemove, irsToConnect, edges) == 
            IF Cardinality(irsToConnect) = 0
                THEN edges
                ELSE LET irToConnect == CHOOSE x \in irsToConnect: TRUE
                     IN _GetDependencyEdges(irToRemove, irsToConnect \ {irToConnect}, edges \cup {<<getDualOfIR(irToRemove), irToConnect>>})
        
        GetDependencyEdges(irToRemove, irsToConnect) == _GetDependencyEdges(irToRemove, irsToConnect, {})
        
        RECURSIVE CreateTEDAG(_, _)
        CreateTEDAG(irsToRemove, dag) == 
            IF Cardinality(irsToRemove) = 0
                THEN dag
                ELSE 
                    LET irToRemove == CHOOSE x \in irsToRemove: TRUE
                    IN CreateTEDAG(
                            irsToRemove \ {irToRemove}, 
                            [
                                v |-> (dag.v \cup {getDualOfIR(irToRemove)}), 
                                e |-> (dag.e \cup GetDependencyEdges(
                                    irToRemove, 
                                    getSetIRsForSwitchInDAG(getSwitchForIR(irToRemove), dag.v)
                                ))
                            ])
    end define

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

    macro unscheduleDagIRs(dagIRSet)
    begin
        SetScheduledIRs := [x \in SW |-> (SetScheduledIRs[x] \ getSetUnschedulableIRs(dagIRSet))];
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

    fair process rcNibEventHandler \in ({rc0} \X {NIB_EVENT_HANDLER})
    variables event = NADIR_NULL;
    begin
    RCSNIBEventHndlerProc:
    while TRUE do
        NadirFIFOPeek(RCNIBEventQueue, event);
        if (event.type = TOPO_MOD) then
            if RCSwSuspensionStatus[event.sw] # event.state then    
                RCSwSuspensionStatus[event.sw] := event.state;
                NadirFIFOPut(TEEventQueue, event);
            end if;
        elsif (event.type = IR_MOD) then
            if getRCIRState(event.IR) # event.state then
                setRCIRState(event.IR, event.state);
                with destination = getSwitchForIR(event.IR) do
                    SetScheduledIRs[destination] := SetScheduledIRs[destination] \ {event.IR};    
                end with;
            end if;
        elsif (event.type = IR_FAILED) then
            with destination = getSwitchForIR(event.IR) do
                SetScheduledIRs[destination] := SetScheduledIRs[destination] \ {event.IR};    
            end with;
        end if;
        NadirFIFOPop(RCNIBEventQueue);
    end while;
    end process

    fair process controllerTrafficEngineering \in ({rc0} \X {CONT_TE})
    variables topoChangeEvent = NADIR_NULL, currSetDownSw = {}, prev_dag_id = NADIR_NULL, init = TRUE,
        DAGID = NADIR_NULL, nxtDAG = NADIR_NULL, nxtDAGVertices = {}, setRemovableIRs = {};
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
            nxtDAG.dag := CreateTEDAG(setRemovableIRs, nxtDAG.dag);
            unscheduleDagIRs(nxtDAG.dag.v);
            
        ControllerTESubmitNewDAG:
            DAGState[nxtDAG.id] := DAG_SUBMIT;
            NadirFIFOPut(DAGEventQueue, [type |-> DAG_NEW, dag_obj |-> nxtDAG]);
    end while;
    end process

    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    variables seqEvent = NADIR_NULL;
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
    variables toBeScheduledIRs = {}, nextIR = NADIR_NULL, currDAG = NADIR_NULL, IRDoneSet = {};
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
                            SetScheduledIRs[destination] := SetScheduledIRs[destination] \cup {nextIR};
                            
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
            
            if allIRsInDAGInstalled(currDAG.dag) then
                IRDoneSet := AddDeleteDAGIRDoneSet(currDAG.dag.v, IRDoneSet);
            end if;
            RemoveDagFromQueue:
                NadirFIFOPop(DAGQueue);
    end while;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRObjectToSend = NADIR_NULL, index = 0;
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
    variables monitoringEvent = NADIR_NULL, setIRsToReset = {}, resetIR = NADIR_NULL;
    begin
    ControllerEventHandlerProc:
    while TRUE do 
        NadirFIFOPeek(swSeqChangedStatus, monitoringEvent);

        if shouldSuspendRunningSw(monitoringEvent) then
            ControllerSuspendSW:
                eventHandlerCheckpoint := TRUE;
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
                if ~existsMonitoringEventHigherNum(monitoringEvent) /\ ~eventHandlerTCAMCleared then
                    getIRsToBeChecked:
                        setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                        if (setIRsToReset = {}) then
                            goto ControllerFreeSuspendedSW;
                        end if;

                    ResetAllIRs:
                        while TRUE do
                            resetIR := CHOOSE x \in setIRsToReset: TRUE;
                            setIRsToReset := setIRsToReset \ {resetIR};
                            eventHandlerLastIRToReset := resetIR;
                            
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
                eventHandlerCheckpoint := TRUE;
                eventHandlerLastIRToReset := NADIR_NULL;
                SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                eventHandlerTCAMCleared := TRUE;
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]
                );
        end if;

        ControllerEvenHanlderRemoveEventFromQueue:
            eventHandlerCheckpoint := FALSE;
            eventHandlerTCAMCleared := FALSE;
            eventHandlerLastIRToReset := NADIR_NULL;
            NadirFIFOPop(swSeqChangedStatus);
    end while;

    ControllerEventHandlerStateReconciliation:
        with lastIR = eventHandlerLastIRToReset do
            if lastIR # NADIR_NULL then
                setNIBIRState(lastIR, IR_NONE);
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> IR_MOD, IR |-> lastIR, state |-> IR_NONE]
                );
            end if;
        end with;
        goto ControllerEventHandlerProc;
    end process

    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = NADIR_NULL, irID = NADIR_NULL;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        NadirFIFOPeek(switch2Controller, msg);
        
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            ControllerProcessIRMod:
                irID := getIRIDForFlow(msg.flow, msg.type);
                setNIBIRState(irID, IR_DONE);
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
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

ENUM_SET_INSTALLER_STATUS == {INSTALLER_DOWN, INSTALLER_UP}
ENUM_SET_OF_CMD == {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM}
ENUM_SET_OF_ACK == {INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY}
ENUM_SET_SW_STATE == {SW_SUSPEND, SW_RUN}
ENUM_SET_IR_STATE == {IR_NONE, IR_SENT, IR_DONE}
ENUM_SET_DAG_STATE == {DAG_SUBMIT, DAG_NONE, DAG_STALE}
NadirEnumSet == ("EnumInstallerStatus" :> ENUM_SET_INSTALLER_STATUS) @@
                ("EnumOpenFlowCMD" :> ENUM_SET_OF_CMD) @@
                ("EnumOpenFlowACK" :> ENUM_SET_OF_ACK) @@
                ("EnumSwitchState" :> ENUM_SET_SW_STATE) @@
                ("EnumIRState" :> ENUM_SET_IR_STATE) @@
                ("EnumDAGState" :> ENUM_SET_DAG_STATE)

STRUCT_SET_RC_DAG == [v: SUBSET NADIR_INT_ID_SET, e: SUBSET (NADIR_INT_ID_SET \X NADIR_INT_ID_SET)]
STRUCT_SET_DAG_OBJECT == [id: NADIR_INT_ID_SET, dag: STRUCT_SET_RC_DAG]
STRUCT_IR == [IR: NADIR_INT_ID_SET, sw: SW]
STRUCT_IR_PAIR == [primary: ENUM_SET_IR_STATE, dual: ENUM_SET_IR_STATE]
STRUCT_SET_NIB_TAGGED_IR == [data: STRUCT_IR, tag: NadirNullable(OFCProcSet)]
NadirStructSet == ("StructRCDAG" :> STRUCT_SET_RC_DAG) @@
                  ("StructDAGObject" :> STRUCT_SET_DAG_OBJECT) @@
                  ("StructIR" :> STRUCT_IR) @@
                  ("StructIRPair" :> STRUCT_IR_PAIR) @@
                  ("StructNIBTaggedIR" :> STRUCT_SET_NIB_TAGGED_IR)

MSG_SET_TIMEOUT == [swID: SW, num: Nat, type: {NIC_ASIC_DOWN, OFA_DOWN}]
MSG_SET_KEEPALIVE == [swID: SW, num: Nat, type: {KEEP_ALIVE, CLEARED_TCAM_SUCCESSFULLY}, installerStatus: ENUM_SET_INSTALLER_STATUS]
MSG_SET_OF_CMD == [from: {ofc0}, type: ENUM_SET_OF_CMD, to: SW, flow: Nat]
MSG_SET_OF_ACK == [to: {ofc0}, type: ENUM_SET_OF_ACK, from: SW, flow: Nat]
MSG_SET_SWITCH_EVENT == (MSG_SET_OF_ACK \cup MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE)
MSG_SET_TOPO_MOD == [type: {TOPO_MOD}, sw: SW, state: ENUM_SET_SW_STATE]
MSG_SET_IR_MOD == [type: {IR_MOD}, state: ENUM_SET_IR_STATE, IR: NADIR_INT_ID_SET]
MSG_SET_IR_FAIL == [type: {IR_FAILED}, state: ENUM_SET_IR_STATE, IR: NADIR_INT_ID_SET]
MSG_SET_TE_EVENT == (MSG_SET_TOPO_MOD \cup MSG_SET_IR_MOD \cup MSG_SET_IR_FAIL)
MSG_SET_DAG_STALE_NOTIF == [type: {DAG_STALE}, id: NADIR_INT_ID_SET]
MSG_SET_DAG_NEW_NOTIF == [type: {DAG_NEW}, dag_obj: STRUCT_SET_DAG_OBJECT]
MSG_SET_DAG_EVENT == (MSG_SET_DAG_STALE_NOTIF \cup MSG_SET_DAG_NEW_NOTIF)
NadirMessageSet == ("MessageSwitchTimeout" :> MSG_SET_TIMEOUT) @@
                   ("MessageSwitchKeepalive" :> MSG_SET_KEEPALIVE) @@
                   ("MessageOpenFlowCMD" :> MSG_SET_OF_CMD) @@
                   ("MessageOpenFlowACK" :> MSG_SET_OF_ACK) @@
                   ("MessageSwitchEvent" :> MSG_SET_SWITCH_EVENT) @@
                   ("MessageTopoMod" :> MSG_SET_TOPO_MOD) @@
                   ("MessageIRMod" :> MSG_SET_IR_MOD) @@
                   ("MessageIRFail" :> MSG_SET_IR_FAIL) @@
                   ("MessageTEEvent" :> MSG_SET_TE_EVENT) @@
                   ("MessageDAGStaleNotif" :> MSG_SET_DAG_STALE_NOTIF) @@
                   ("MessageDAGNewNotif" :> MSG_SET_DAG_NEW_NOTIF) @@
                   ("MessageDAGEvent" :> MSG_SET_DAG_EVENT)

TypeOK ==  /\ NadirFIFO(MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE, swSeqChangedStatus)
           /\ NadirFIFO(MSG_SET_SWITCH_EVENT, switch2Controller)
           /\ NadirFIFO(MSG_SET_TE_EVENT, TEEventQueue)
           /\ NadirFIFO(MSG_SET_DAG_EVENT, DAGEventQueue)
           /\ NadirFIFO(STRUCT_SET_DAG_OBJECT, DAGQueue)
           /\ NadirFIFO(MSG_SET_TE_EVENT, RCNIBEventQueue)
           /\ NadirAckQueue(STRUCT_SET_NIB_TAGGED_IR, IRQueueNIB)
           /\ NadirFanoutFIFO(SW, MSG_SET_OF_CMD, controller2Switch)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, ENUM_SET_DAG_STATE, DAGState)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, STRUCT_IR_PAIR, RCIRStatus)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, STRUCT_IR_PAIR, NIBIRStatus)
           /\ NadirFunctionTypeCheck(SW, ENUM_SET_SW_STATE, RCSwSuspensionStatus)
           /\ seqWorkerIsBusy \in BOOLEAN 
           /\ eventHandlerCheckpoint \in BOOLEAN 
           /\ eventHandlerTCAMCleared \in BOOLEAN
           /\ eventHandlerLastIRToReset \in NadirNullable(NADIR_INT_ID_SET)
           /\ NadirFunctionTypeCheck(SW, ENUM_SET_SW_STATE, SwSuspensionStatus)
           /\ NadirFunctionTypeCheck(SW, SUBSET NADIR_INT_ID_SET, SetScheduledIRs)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_TE_EVENT), event)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_TE_EVENT), topoChangeEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET SW, currSetDownSw)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), prev_dag_id)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), DAGID)
           /\ NadirLocalVariableTypeCheck(BOOLEAN, init)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_DAG_OBJECT), nxtDAG)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, setRemovableIRs)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, nxtDAGVertices)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_DAG_EVENT), seqEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, toBeScheduledIRs)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), nextIR)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_DAG_OBJECT), currDAG)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, IRDoneSet)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_IR), nextIRObjectToSend)
           /\ NadirLocalVariableTypeCheck(Nat, index)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_KEEPALIVE \cup MSG_SET_TIMEOUT), monitoringEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, setIRsToReset)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), resetIR)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_SWITCH_EVENT), msg)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), irID)

NadirConstantAssumptions == /\ MaxDAGID \in Nat
                            /\ MaxNumIRs \in Nat
                            /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, SW, IR2SW)
                            /\ NadirFunctionTypeCheck(SUBSET SW, STRUCT_SET_RC_DAG, TOPO_DAG_MAPPING)

ASSUME NadirConstantAssumptions

=============================================================================

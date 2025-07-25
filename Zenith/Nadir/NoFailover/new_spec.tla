------------------- MODULE new_spec -------------------
\* EXTENDS Integers, Sequences, FiniteSets, TLC, NadirTypes, NadirAckQueue

\* CONSTANTS SW
\* CONSTANTS ofc0, rc0
\* CONSTANTS CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_TE, CONT_MONITOR
\* CONSTANTS CONTROLLER_THREAD_POOL, CONT_OFC_MONITOR, CONT_EVENT, NIB_EVENT_HANDLER
\* CONSTANTS IR_NONE, IR_SENT, IR_DONE
\* CONSTANTS SW_RUN, SW_SUSPEND
\* CONSTANTS DAG_STALE, DAG_NEW, DAG_SUBMIT, DAG_NONE
\* CONSTANTS TOPO_MOD, IR_MOD
\* CONSTANTS STATUS_START_SCHEDULING, STATUS_LOCKING, STATUS_SENT_DONE, START_RESET_IR
\* CONSTANTS INSTALL_FLOW, DELETE_FLOW, INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY, KEEP_ALIVE
\* CONSTANTS NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN, INSTALLER_UP
\* CONSTANTS MaxDAGID, MaxNumIRs
\* CONSTANTS TOPO_DAG_MAPPING, IR2SW
\* CONSTANTS RCProcSet, OFCProcSet, ContProcSet

EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag, NadirTypes, NadirAckQueue

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR, CONT_EVENT, 
          WATCH_DOG, NIB_EVENT_HANDLER, CONT_TE
CONSTANTS TOPO_DAG_MAPPING, IR2SW
CONSTANTS RCProcSet, OFCProcSet, ContProcSet

ASSUME MaxNumIRs >= Cardinality({TOPO_DAG_MAPPING[i]: i \in DOMAIN TOPO_DAG_MAPPING})
ASSUME {"ofc0", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE
ASSUME \A x \in DOMAIN TOPO_DAG_MAPPING: /\ "v" \in DOMAIN TOPO_DAG_MAPPING[x]
                                         /\ "e" \in DOMAIN TOPO_DAG_MAPPING[x]
ASSUME \A x \in 1..MaxNumIRs: x \in DOMAIN IR2SW


(*--fair algorithm stateConsistency
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
        RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE],
        RCSwSuspensionStatus = [y \in SW |-> SW_RUN],
        NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE],
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        rcInternalState = [x \in RCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]],
        ofcInternalState = [x \in OFCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]],
        SetScheduledIRs = [y \in SW |-> {}],
        seqWorkerIsBusy = FALSE
    define
        getDualOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN IntegerAsNadirID(NadirIDAsInteger(ir) + MaxNumIRs)
                                                                  ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
        getPrimaryOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN ir 
                                                                     ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
        getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
        getIRType(irID) == IF NadirIDAsInteger(irID) \leq MaxNumIRs THEN INSTALL_FLOW
                                                                    ELSE DELETE_FLOW
        getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                             ELSE IntegerAsNadirID(NadirIDAsInteger(flowID) + MaxNumIRs)
        getSetRemovableIRs(swSet, nxtDAGV) == {x \in IntegerSetAsNadirIDSet(1..MaxNumIRs): /\ \/ RCIRStatus[x] # IR_NONE
                                                                                              \/ x \in SetScheduledIRs[getSwitchForIR(x)]
                                                                                           /\ x \notin nxtDAGV
                                                                                           /\ getSwitchForIR(x) \in swSet}
        getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: getSwitchForIR(x) = swID}
        isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                           /\ RCIRStatus[y] # IR_DONE
        getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ RCIRStatus[x] = IR_NONE
                                                           /\ isDependencySatisfied(DAG, x)
                                                           /\ RCSwSuspensionStatus[getSwitchForIR(x)] = SW_RUN
                                                           /\ x \notin SetScheduledIRs[getSwitchForIR(x)]}
        allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: RCIRStatus[y] # IR_DONE
        isDAGStale(id) == DAGState[id] # DAG_SUBMIT
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                        /\ swSeqChangedStatus[x].num > monEvent.num
        shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                                     \/ monEvent.type = NIC_ASIC_DOWN
                                     \/ /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.installerStatus = INSTALLER_DOWN
        canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.installerStatus = INSTALLER_UP
        getIRSetToReset(SID) == {x \in IntegerSetAsNadirIDSet(1..MaxNumIRs): /\ getSwitchForIR(x) = SID
                                                                             /\ NIBIRStatus[x] # IR_NONE}
        isFinished == \A x \in IntegerSetAsNadirIDSet(1..MaxNumIRs): NIBIRStatus[x] = IR_DONE
        allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getIRType(y) = INSTALL_FLOW
                                                      /\ RCIRStatus[y] = IR_DONE
                                                      /\ getDualOfIR(y) \in DOMAIN RCIRStatus
                                                      /\ \/ RCIRStatus[getDualOfIR(y)] # IR_NONE
                                                         \/ getDualOfIR(y) \in SetScheduledIRs[IR2SW[y]]
        dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag) 
                                                    /\ ~isDAGStale(dagObject.id) 
                                                 \/ ~allIRsInDAGAreStable(dagObject.dag)
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

    macro controllerSendIR(irID)
    begin
        with destination = getSwitchForIR(irID) do
            NadirFanoutFIFOPut(
                controller2Switch,
                destination,
                [type |-> getIRType(irID), flow |-> getPrimaryOfIR(irID), to |-> destination, from |-> self[1]]
            );
        end with;
    end macro;

    macro prepareDeletionIR(forWhat, DID)
    begin
        if (DID \notin DOMAIN RCIRStatus) then
            RCIRStatus    := RCIRStatus    @@ (DID :> IR_NONE);
            NIBIRStatus   := NIBIRStatus   @@ (DID :> IR_NONE);
        else
            RCIRStatus[DID] := IR_NONE;
            NIBIRStatus[DID] := IR_NONE;
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
        SetScheduledIRs := [x \in SW |-> (SetScheduledIRs[x] \ dagIRSet)];
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
            if RCIRStatus[event.IR] # event.state then
                RCIRStatus[event.IR] := event.state;
                with destination = getSwitchForIR(event.IR) do
                    SetScheduledIRs[destination] := SetScheduledIRs[destination] \ {event.IR};    
                end with;
            end if;
        end if;
        NadirFIFOPop(RCNIBEventQueue);
    end while;
    end process

    fair process controllerTrafficEngineering \in ({rc0} \X {CONT_TE})
    variables topoChangeEvent = NADIR_NULL, currSetDownSw = {}, prev_dag_id = NADIR_NULL, init = 1,
        DAGID = NADIR_NULL, nxtDAG = NADIR_NULL, deleterID = NADIR_NULL, setRemovableIRs = {}, 
        currIR = NADIR_NULL, currIRInDAG = NADIR_NULL, nxtDAGVertices = {}, setIRsInDAG = {}, 
        prev_dag = NADIR_NULL;
    begin
    ControllerTEProc:
    while TRUE do
        if init = 1 then
            goto ControllerTEComputeDagBasedOnTopo;
        else
            NadirFIFOPeek(TEEventQueue, topoChangeEvent);
        end if;
        
        ControllerTEEventProcessing:
        while init # 1 do
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
            if prev_dag = nxtDAG.dag then
                goto ControllerTEProc;
            else
                nxtDAGVertices := nxtDAG.dag.v;
                if init = 0 then
                    DAGState[prev_dag_id] := DAG_STALE;
                    NadirFIFOPut(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id]);
                
                    ControllerTEWaitForStaleDAGToBeRemoved:
                        await DAGState[prev_dag_id] = DAG_NONE;
                        prev_dag_id := DAGID;
                        prev_dag := nxtDAG.dag;
                        setRemovableIRs := getSetRemovableIRs(SW \ currSetDownSw, nxtDAGVertices);
                else
                    init := 0;
                    prev_dag_id := DAGID;
                end if;
            end if;
            
        ControllerTERemoveUnnecessaryIRs:
            while setRemovableIRs # {} do
                currIR := CHOOSE x \in setRemovableIRs: TRUE;
                setRemovableIRs := setRemovableIRs \ {currIR};
                deleterID := getDualOfIR(currIR);
                prepareDeletionIR(currIR, deleterID);
                nxtDAG.dag.v := nxtDAG.dag.v \cup {deleterID};
                setIRsInDAG := getSetIRsForSwitchInDAG(getSwitchForIR(currIR), nxtDAGVertices); 
                
                ControllerTEAddEdge:
                while setIRsInDAG # {} do
                    currIRInDAG := CHOOSE x \in setIRsInDAG: TRUE;
                    setIRsInDAG := setIRsInDAG \ {currIRInDAG};
                    nxtDAG.dag.e := nxtDAG.dag.e \cup {<<deleterID, currIRInDAG>>};
                end while;
            end while;
            unscheduleDagIRs(nxtDAG.dag.v);
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
    variables toBeScheduledIRs = {}, nextIR = NADIR_NULL, currDAG = NADIR_NULL, IRSet = {}, IRDoneSet = {};
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
                    nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                    rcInternalState[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
                    with destination = getSwitchForIR(nextIR) do
                        SetScheduledIRs[destination] := SetScheduledIRs[destination] \cup {nextIR};
                    end with;
                    
                    AddDeleteIRIRDoneSet:
                        if getIRType(nextIR) = INSTALL_FLOW then
                            IRDoneSet := IRDoneSet \cup {nextIR};
                        else
                            IRDoneSet := IRDoneSet \ {getDualOfIR(nextIR)}
                        end if;

                    ScheduleTheIR: 
                        NadirAckQueuePut(IRQueueNIB, nextIR);
                        toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                        rcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL];
                
                        if toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then
                            goto ControllerWorkerSeqScheduleDAG;
                        end if;
                end while;                                                
            end while;

            seqWorkerIsBusy := FALSE;
            IRSet := currDAG.dag.v;
            
            if allIRsInDAGInstalled(currDAG.dag) then
                AddDeleteDAGIRDoneSet:
                while IRSet # {} do
                    nextIR := CHOOSE x \in IRSet: TRUE;
                    if getIRType(nextIR) = INSTALL_FLOW then
                        IRDoneSet := IRDoneSet \cup {nextIR};
                    else
                        IRDoneSet := IRDoneSet \ {getDualOfIR(nextIR)};
                    end if;
                    IRSet := IRSet \ {nextIR};
                end while; 
            end if;
            RemoveDagFromQueue:
                NadirFIFOPop(DAGQueue);
    end while;
    
    ControllerSeqStateReconciliation:
        if(rcInternalState[self].type = STATUS_START_SCHEDULING) then
            with destination = getSwitchForIR(rcInternalState[self].next) do
                SetScheduledIRs[destination] := SetScheduledIRs[destination] \ {rcInternalState[self].next};
            end with;
        end if;
        goto ControllerWorkerSeqProc;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRIDToSend = NADIR_NULL, index = 0;
    begin
    ControllerThread:
    while TRUE do
        NadirAckQueueGet(IRQueueNIB, self, index, nextIRIDToSend);
        ofcInternalState[self] := [type |-> STATUS_LOCKING, next |-> nextIRIDToSend];
        
        ControllerThreadSendIR:
            if ~isSwitchSuspended(getSwitchForIR(nextIRIDToSend)) /\ NIBIRStatus[nextIRIDToSend] = IR_NONE then
                NIBIRStatus[nextIRIDToSend] := IR_SENT;
                NadirFIFOPut(
                    RCNIBEventQueue, 
                    [type |-> IR_MOD, IR |-> nextIRIDToSend, state |-> IR_SENT]
                );
                controllerSendIR(nextIRIDToSend);
            end if;
            ofcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL];
            NadirAckQueueAck(IRQueueNIB, self, index);
    end while;
    
    ControllerThreadStateReconciliation:
        if (ofcInternalState[self].type = STATUS_LOCKING) then
            if (NIBIRStatus[ofcInternalState[self].next] = IR_SENT) then
                NIBIRStatus[ofcInternalState[self].next] := IR_NONE;
            end if;
        end if;
        goto ControllerThread;
    end process

    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = NADIR_NULL, setIRsToReset = {}, resetIR = NADIR_NULL;
    begin
    ControllerEventHandlerProc:
    while TRUE do 
        NadirFIFOPeek(swSeqChangedStatus, monitoringEvent);

        if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            ControllerSuspendSW:
                SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]
                );
                
        elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
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
                        NIBIRStatus[resetIR] := IR_NONE;
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
                ofcInternalState[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]
                );
        end if;

        ControllerEvenHanlderRemoveEventFromQueue:
            ofcInternalState[self] := [type |-> NADIR_NULL, sw |-> NADIR_NULL]; 
            NadirFIFOPop(swSeqChangedStatus);
    end while;

    ControllerEventHandlerStateReconciliation:
        if (ofcInternalState[self].type = START_RESET_IR) then
            SwSuspensionStatus[ofcInternalState[self].sw] := SW_SUSPEND;
            NadirFIFOPut(
                RCNIBEventQueue,
                [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]
            );
        end if;
        goto ControllerEventHandlerProc;
    end process

    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = NADIR_NULL, irID = NADIR_NULL, removedIR = NADIR_NULL;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        NadirFIFOPeek(switch2Controller, msg);
        irID := getIRIDForFlow(msg.flow, msg.type);
        
        ControllerUpdateIRDone:
            if NIBIRStatus[irID] = IR_SENT then
                NIBIRStatus[irID] := IR_DONE; 
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                );
            end if;

            removedIR := getDualOfIR(irID);
            if removedIR \in DOMAIN NIBIRStatus then 
                ControllerMonUpdateIRNone:
                    if NIBIRStatus[removedIR] = IR_DONE then
                        NIBIRStatus[removedIR] := IR_NONE; 
                        NadirFIFOPut(
                            RCNIBEventQueue,
                            [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]
                        );
                    end if;
            end if;
        
        MonitoringServerRemoveFromQueue:
            NadirFIFOPop(switch2Controller);
    end while
    end process   
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "dab8c851")
VARIABLES swSeqChangedStatus, controller2Switch, switch2Controller, 
          TEEventQueue, DAGEventQueue, DAGQueue, IRQueueNIB, RCNIBEventQueue, 
          DAGState, RCIRStatus, RCSwSuspensionStatus, NIBIRStatus, 
          SwSuspensionStatus, rcInternalState, ofcInternalState, 
          SetScheduledIRs, seqWorkerIsBusy, pc

(* define statement *)
getDualOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN IntegerAsNadirID(NadirIDAsInteger(ir) + MaxNumIRs)
                                                          ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
getPrimaryOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN ir
                                                             ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
getIRType(irID) == IF NadirIDAsInteger(irID) \leq MaxNumIRs THEN INSTALL_FLOW
                                                            ELSE DELETE_FLOW
getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                     ELSE IntegerAsNadirID(NadirIDAsInteger(flowID) + MaxNumIRs)
getSetRemovableIRs(swSet, nxtDAGV) == {x \in IntegerSetAsNadirIDSet(1..MaxNumIRs): /\ \/ RCIRStatus[x] # IR_NONE
                                                                                      \/ x \in SetScheduledIRs[getSwitchForIR(x)]
                                                                                   /\ x \notin nxtDAGV
                                                                                   /\ getSwitchForIR(x) \in swSet}
getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: getSwitchForIR(x) = swID}
isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                   /\ RCIRStatus[y] # IR_DONE
getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ RCIRStatus[x] = IR_NONE
                                                   /\ isDependencySatisfied(DAG, x)
                                                   /\ RCSwSuspensionStatus[getSwitchForIR(x)] = SW_RUN
                                                   /\ x \notin SetScheduledIRs[getSwitchForIR(x)]}
allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: RCIRStatus[y] # IR_DONE
isDAGStale(id) == DAGState[id] # DAG_SUBMIT
isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                /\ swSeqChangedStatus[x].num > monEvent.num
shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                             \/ monEvent.type = NIC_ASIC_DOWN
                             \/ /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.installerStatus = INSTALLER_DOWN
canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.installerStatus = INSTALLER_UP
getIRSetToReset(SID) == {x \in IntegerSetAsNadirIDSet(1..MaxNumIRs): /\ getSwitchForIR(x) = SID
                                                                     /\ NIBIRStatus[x] # IR_NONE}
isFinished == \A x \in IntegerSetAsNadirIDSet(1..MaxNumIRs): NIBIRStatus[x] = IR_DONE
allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getIRType(y) = INSTALL_FLOW
                                              /\ RCIRStatus[y] = IR_DONE
                                              /\ getDualOfIR(y) \in DOMAIN RCIRStatus
                                              /\ \/ RCIRStatus[getDualOfIR(y)] # IR_NONE
                                                 \/ getDualOfIR(y) \in SetScheduledIRs[IR2SW[y]]
dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag)
                                            /\ ~isDAGStale(dagObject.id)
                                         \/ ~allIRsInDAGAreStable(dagObject.dag)

VARIABLES event, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, 
          nxtDAG, deleterID, setRemovableIRs, currIR, currIRInDAG, 
          nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, toBeScheduledIRs, 
          nextIR, currDAG, IRSet, IRDoneSet, nextIRIDToSend, index, 
          monitoringEvent, setIRsToReset, resetIR, msg, irID, removedIR

vars == << swSeqChangedStatus, controller2Switch, switch2Controller, 
           TEEventQueue, DAGEventQueue, DAGQueue, IRQueueNIB, RCNIBEventQueue, 
           DAGState, RCIRStatus, RCSwSuspensionStatus, NIBIRStatus, 
           SwSuspensionStatus, rcInternalState, ofcInternalState, 
           SetScheduledIRs, seqWorkerIsBusy, pc, event, topoChangeEvent, 
           currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, deleterID, 
           setRemovableIRs, currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, 
           prev_dag, seqEvent, toBeScheduledIRs, nextIR, currDAG, IRSet, 
           IRDoneSet, nextIRIDToSend, index, monitoringEvent, setIRsToReset, 
           resetIR, msg, irID, removedIR >>

ProcSet == (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))

Init == (* Global variables *)
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ TEEventQueue = <<>>
        /\ DAGEventQueue = <<>>
        /\ DAGQueue = <<>>
        /\ IRQueueNIB = <<>>
        /\ RCNIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ rcInternalState = [x \in RCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]]
        /\ ofcInternalState = [x \in OFCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ seqWorkerIsBusy = FALSE
        (* Process rcNibEventHandler *)
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> NADIR_NULL]
        (* Process controllerTrafficEngineering *)
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
        (* Process controllerBossSequencer *)
        /\ seqEvent = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ IRDoneSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        (* Process controllerWorkerThreads *)
        /\ nextIRIDToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ removedIR = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ Len(RCNIBEventQueue) > 0
                               /\ event' = [event EXCEPT ![self] = Head(RCNIBEventQueue)]
                               /\ IF (event'[self].type = TOPO_MOD)
                                     THEN /\ IF RCSwSuspensionStatus[event'[self].sw] # event'[self].state
                                                THEN /\ RCSwSuspensionStatus' = [RCSwSuspensionStatus EXCEPT ![event'[self].sw] = event'[self].state]
                                                     /\ TEEventQueue' = Append(TEEventQueue, event'[self])
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << TEEventQueue, 
                                                                     RCSwSuspensionStatus >>
                                          /\ UNCHANGED << RCIRStatus, 
                                                          SetScheduledIRs >>
                                     ELSE /\ IF (event'[self].type = IR_MOD)
                                                THEN /\ IF RCIRStatus[event'[self].IR] # event'[self].state
                                                           THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![event'[self].IR] = event'[self].state]
                                                                /\ LET destination == getSwitchForIR(event'[self].IR) IN
                                                                     SetScheduledIRs' = [SetScheduledIRs EXCEPT ![destination] = SetScheduledIRs[destination] \ {event'[self].IR}]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << RCIRStatus, 
                                                                                SetScheduledIRs >>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << RCIRStatus, 
                                                                     SetScheduledIRs >>
                                          /\ UNCHANGED << TEEventQueue, 
                                                          RCSwSuspensionStatus >>
                               /\ RCNIBEventQueue' = Tail(RCNIBEventQueue)
                               /\ pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]
                               /\ UNCHANGED << swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, DAGState, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               seqWorkerIsBusy, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               toBeScheduledIRs, nextIR, 
                                               currDAG, IRSet, IRDoneSet, 
                                               nextIRIDToSend, index, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, irID, removedIR >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ IF init[self] = 1
                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                     /\ UNCHANGED topoChangeEvent
                                ELSE /\ Len(TEEventQueue) > 0
                                     /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, IRQueueNIB, 
                                          RCNIBEventQueue, DAGState, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          rcInternalState, ofcInternalState, 
                                          SetScheduledIRs, seqWorkerIsBusy, 
                                          event, currSetDownSw, prev_dag_id, 
                                          init, DAGID, nxtDAG, deleterID, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, toBeScheduledIRs, 
                                          nextIR, currDAG, IRSet, IRDoneSet, 
                                          nextIRIDToSend, index, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, msg, irID, removedIR >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF init[self] # 1
                                           THEN /\ IF topoChangeEvent[self] = NADIR_NULL
                                                      THEN /\ IF Len(TEEventQueue) > 0
                                                                 THEN /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                                                 ELSE /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = NADIR_NULL]
                                                           /\ IF topoChangeEvent'[self] = NADIR_NULL
                                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                                           /\ UNCHANGED << TEEventQueue, 
                                                                           currSetDownSw >>
                                                      ELSE /\ IF topoChangeEvent[self].state = SW_SUSPEND
                                                                 THEN /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \cup {topoChangeEvent[self].sw}]
                                                                 ELSE /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \ {topoChangeEvent[self].sw}]
                                                           /\ TEEventQueue' = Tail(TEEventQueue)
                                                           /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = NADIR_NULL]
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                /\ UNCHANGED << TEEventQueue, 
                                                                topoChangeEvent, 
                                                                currSetDownSw >>
                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     DAGEventQueue, DAGQueue, 
                                                     IRQueueNIB, 
                                                     RCNIBEventQueue, DAGState, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     SetScheduledIRs, 
                                                     seqWorkerIsBusy, event, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRSet, IRDoneSet, 
                                                     nextIRIDToSend, index, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, irID, removedIR >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ IF DAGID[self] = NADIR_NULL
                                                 THEN /\ DAGID' = [DAGID EXCEPT ![self] = 1]
                                                 ELSE /\ DAGID' = [DAGID EXCEPT ![self] = (DAGID[self] % MaxDAGID) + 1]
                                           /\ nxtDAG' = [nxtDAG EXCEPT ![self] = [id |-> DAGID'[self], dag |-> TOPO_DAG_MAPPING[currSetDownSw[self]]]]
                                           /\ IF prev_dag[self] = nxtDAG'[self].dag
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                                      /\ UNCHANGED << DAGEventQueue, 
                                                                      DAGState, 
                                                                      prev_dag_id, 
                                                                      init, 
                                                                      nxtDAGVertices >>
                                                 ELSE /\ nxtDAGVertices' = [nxtDAGVertices EXCEPT ![self] = nxtDAG'[self].dag.v]
                                                      /\ IF init[self] = 0
                                                            THEN /\ DAGState' = [DAGState EXCEPT ![prev_dag_id[self]] = DAG_STALE]
                                                                 /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_STALE, id |-> prev_dag_id[self]]))
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                                                 /\ UNCHANGED << prev_dag_id, 
                                                                                 init >>
                                                            ELSE /\ init' = [init EXCEPT ![self] = 0]
                                                                 /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID'[self]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                                 /\ UNCHANGED << DAGEventQueue, 
                                                                                 DAGState >>
                                           /\ UNCHANGED << swSeqChangedStatus, 
                                                           controller2Switch, 
                                                           switch2Controller, 
                                                           TEEventQueue, 
                                                           DAGQueue, 
                                                           IRQueueNIB, 
                                                           RCNIBEventQueue, 
                                                           RCIRStatus, 
                                                           RCSwSuspensionStatus, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           rcInternalState, 
                                                           ofcInternalState, 
                                                           SetScheduledIRs, 
                                                           seqWorkerIsBusy, 
                                                           event, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           deleterID, 
                                                           setRemovableIRs, 
                                                           currIR, currIRInDAG, 
                                                           setIRsInDAG, 
                                                           prev_dag, seqEvent, 
                                                           toBeScheduledIRs, 
                                                           nextIR, currDAG, 
                                                           IRSet, IRDoneSet, 
                                                           nextIRIDToSend, 
                                                           index, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, msg, irID, 
                                                           removedIR >>

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ DAGState[prev_dag_id[self]] = DAG_NONE
                                                /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID[self]]
                                                /\ prev_dag' = [prev_dag EXCEPT ![self] = nxtDAG[self].dag]
                                                /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = getSetRemovableIRs(SW \ currSetDownSw[self], nxtDAGVertices[self])]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                /\ UNCHANGED << swSeqChangedStatus, 
                                                                controller2Switch, 
                                                                switch2Controller, 
                                                                TEEventQueue, 
                                                                DAGEventQueue, 
                                                                DAGQueue, 
                                                                IRQueueNIB, 
                                                                RCNIBEventQueue, 
                                                                DAGState, 
                                                                RCIRStatus, 
                                                                RCSwSuspensionStatus, 
                                                                NIBIRStatus, 
                                                                SwSuspensionStatus, 
                                                                rcInternalState, 
                                                                ofcInternalState, 
                                                                SetScheduledIRs, 
                                                                seqWorkerIsBusy, 
                                                                event, 
                                                                topoChangeEvent, 
                                                                currSetDownSw, 
                                                                init, DAGID, 
                                                                nxtDAG, 
                                                                deleterID, 
                                                                currIR, 
                                                                currIRInDAG, 
                                                                nxtDAGVertices, 
                                                                setIRsInDAG, 
                                                                seqEvent, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                currDAG, IRSet, 
                                                                IRDoneSet, 
                                                                nextIRIDToSend, 
                                                                index, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, msg, 
                                                                irID, 
                                                                removedIR >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF setRemovableIRs[self] # {}
                                                THEN /\ currIR' = [currIR EXCEPT ![self] = CHOOSE x \in setRemovableIRs[self]: TRUE]
                                                     /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = setRemovableIRs[self] \ {currIR'[self]}]
                                                     /\ deleterID' = [deleterID EXCEPT ![self] = getDualOfIR(currIR'[self])]
                                                     /\ IF (deleterID'[self] \notin DOMAIN RCIRStatus)
                                                           THEN /\ RCIRStatus' = RCIRStatus    @@ (deleterID'[self] :> IR_NONE)
                                                                /\ NIBIRStatus' = NIBIRStatus   @@ (deleterID'[self] :> IR_NONE)
                                                           ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                                /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                     /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {deleterID'[self]}]
                                                     /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(getSwitchForIR(currIR'[self]), nxtDAGVertices[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                                     /\ UNCHANGED << DAGEventQueue, 
                                                                     DAGState, 
                                                                     SetScheduledIRs >>
                                                ELSE /\ SetScheduledIRs' = [x \in SW |-> (SetScheduledIRs[x] \ (nxtDAG[self].dag.v))]
                                                     /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                                     /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_NEW, dag_obj |-> nxtDAG[self]]))
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                                     /\ UNCHANGED << RCIRStatus, 
                                                                     NIBIRStatus, 
                                                                     nxtDAG, 
                                                                     deleterID, 
                                                                     setRemovableIRs, 
                                                                     currIR, 
                                                                     setIRsInDAG >>
                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          RCSwSuspensionStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          seqWorkerIsBusy, 
                                                          event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          prev_dag, seqEvent, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRSet, IRDoneSet, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID, 
                                                          removedIR >>

ControllerTEAddEdge(self) == /\ pc[self] = "ControllerTEAddEdge"
                             /\ IF setIRsInDAG[self] # {}
                                   THEN /\ currIRInDAG' = [currIRInDAG EXCEPT ![self] = CHOOSE x \in setIRsInDAG[self]: TRUE]
                                        /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = setIRsInDAG[self] \ {currIRInDAG'[self]}]
                                        /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.e = nxtDAG[self].dag.e \cup {<<deleterID[self], currIRInDAG'[self]>>}]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                        /\ UNCHANGED << nxtDAG, currIRInDAG, 
                                                        setIRsInDAG >>
                             /\ UNCHANGED << swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, RCNIBEventQueue, 
                                             DAGState, RCIRStatus, 
                                             RCSwSuspensionStatus, NIBIRStatus, 
                                             SwSuspensionStatus, 
                                             rcInternalState, ofcInternalState, 
                                             SetScheduledIRs, seqWorkerIsBusy, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             DAGID, deleterID, setRemovableIRs, 
                                             currIR, nxtDAGVertices, prev_dag, 
                                             seqEvent, toBeScheduledIRs, 
                                             nextIR, currDAG, IRSet, IRDoneSet, 
                                             nextIRIDToSend, index, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, irID, removedIR >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTEAddEdge(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ Len(DAGEventQueue) > 0
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue)]
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ IF seqEvent'[self].type = DAG_NEW
                                     THEN /\ DAGQueue' = Append(DAGQueue, (seqEvent'[self].dag_obj))
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                          /\ UNCHANGED DAGState
                                     ELSE /\ IF seqWorkerIsBusy # FALSE
                                                THEN /\ pc' = [pc EXCEPT ![self] = "WaitForRCSeqWorkerTerminate"]
                                                     /\ UNCHANGED DAGState
                                                ELSE /\ DAGState' = [DAGState EXCEPT ![seqEvent'[self].id] = DAG_NONE]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                          /\ UNCHANGED DAGQueue
                               /\ UNCHANGED << swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               IRQueueNIB, RCNIBEventQueue, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, 
                                               seqWorkerIsBusy, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, 
                                               toBeScheduledIRs, nextIR, 
                                               currDAG, IRSet, IRDoneSet, 
                                               nextIRIDToSend, index, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, irID, removedIR >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ seqWorkerIsBusy = FALSE
                                     /\ DAGState' = [DAGState EXCEPT ![seqEvent[self].id] = DAG_NONE]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     IRQueueNIB, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     SetScheduledIRs, 
                                                     seqWorkerIsBusy, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRSet, IRDoneSet, 
                                                     nextIRIDToSend, index, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, irID, removedIR >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ Len(DAGQueue) > 0
                                 /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue)]
                                 /\ seqWorkerIsBusy' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                 /\ UNCHANGED << swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 TEEventQueue, DAGEventQueue, 
                                                 DAGQueue, IRQueueNIB, 
                                                 RCNIBEventQueue, DAGState, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 rcInternalState, 
                                                 ofcInternalState, 
                                                 SetScheduledIRs, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 deleterID, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, 
                                                 toBeScheduledIRs, nextIR, 
                                                 IRSet, IRDoneSet, 
                                                 nextIRIDToSend, index, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 irID, removedIR >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF dagObjectShouldBeProcessed(currDAG[self])
                                              THEN /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(currDAG[self].dag)]
                                                   /\ toBeScheduledIRs'[self] # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                   /\ UNCHANGED << seqWorkerIsBusy, 
                                                                   IRSet >>
                                              ELSE /\ seqWorkerIsBusy' = FALSE
                                                   /\ IRSet' = [IRSet EXCEPT ![self] = currDAG[self].dag.v]
                                                   /\ IF allIRsInDAGInstalled(currDAG[self].dag)
                                                         THEN /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]
                                                   /\ UNCHANGED toBeScheduledIRs
                                        /\ UNCHANGED << swSeqChangedStatus, 
                                                        controller2Switch, 
                                                        switch2Controller, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, IRQueueNIB, 
                                                        RCNIBEventQueue, 
                                                        DAGState, RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        rcInternalState, 
                                                        ofcInternalState, 
                                                        SetScheduledIRs, event, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        DAGID, nxtDAG, 
                                                        deleterID, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, nextIR, 
                                                        currDAG, IRDoneSet, 
                                                        nextIRIDToSend, index, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        msg, irID, removedIR >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                            /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> STATUS_START_SCHEDULING, next |-> nextIR'[self]]]
                            /\ LET destination == getSwitchForIR(nextIR'[self]) IN
                                 SetScheduledIRs' = [SetScheduledIRs EXCEPT ![destination] = SetScheduledIRs[destination] \cup {nextIR'[self]}]
                            /\ pc' = [pc EXCEPT ![self] = "AddDeleteIRIRDoneSet"]
                            /\ UNCHANGED << swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, 
                                            IRQueueNIB, RCNIBEventQueue, 
                                            DAGState, RCIRStatus, 
                                            RCSwSuspensionStatus, NIBIRStatus, 
                                            SwSuspensionStatus, 
                                            ofcInternalState, seqWorkerIsBusy, 
                                            event, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            DAGID, nxtDAG, deleterID, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            toBeScheduledIRs, currDAG, IRSet, 
                                            IRDoneSet, nextIRIDToSend, index, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, msg, irID, removedIR >>

AddDeleteIRIRDoneSet(self) == /\ pc[self] = "AddDeleteIRIRDoneSet"
                              /\ IF getIRType(nextIR[self]) = INSTALL_FLOW
                                    THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \cup {nextIR[self]}]
                                    ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \ {getDualOfIR(nextIR[self])}]
                              /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                              /\ UNCHANGED << swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, 
                                              IRQueueNIB, RCNIBEventQueue, 
                                              DAGState, RCIRStatus, 
                                              RCSwSuspensionStatus, 
                                              NIBIRStatus, SwSuspensionStatus, 
                                              rcInternalState, 
                                              ofcInternalState, 
                                              SetScheduledIRs, seqWorkerIsBusy, 
                                              event, topoChangeEvent, 
                                              currSetDownSw, prev_dag_id, init, 
                                              DAGID, nxtDAG, deleterID, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              toBeScheduledIRs, nextIR, 
                                              currDAG, IRSet, nextIRIDToSend, 
                                              index, monitoringEvent, 
                                              setIRsToReset, resetIR, msg, 
                                              irID, removedIR >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> nextIR[self], tag |-> NADIR_NULL])
                       /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
                       /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                       /\ IF toBeScheduledIRs'[self] = {} \/ isDAGStale(currDAG[self].id)
                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                       /\ UNCHANGED << swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, TEEventQueue, 
                                       DAGEventQueue, DAGQueue, 
                                       RCNIBEventQueue, DAGState, RCIRStatus, 
                                       RCSwSuspensionStatus, NIBIRStatus, 
                                       SwSuspensionStatus, ofcInternalState, 
                                       SetScheduledIRs, seqWorkerIsBusy, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, DAGID, nxtDAG, 
                                       deleterID, setRemovableIRs, currIR, 
                                       currIRInDAG, nxtDAGVertices, 
                                       setIRsInDAG, prev_dag, seqEvent, nextIR, 
                                       currDAG, IRSet, IRDoneSet, 
                                       nextIRIDToSend, index, monitoringEvent, 
                                       setIRsToReset, resetIR, msg, irID, 
                                       removedIR >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {}
                                     THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF getIRType(nextIR'[self]) = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \cup {nextIR'[self]}]
                                                ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \ {getDualOfIR(nextIR'[self])}]
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]
                                          /\ UNCHANGED << nextIR, IRSet, 
                                                          IRDoneSet >>
                               /\ UNCHANGED << swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, RCNIBEventQueue, 
                                               DAGState, RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, 
                                               seqWorkerIsBusy, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               toBeScheduledIRs, currDAG, 
                                               nextIRIDToSend, index, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, irID, removedIR >>

RemoveDagFromQueue(self) == /\ pc[self] = "RemoveDagFromQueue"
                            /\ DAGQueue' = Tail(DAGQueue)
                            /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                            /\ UNCHANGED << swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, IRQueueNIB, 
                                            RCNIBEventQueue, DAGState, 
                                            RCIRStatus, RCSwSuspensionStatus, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            rcInternalState, ofcInternalState, 
                                            SetScheduledIRs, seqWorkerIsBusy, 
                                            event, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            DAGID, nxtDAG, deleterID, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            toBeScheduledIRs, nextIR, currDAG, 
                                            IRSet, IRDoneSet, nextIRIDToSend, 
                                            index, monitoringEvent, 
                                            setIRsToReset, resetIR, msg, irID, 
                                            removedIR >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ IF (rcInternalState[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ LET destination == getSwitchForIR(rcInternalState[self].next) IN
                                                          SetScheduledIRs' = [SetScheduledIRs EXCEPT ![destination] = SetScheduledIRs[destination] \ {rcInternalState[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          DAGState, RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          seqWorkerIsBusy, 
                                                          event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, nxtDAG, 
                                                          deleterID, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, seqEvent, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRSet, IRDoneSet, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID, 
                                                          removedIR >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteIRIRDoneSet(self)
                                \/ ScheduleTheIR(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ RemoveDagFromQueue(self)
                                \/ ControllerSeqStateReconciliation(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ ExistsItemWithTag(IRQueueNIB, NADIR_NULL) \/ ExistsItemWithTag(IRQueueNIB, self)
                          /\ index' = [index EXCEPT ![self] = GetItemIndexWithTag(IRQueueNIB, self)]
                          /\ nextIRIDToSend' = [nextIRIDToSend EXCEPT ![self] = IRQueueNIB[index'[self]].data]
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![index'[self]].tag = self]
                          /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRIDToSend'[self]]]
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                          /\ UNCHANGED << swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, RCNIBEventQueue, DAGState, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          rcInternalState, SetScheduledIRs, 
                                          seqWorkerIsBusy, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, DAGID, nxtDAG, 
                                          deleterID, setRemovableIRs, currIR, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRSet, IRDoneSet, monitoringEvent, 
                                          setIRsToReset, resetIR, msg, irID, 
                                          removedIR >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ IF ~isSwitchSuspended(getSwitchForIR(nextIRIDToSend[self])) /\ NIBIRStatus[nextIRIDToSend[self]] = IR_NONE
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![nextIRIDToSend[self]] = IR_SENT]
                                           /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> nextIRIDToSend[self], state |-> IR_SENT]))
                                           /\ LET destination == getSwitchForIR(nextIRIDToSend[self]) IN
                                                controller2Switch' = [controller2Switch EXCEPT ![destination] = Append(controller2Switch[destination], ([type |-> getIRType(nextIRIDToSend[self]), flow |-> getPrimaryOfIR(nextIRIDToSend[self]), to |-> destination, from |-> self[1]]))]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << controller2Switch, 
                                                           RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                                /\ index' = [index EXCEPT ![self] = GetFirstItemIndexWithTag(IRQueueNIB, self)]
                                /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index'[self])
                                /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                /\ UNCHANGED << swSeqChangedStatus, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, DAGState, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                SetScheduledIRs, 
                                                seqWorkerIsBusy, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, toBeScheduledIRs, 
                                                nextIR, currDAG, IRSet, 
                                                IRDoneSet, nextIRIDToSend, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, msg, irID, removedIR >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ IF (ofcInternalState[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (NIBIRStatus[ofcInternalState[self].next] = IR_SENT)
                                                              THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![ofcInternalState[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED NIBIRStatus
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED NIBIRStatus
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << swSeqChangedStatus, 
                                                             controller2Switch, 
                                                             switch2Controller, 
                                                             TEEventQueue, 
                                                             DAGEventQueue, 
                                                             DAGQueue, 
                                                             IRQueueNIB, 
                                                             RCNIBEventQueue, 
                                                             DAGState, 
                                                             RCIRStatus, 
                                                             RCSwSuspensionStatus, 
                                                             SwSuspensionStatus, 
                                                             rcInternalState, 
                                                             ofcInternalState, 
                                                             SetScheduledIRs, 
                                                             seqWorkerIsBusy, 
                                                             event, 
                                                             topoChangeEvent, 
                                                             currSetDownSw, 
                                                             prev_dag_id, init, 
                                                             DAGID, nxtDAG, 
                                                             deleterID, 
                                                             setRemovableIRs, 
                                                             currIR, 
                                                             currIRInDAG, 
                                                             nxtDAGVertices, 
                                                             setIRsInDAG, 
                                                             prev_dag, 
                                                             seqEvent, 
                                                             toBeScheduledIRs, 
                                                             nextIR, currDAG, 
                                                             IRSet, IRDoneSet, 
                                                             nextIRIDToSend, 
                                                             index, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, msg, 
                                                             irID, removedIR >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ Len(swSeqChangedStatus) > 0
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    IRQueueNIB, 
                                                    RCNIBEventQueue, DAGState, 
                                                    RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    rcInternalState, 
                                                    ofcInternalState, 
                                                    SetScheduledIRs, 
                                                    seqWorkerIsBusy, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    deleterID, setRemovableIRs, 
                                                    currIR, currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, toBeScheduledIRs, 
                                                    nextIR, currDAG, IRSet, 
                                                    IRDoneSet, nextIRIDToSend, 
                                                    index, setIRsToReset, 
                                                    resetIR, msg, irID, 
                                                    removedIR >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, sw |-> NADIR_NULL]]
                                                   /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << controller2Switch, 
                                                                   switch2Controller, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   IRQueueNIB, 
                                                                   RCNIBEventQueue, 
                                                                   DAGState, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   NIBIRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   rcInternalState, 
                                                                   SetScheduledIRs, 
                                                                   seqWorkerIsBusy, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, DAGID, 
                                                                   nxtDAG, 
                                                                   deleterID, 
                                                                   setRemovableIRs, 
                                                                   currIR, 
                                                                   currIRInDAG, 
                                                                   nxtDAGVertices, 
                                                                   setIRsInDAG, 
                                                                   prev_dag, 
                                                                   seqEvent, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   IRDoneSet, 
                                                                   nextIRIDToSend, 
                                                                   index, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   removedIR >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                             /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND]))
                             /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                             /\ UNCHANGED << swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, DAGState, RCIRStatus, 
                                             RCSwSuspensionStatus, NIBIRStatus, 
                                             rcInternalState, ofcInternalState, 
                                             SetScheduledIRs, seqWorkerIsBusy, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             DAGID, nxtDAG, deleterID, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             toBeScheduledIRs, nextIR, currDAG, 
                                             IRSet, IRDoneSet, nextIRIDToSend, 
                                             index, monitoringEvent, 
                                             setIRsToReset, resetIR, msg, irID, 
                                             removedIR >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          DAGState, RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          SetScheduledIRs, 
                                                          seqWorkerIsBusy, 
                                                          event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, nxtDAG, 
                                                          deleterID, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, seqEvent, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRSet, IRDoneSet, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID, 
                                                          removedIR >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = getIRSetToReset(monitoringEvent[self].swID)]
                           /\ IF (setIRsToReset'[self] = {})
                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           /\ UNCHANGED << swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, IRQueueNIB, 
                                           RCNIBEventQueue, DAGState, 
                                           RCIRStatus, RCSwSuspensionStatus, 
                                           NIBIRStatus, SwSuspensionStatus, 
                                           rcInternalState, ofcInternalState, 
                                           SetScheduledIRs, seqWorkerIsBusy, 
                                           event, topoChangeEvent, 
                                           currSetDownSw, prev_dag_id, init, 
                                           DAGID, nxtDAG, deleterID, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           toBeScheduledIRs, nextIR, currDAG, 
                                           IRSet, IRDoneSet, nextIRIDToSend, 
                                           index, monitoringEvent, resetIR, 
                                           msg, irID, removedIR >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                     /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                     /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]] = IR_NONE]
                     /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> resetIR'[self], state |-> IR_NONE]))
                     /\ IF setIRsToReset'[self] = {}
                           THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                     /\ UNCHANGED << swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, IRQueueNIB, 
                                     DAGState, RCIRStatus, 
                                     RCSwSuspensionStatus, SwSuspensionStatus, 
                                     rcInternalState, ofcInternalState, 
                                     SetScheduledIRs, seqWorkerIsBusy, event, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     deleterID, setRemovableIRs, currIR, 
                                     currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                     prev_dag, seqEvent, toBeScheduledIRs, 
                                     nextIR, currDAG, IRSet, IRDoneSet, 
                                     nextIRIDToSend, index, monitoringEvent, 
                                     msg, irID, removedIR >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                   /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                   /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_RUN]))
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   NIBIRStatus, 
                                                   rcInternalState, 
                                                   SetScheduledIRs, 
                                                   seqWorkerIsBusy, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, IRDoneSet, 
                                                   nextIRIDToSend, index, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ IF (ofcInternalState[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![ofcInternalState[self].sw] = SW_SUSPEND]
                                                              /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND]))
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                                              SwSuspensionStatus >>
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   IRQueueNIB, 
                                                                   DAGState, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   NIBIRStatus, 
                                                                   rcInternalState, 
                                                                   ofcInternalState, 
                                                                   SetScheduledIRs, 
                                                                   seqWorkerIsBusy, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, DAGID, 
                                                                   nxtDAG, 
                                                                   deleterID, 
                                                                   setRemovableIRs, 
                                                                   currIR, 
                                                                   currIRInDAG, 
                                                                   nxtDAGVertices, 
                                                                   setIRsInDAG, 
                                                                   prev_dag, 
                                                                   seqEvent, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   IRDoneSet, 
                                                                   nextIRIDToSend, 
                                                                   index, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   removedIR >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ Len(switch2Controller) > 0
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg'[self].flow, msg'[self].type)]
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone"]
                                       /\ UNCHANGED << swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       TEEventQueue, 
                                                       DAGEventQueue, DAGQueue, 
                                                       IRQueueNIB, 
                                                       RCNIBEventQueue, 
                                                       DAGState, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       SetScheduledIRs, 
                                                       seqWorkerIsBusy, event, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       DAGID, nxtDAG, 
                                                       deleterID, 
                                                       setRemovableIRs, currIR, 
                                                       currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       seqEvent, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, IRSet, 
                                                       IRDoneSet, 
                                                       nextIRIDToSend, index, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       removedIR >>

ControllerUpdateIRDone(self) == /\ pc[self] = "ControllerUpdateIRDone"
                                /\ IF NIBIRStatus[irID[self]] = IR_SENT
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID[self]] = IR_DONE]
                                           /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> irID[self], state |-> IR_DONE]))
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                /\ removedIR' = [removedIR EXCEPT ![self] = getDualOfIR(irID[self])]
                                /\ IF removedIR'[self] \in DOMAIN NIBIRStatus'
                                      THEN /\ pc' = [pc EXCEPT ![self] = "ControllerMonUpdateIRNone"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                /\ UNCHANGED << swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, DAGState, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, 
                                                seqWorkerIsBusy, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, toBeScheduledIRs, 
                                                nextIR, currDAG, IRSet, 
                                                IRDoneSet, nextIRIDToSend, 
                                                index, monitoringEvent, 
                                                setIRsToReset, resetIR, msg, 
                                                irID >>

ControllerMonUpdateIRNone(self) == /\ pc[self] = "ControllerMonUpdateIRNone"
                                   /\ IF NIBIRStatus[removedIR[self]] = IR_DONE
                                         THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![removedIR[self]] = IR_NONE]
                                              /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> removedIR[self], state |-> IR_NONE]))
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                              NIBIRStatus >>
                                   /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   SwSuspensionStatus, 
                                                   rcInternalState, 
                                                   ofcInternalState, 
                                                   SetScheduledIRs, 
                                                   seqWorkerIsBusy, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, IRDoneSet, 
                                                   nextIRIDToSend, index, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ switch2Controller' = Tail(switch2Controller)
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                         /\ UNCHANGED << swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         RCNIBEventQueue, 
                                                         DAGState, RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         SetScheduledIRs, 
                                                         seqWorkerIsBusy, 
                                                         event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         DAGID, nxtDAG, 
                                                         deleterID, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, 
                                                         toBeScheduledIRs, 
                                                         nextIR, currDAG, 
                                                         IRSet, IRDoneSet, 
                                                         nextIRIDToSend, index, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, irID, 
                                                         removedIR >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ ControllerUpdateIRDone(self)
                                       \/ ControllerMonUpdateIRNone(self)
                                       \/ MonitoringServerRemoveFromQueue(self)

Next == (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))

\* END TRANSLATION 

ENUM_SET_INSTALLER_STATUS == {INSTALLER_DOWN, INSTALLER_UP}
ENUM_SET_OF_CMD == {INSTALL_FLOW, DELETE_FLOW}
ENUM_SET_OF_ACK == {INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY}
ENUM_SET_SW_STATE == {SW_SUSPEND, SW_RUN}
ENUM_SET_IR_STATE == {IR_NONE, IR_SENT, IR_DONE}
ENUM_SET_DAG_STATE == {DAG_SUBMIT, DAG_NONE, DAG_STALE}
ENUM_SET_RC_SCHEDULER_INTERNAL_STATE == {STATUS_START_SCHEDULING}
ENUM_SET_OFC_WORKER_POOL_INTERNAL_STATE == {STATUS_LOCKING, STATUS_SENT_DONE}
ENUM_SET_OFC_EVENT_HANDLER_INTERNAL_STATE == {START_RESET_IR}

NadirEnumSet == ("EnumInstallerStatus" :> ENUM_SET_INSTALLER_STATUS) @@
                ("EnumOpenFlowCMD" :> ENUM_SET_OF_CMD) @@
                ("EnumOpenFlowACK" :> ENUM_SET_OF_ACK) @@
                ("EnumSwitchState" :> ENUM_SET_SW_STATE) @@
                ("EnumIRState" :> ENUM_SET_IR_STATE) @@
                ("EnumDAGState" :> ENUM_SET_DAG_STATE) @@
                ("EnumRCSchedulerInternalState" :> ENUM_SET_RC_SCHEDULER_INTERNAL_STATE) @@
                ("EnumOFCWorkerPoolInternalState" :> ENUM_SET_OFC_WORKER_POOL_INTERNAL_STATE) @@
                ("EnumOFCEventHandlerInternalState" :> ENUM_SET_OFC_EVENT_HANDLER_INTERNAL_STATE)

STRUCT_SET_RC_DAG == [v: SUBSET NADIR_INT_ID_SET, e: SUBSET (NADIR_INT_ID_SET \X NADIR_INT_ID_SET)]

STRUCT_SET_DAG_OBJECT == [id: NADIR_INT_ID_SET, dag: STRUCT_SET_RC_DAG]

STRUCT_SET_RC_SCHEDULER_INTERNAL_STATE == [
    type: NadirNullable(ENUM_SET_RC_SCHEDULER_INTERNAL_STATE), 
    next: NadirNullable(NADIR_INT_ID_SET)]

STRUCT_SET_RC_INTERNAL_STATE == STRUCT_SET_RC_SCHEDULER_INTERNAL_STATE

STRUCT_SET_OFC_WORKER_POOL_INTERNAL_STATE == [
    type: NadirNullable(ENUM_SET_OFC_WORKER_POOL_INTERNAL_STATE), 
    next: NadirNullable(NADIR_INT_ID_SET)]

STRUCT_SET_OFC_EVENT_HANDLER_INTERNAL_STATE == [
    type: NadirNullable(ENUM_SET_OFC_EVENT_HANDLER_INTERNAL_STATE), 
    sw: NadirNullable(SW)]

STRUCT_SET_OFC_INTERNAL_STATE == (STRUCT_SET_OFC_WORKER_POOL_INTERNAL_STATE \cup STRUCT_SET_OFC_EVENT_HANDLER_INTERNAL_STATE)

STRUCT_SET_NIB_TAGGED_IR == [
    data: NADIR_INT_ID_SET, 
    tag: NadirNullable(OFCProcSet)]

NadirStructSet == ("StructRCDAG" :> STRUCT_SET_RC_DAG) @@
                  ("StructDAGObject" :> STRUCT_SET_DAG_OBJECT) @@
                  ("StructRCSchedulerInternalState" :> STRUCT_SET_RC_SCHEDULER_INTERNAL_STATE) @@
                  ("StructRCInternalState" :> STRUCT_SET_RC_INTERNAL_STATE) @@
                  ("StructOFCWorkerPoolInternalState" :> STRUCT_SET_OFC_WORKER_POOL_INTERNAL_STATE) @@
                  ("StructOFCEventHandlerInternalState" :> STRUCT_SET_OFC_EVENT_HANDLER_INTERNAL_STATE) @@
                  ("StructOFCInternalState" :> STRUCT_SET_OFC_INTERNAL_STATE) @@
                  ("StructNIBTaggedIR" :> STRUCT_SET_NIB_TAGGED_IR)

MSG_SET_TIMEOUT == [
    swID: SW, 
    num: Nat, 
    type: {NIC_ASIC_DOWN, OFA_DOWN}]
        
MSG_SET_KEEPALIVE == [
    swID: SW, 
    num: Nat, 
    type: {KEEP_ALIVE}, 
    installerStatus: ENUM_SET_INSTALLER_STATUS]
        
MSG_SET_OF_CMD == [
    from: {ofc0},
    type: ENUM_SET_OF_CMD, 
    to: SW, 
    flow: Nat]

MSG_SET_OF_ACK == [
    to: {ofc0},
    type: ENUM_SET_OF_ACK, 
    from: SW,
    flow: Nat]

MSG_SET_TOPO_MOD == [
    type: {TOPO_MOD},
    sw: SW,
    state: ENUM_SET_SW_STATE]

MSG_SET_IR_MOD == [
    type: {IR_MOD},
    state: ENUM_SET_IR_STATE,
    IR: NADIR_INT_ID_SET]

MSG_SET_TE_EVENT == (MSG_SET_TOPO_MOD \cup MSG_SET_IR_MOD)

MSG_SET_DAG_STALE_NOTIF == [
    type: {DAG_STALE},
    id: NADIR_INT_ID_SET]

MSG_SET_DAG_NEW_NOTIF == [
    type: {DAG_NEW},
    dag_obj: STRUCT_SET_DAG_OBJECT]

MSG_SET_DAG_EVENT == (MSG_SET_DAG_STALE_NOTIF \cup MSG_SET_DAG_NEW_NOTIF)
        
NadirMessageSet == ("MessageSwitchTimeout" :> MSG_SET_TIMEOUT) @@
                   ("MessageSwitchKeepalive" :> MSG_SET_KEEPALIVE) @@
                   ("MessageOpenFlowCMD" :> MSG_SET_OF_CMD) @@
                   ("MessageOpenFlowACK" :> MSG_SET_OF_ACK) @@
                   ("MessageTopoMod" :> MSG_SET_TOPO_MOD) @@
                   ("MessageIRMod" :> MSG_SET_IR_MOD) @@
                   ("MessageTEEvent" :> MSG_SET_TE_EVENT) @@
                   ("MessageDAGStaleNotif" :> MSG_SET_DAG_STALE_NOTIF) @@
                   ("MessageDAGNewNotif" :> MSG_SET_DAG_NEW_NOTIF) @@
                   ("MessageDAGEvent" :> MSG_SET_DAG_EVENT)

TypeOK ==  /\ NadirFIFO(MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE, swSeqChangedStatus)
           /\ NadirFIFO(MSG_SET_OF_ACK, switch2Controller)
           /\ NadirFIFO(MSG_SET_TE_EVENT, TEEventQueue)
           /\ NadirFIFO(MSG_SET_DAG_EVENT, DAGEventQueue)
           /\ NadirFIFO(STRUCT_SET_DAG_OBJECT, DAGQueue)
           /\ NadirFIFO(MSG_SET_TE_EVENT, RCNIBEventQueue)
           /\ NadirAckQueue(STRUCT_SET_NIB_TAGGED_IR, IRQueueNIB)
           /\ NadirFanoutFIFO(SW, MSG_SET_OF_CMD, controller2Switch)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, ENUM_SET_DAG_STATE, DAGState)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, ENUM_SET_IR_STATE, RCIRStatus)
           /\ NadirFunctionTypeCheck(SW, ENUM_SET_SW_STATE, RCSwSuspensionStatus)
           /\ seqWorkerIsBusy \in BOOLEAN 
           /\ NadirFunctionTypeCheck(RCProcSet, STRUCT_SET_RC_INTERNAL_STATE, rcInternalState)
           /\ NadirFunctionTypeCheck(OFCProcSet, STRUCT_SET_OFC_INTERNAL_STATE, ofcInternalState)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, ENUM_SET_IR_STATE, NIBIRStatus)
           /\ NadirFunctionTypeCheck(SW, ENUM_SET_SW_STATE, SwSuspensionStatus)
           /\ NadirFunctionTypeCheck(SW, SUBSET NADIR_INT_ID_SET, SetScheduledIRs)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_TE_EVENT), event)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_TE_EVENT), topoChangeEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET SW, currSetDownSw)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), prev_dag_id)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), DAGID)
           /\ NadirLocalVariableTypeCheck({0, 1}, init)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_DAG_OBJECT), nxtDAG)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), deleterID)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, setRemovableIRs)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), currIR)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), currIRInDAG)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, nxtDAGVertices)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, setIRsInDAG)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_RC_DAG), prev_dag)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_DAG_EVENT), seqEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, toBeScheduledIRs)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), nextIR)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_DAG_OBJECT), currDAG)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, IRSet)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, IRDoneSet)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), nextIRIDToSend)
           /\ NadirLocalVariableTypeCheck(NadirNullable(Nat), index)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_KEEPALIVE \cup MSG_SET_TIMEOUT), monitoringEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, setIRsToReset)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), resetIR)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_OF_ACK), msg)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), irID)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), removedIR)

NadirConstantAssumptions == /\ MaxDAGID \in Nat
                            /\ MaxNumIRs \in Nat
                            /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, SW, IR2SW)
                            /\ NadirFunctionTypeCheck(SUBSET SW, STRUCT_SET_RC_DAG, TOPO_DAG_MAPPING)
                            /\ NadirSetOfPIDs(RCProcSet)
                            /\ NadirSetOfPIDs(OFCProcSet)

ASSUME NadirConstantAssumptions
=============================================================================

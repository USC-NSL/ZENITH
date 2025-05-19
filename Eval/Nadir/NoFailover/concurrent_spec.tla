------------------- MODULE concurrent_spec -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, NadirTypes, NadirAckQueue

CONSTANTS SW
CONSTANTS ofc0, rc0
CONSTANTS CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_TE
CONSTANTS CONTROLLER_THREAD_POOL, CONT_MONITOR, CONT_EVENT, NIB_EVENT_HANDLER
CONSTANTS IR_NONE, IR_SENT, IR_DONE, IR_FAILED
CONSTANTS SW_RUN, SW_SUSPEND
CONSTANTS DAG_STALE, DAG_NEW, DAG_SUBMIT, DAG_NONE
CONSTANTS TOPO_MOD, IR_MOD
CONSTANTS STATUS_START_SCHEDULING, STATUS_LOCKING, STATUS_SENT_DONE, START_RESET_IR
CONSTANTS INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM, INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY, CLEARED_TCAM_SUCCESSFULLY, KEEP_ALIVE
CONSTANTS NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN, INSTALLER_UP
CONSTANTS MaxDAGID, MaxNumIRs
CONSTANTS TOPO_DAG_MAPPING, IR2SW
CONSTANTS OFCProcSet

CONSTANTS NO_LOCK, SW_SIMPLE_ID
CONSTANTS MAX_OFC_SUBMODULE_FAILS


(*--fair algorithm stateConsistency
    variables 
        switchLock = <<NO_LOCK, NO_LOCK>>,
        controllerLock = <<NO_LOCK, NO_LOCK>>, 
        
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

        ofcSubmoduleFailNum  = [x \in OFCProcSet |-> 0],
        FirstInstall = [x \in 1..2*MaxNumIRs |-> 0],
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

        maxFailure(threadID) == MAX_OFC_SUBMODULE_FAILS
    end define

    \************************

    macro workerPoolFails()
    begin
        ofcSubmoduleFailNum[self] := ofcSubmoduleFailNum[self] + 1;
        nextIRObjectToSend := NADIR_NULL;
        index := 0;
        goto ControllerThread;
    end macro;

    macro eventHandlerFails() begin
        ofcSubmoduleFailNum[self] := ofcSubmoduleFailNum[self] + 1;
        monitoringEvent := NADIR_NULL;
        goto ControllerEventHandlerStateReconciliation;
    end macro;

    macro monitoringServerFails() begin
        ofcSubmoduleFailNum[self] := ofcSubmoduleFailNum[self] + 1;
        msg := NADIR_NULL;
        goto ControllerMonitorCheckIfMastr;
    end macro;

    macro whichStepToFail(numSteps, step)
    begin
        if (ofcSubmoduleFailNum[self] < maxFailure(self)) then
            with num \in 0..numSteps do
                step := num;
            end with;
        else
            step := 0;
        end if;
    end macro;

    \************************

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

    macro controllerWaitForLockFree()
    begin
        await controllerLock \in {self, <<NO_LOCK, NO_LOCK>>};
        await switchLock = <<NO_LOCK, NO_LOCK>>;
    end macro

    macro controllerAcquireLock()
    begin
        controllerWaitForLockFree();
        controllerLock := self;
    end macro    

    macro controllerReleaseLock()
    begin
        controllerWaitForLockFree();
        controllerLock := <<NO_LOCK, NO_LOCK>>;
    end macro

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
        switchLock := <<SW_SIMPLE_ID, irObject.sw>>;
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
        controllerWaitForLockFree();
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
        controllerAcquireLock();
        if init = TRUE then
            goto ControllerTEComputeDagBasedOnTopo;
        else
            NadirFIFOPeek(TEEventQueue, topoChangeEvent);
        end if;
        
        ControllerTEEventProcessing:
        while init # TRUE do
            controllerWaitForLockFree();
            if topoChangeEvent = NADIR_NULL then
                NadirFIFOPeekWithTimeout(TEEventQueue, topoChangeEvent);
                if topoChangeEvent = NADIR_NULL then
                    controllerReleaseLock();
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
        controllerReleaseLock();
        
        ControllerTEComputeDagBasedOnTopo:
            controllerWaitForLockFree();
            getNextDAGID();
            nxtDAG := [id |-> DAGID, dag |-> TOPO_DAG_MAPPING[currSetDownSw]];
            nxtDAGVertices := nxtDAG.dag.v;
            if init = FALSE then
                DAGState[prev_dag_id] := DAG_STALE;
            
                ControllerTESendDagStaleNotif:
                    controllerWaitForLockFree();
                    NadirFIFOPut(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id]);
            
                ControllerTEWaitForStaleDAGToBeRemoved:
                    controllerWaitForLockFree();
                    await DAGState[prev_dag_id] = DAG_NONE;
                    prev_dag_id := DAGID;
                    setRemovableIRs := getSetRemovableIRs(SW \ currSetDownSw, nxtDAGVertices);
            else
                init := FALSE;
                prev_dag_id := DAGID;
            end if;
            
        ControllerTERemoveUnnecessaryIRs:
            nxtDAG.dag := CreateTEDAG(setRemovableIRs, nxtDAG.dag);
            controllerReleaseLock();
            unscheduleDagIRs(nxtDAG.dag.v);
            
        ControllerTESubmitNewDAG:
            controllerWaitForLockFree();
            DAGState[nxtDAG.id] := DAG_SUBMIT;
            NadirFIFOPut(DAGEventQueue, [type |-> DAG_NEW, dag_obj |-> nxtDAG]);
    end while;
    end process

    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    variables seqEvent = NADIR_NULL;
    begin
    ControllerBossSeqProc:
    while TRUE do
        controllerWaitForLockFree();
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
        controllerWaitForLockFree();
        NadirFIFOPeek(DAGQueue, currDAG);
        seqWorkerIsBusy := TRUE;
        
        ControllerWorkerSeqScheduleDAG:
            while dagObjectShouldBeProcessed(currDAG) do
                controllerWaitForLockFree();
                toBeScheduledIRs := getSetIRsCanBeScheduledNext(currDAG.dag);
                await toBeScheduledIRs # {};

                SchedulerMechanism:
                while TRUE do
                    controllerWaitForLockFree();
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

            controllerAcquireLock();
            seqWorkerIsBusy := FALSE;
            
            if allIRsInDAGInstalled(currDAG.dag) then
                IRDoneSet := AddDeleteDAGIRDoneSet(currDAG.dag.v, IRDoneSet);
            end if;
            RemoveDagFromQueue:
                controllerReleaseLock();
                NadirFIFOPop(DAGQueue);
    end while;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRObjectToSend = NADIR_NULL, index = 0, stepOfFailureWP = 0;
    begin
    ControllerThread:
    while TRUE do
        controllerWaitForLockFree();
        NadirAckQueueGet(IRQueueNIB, self, index, nextIRObjectToSend);

        ControllerThreadSendIR:
            controllerWaitForLockFree();
        
            if isClearIR(nextIRObjectToSend.IR) then
                if isSwitchSuspended(nextIRObjectToSend.sw) then
                    \* whichStepToFail(1, stepOfFailureWP);
                    
                    if (stepOfFailureWP = 1) then
                        workerPoolFails();
                    else
                        controllerSendIR(nextIRObjectToSend);
                    end if;
                end if;
            elsif getNIBIRState(nextIRObjectToSend.IR) \in {IR_NONE, IR_SENT} then
                if isSwitchSuspended(nextIRObjectToSend.sw) then
                    \* whichStepToFail(1, stepOfFailureWP);
                    
                    if (stepOfFailureWP = 1) then
                        workerPoolFails();
                    else
                        RCNIBEventQueue := Append(
                            RCNIBEventQueue, 
                            [type |-> IR_FAILED, IR |-> nextIRObjectToSend.IR, state |-> IR_NONE]
                        );
                    end if;
                else
                    \* whichStepToFail(2, stepOfFailureWP);
                    
                    if (stepOfFailureWP = 1) then
                        workerPoolFails();
                    else
                        setNIBIRState(nextIRObjectToSend.IR, IR_SENT);

                        if (stepOfFailureWP = 2) then
                            workerPoolFails();
                        else
                            RCNIBEventQueue := Append(
                                RCNIBEventQueue, 
                                [type |-> IR_MOD, IR |-> nextIRObjectToSend.IR, state |-> IR_SENT]
                            );
                        end if;
                    end if;
                    
                    ControllerThreadForwardIR:
                        controllerWaitForLockFree();
                        \* whichStepToFail(1, stepOfFailureWP);

                        if (stepOfFailureWP = 1) then
                            workerPoolFails();
                        else
                            controllerSendIR(nextIRObjectToSend);
                        end if;
                end if;
            end if;
        
        ControllerThreadRemoveIRFromQueue:
            controllerWaitForLockFree();
            \* whichStepToFail(1, stepOfFailureWP);

            if (stepOfFailureWP = 1) then
                workerPoolFails();
            else
                NadirAckQueueAck(IRQueueNIB, self, index);
            end if;
        
    end while;
    end process

    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = NADIR_NULL, setIRsToReset = {}, resetIR = NADIR_NULL, stepOfFailureEH = 0;
    begin
    ControllerEventHandlerProc:
    while TRUE do 
        controllerAcquireLock();
        NadirFIFOPeek(swSeqChangedStatus, monitoringEvent);

        if shouldSuspendRunningSw(monitoringEvent) then
            ControllerSuspendSW: 
                controllerWaitForLockFree();
                whichStepToFail(2, stepOfFailureEH);
            
                eventHandlerCheckpoint := TRUE;
            
                if (stepOfFailureEH = 1) then
                    eventHandlerFails();
                else
                    SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                    if (stepOfFailureEH = 2) then
                        eventHandlerFails();
                    else
                        NadirFIFOPut(
                            RCNIBEventQueue,
                            [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]
                        );
                    end if;
                end if;
        
        elsif shouldClearSuspendedSw(monitoringEvent) then
            ControllerRequestTCAMClear:
                whichStepToFail(1, stepOfFailureEH);
            
                if (stepOfFailureEH = 1) then
                    eventHandlerFails();
                else
                    if ~existsMonitoringEventHigherNum(monitoringEvent) then
                        NadirAckQueuePut(IRQueueNIB, [IR |-> 0, sw |-> monitoringEvent.swID]);
                    end if;
                end if;

        elsif shouldFreeSuspendedSw(monitoringEvent) then
            ControllerCheckIfThisIsLastEvent:
                controllerReleaseLock();
                if ~existsMonitoringEventHigherNum(monitoringEvent) /\ ~eventHandlerTCAMCleared then
                    getIRsToBeChecked:
                        controllerWaitForLockFree();
                        setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                        if (setIRsToReset = {}) then
                            goto ControllerFreeSuspendedSW;
                        end if;

                    ResetAllIRs:
                        while TRUE do
                            controllerWaitForLockFree();
                            whichStepToFail(2, stepOfFailureEH);

                            resetIR := CHOOSE x \in setIRsToReset: TRUE;
                            setIRsToReset := setIRsToReset \ {resetIR};

                            if (stepOfFailureEH = 1) then
                                eventHandlerFails();
                            else
                                eventHandlerLastIRToReset := resetIR;
                                setNIBIRState(resetIR, IR_NONE);
                                if (stepOfFailureEH = 2) then
                                    eventHandlerFails();
                                else
                                    NadirFIFOPut(
                                        RCNIBEventQueue,
                                        [type |-> IR_MOD, IR |-> resetIR, state |-> IR_NONE]
                                    );
                                    if setIRsToReset = {} then
                                        goto ControllerFreeSuspendedSW;
                                    end if;
                                end if;
                            end if;
                        end while;
                end if;

            ControllerFreeSuspendedSW: 
                controllerAcquireLock();
                whichStepToFail(3, stepOfFailureEH);

                eventHandlerCheckpoint := TRUE;
                eventHandlerLastIRToReset := NADIR_NULL;

                if (stepOfFailureEH = 1) then
                    eventHandlerFails();
                else
                    SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                    if (stepOfFailureEH = 2) then
                        eventHandlerFails();
                    else
                        eventHandlerTCAMCleared := TRUE;
                        if (stepOfFailureEH = 3) then
                            eventHandlerFails();
                        else
                            NadirFIFOPut(
                                RCNIBEventQueue,
                                [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]
                            );
                        end if;
                    end if;
                end if;
        end if;

        ControllerEvenHanlderRemoveEventFromQueue:
            controllerReleaseLock();
            whichStepToFail(2, stepOfFailureEH);

            if (stepOfFailureEH = 1) then
                eventHandlerFails();
            else
                eventHandlerCheckpoint := FALSE;
                eventHandlerTCAMCleared := FALSE;
                eventHandlerLastIRToReset := NADIR_NULL;
                if (stepOfFailureEH = 2) then
                    eventHandlerFails();
                else
                    NadirFIFOPop(swSeqChangedStatus);
                end if;
            end if;
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
    variable msg = NADIR_NULL, irID = NADIR_NULL, stepOfFailureMS = 0;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        controllerAcquireLock();
        NadirFIFOPeek(switch2Controller, msg);
        
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            ControllerProcessIRMod:
                controllerWaitForLockFree();
                \* whichStepToFail(2 ,stepOfFailureMS);
            
                irID := getIRIDForFlow(msg.flow, msg.type);
                FirstInstall[irID] := 1;
                if (stepOfFailureMS = 1) then
                    monitoringServerFails();
                else
                    setNIBIRState(irID, IR_DONE);
                    if (stepOfFailureMS = 2) then
                        monitoringServerFails();
                    else
                        NadirFIFOPut(
                            RCNIBEventQueue,
                            [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                        );
                    end if;
                end if;
        else
            ForwardToEH:
                controllerWaitForLockFree();
                \* whichStepToFail(1 ,stepOfFailureMS);
            
                if (stepOfFailureMS = 1) then
                    monitoringServerFails();
                else
                    NadirFIFOPut(swSeqChangedStatus, msg);
                end if;
        end if;

        MonitoringServerRemoveFromQueue:
            controllerReleaseLock();
            \* whichStepToFail(1 ,stepOfFailureMS);

            if (stepOfFailureMS = 1) then
                monitoringServerFails();
            else
                NadirFIFOPop(switch2Controller);
            end if;
    end while
end process
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "27ecb249" /\ chksum(tla) = "4463ff7b")
VARIABLES switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
          switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
          IRQueueNIB, RCNIBEventQueue, DAGState, RCSwSuspensionStatus, 
          RCIRStatus, NIBIRStatus, SwSuspensionStatus, SetScheduledIRs, 
          seqWorkerIsBusy, eventHandlerCheckpoint, eventHandlerTCAMCleared, 
          eventHandlerLastIRToReset, ofcSubmoduleFailNum, FirstInstall, pc

(* define statement *)
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

maxFailure(threadID) == MAX_OFC_SUBMODULE_FAILS

VARIABLES event, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, 
          nxtDAG, nxtDAGVertices, setRemovableIRs, seqEvent, toBeScheduledIRs, 
          nextIR, currDAG, IRDoneSet, nextIRObjectToSend, index, 
          stepOfFailureWP, monitoringEvent, setIRsToReset, resetIR, 
          stepOfFailureEH, msg, irID, stepOfFailureMS

vars == << switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
           switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
           IRQueueNIB, RCNIBEventQueue, DAGState, RCSwSuspensionStatus, 
           RCIRStatus, NIBIRStatus, SwSuspensionStatus, SetScheduledIRs, 
           seqWorkerIsBusy, eventHandlerCheckpoint, eventHandlerTCAMCleared, 
           eventHandlerLastIRToReset, ofcSubmoduleFailNum, FirstInstall, pc, 
           event, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, 
           nxtDAG, nxtDAGVertices, setRemovableIRs, seqEvent, 
           toBeScheduledIRs, nextIR, currDAG, IRDoneSet, nextIRObjectToSend, 
           index, stepOfFailureWP, monitoringEvent, setIRsToReset, resetIR, 
           stepOfFailureEH, msg, irID, stepOfFailureMS >>

ProcSet == (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ seqWorkerIsBusy = FALSE
        /\ eventHandlerCheckpoint = FALSE
        /\ eventHandlerTCAMCleared = FALSE
        /\ eventHandlerLastIRToReset = NADIR_NULL
        /\ ofcSubmoduleFailNum = [x \in OFCProcSet |-> 0]
        /\ FirstInstall = [x \in 1..2*MaxNumIRs |-> 0]
        (* Process rcNibEventHandler *)
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> NADIR_NULL]
        (* Process controllerTrafficEngineering *)
        /\ topoChangeEvent = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ currSetDownSw = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag_id = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ init = [self \in ({rc0} \X {CONT_TE}) |-> TRUE]
        /\ DAGID = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ nxtDAG = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ nxtDAGVertices = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ setRemovableIRs = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        (* Process controllerBossSequencer *)
        /\ seqEvent = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ IRDoneSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        (* Process controllerWorkerThreads *)
        /\ nextIRObjectToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ stepOfFailureWP = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ stepOfFailureEH = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ stepOfFailureMS = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                THEN /\ IF getRCIRState(event'[self].IR) # event'[self].state
                                                           THEN /\ IF (isPrimary((event'[self].IR)))
                                                                      THEN /\ IF (event'[self].state) = IR_DONE /\ RCIRStatus[(event'[self].IR)].dual = IR_DONE
                                                                                 THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![(event'[self].IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                 ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![(event'[self].IR)].primary = event'[self].state]
                                                                      ELSE /\ LET primary == getPrimaryOfIR((event'[self].IR)) IN
                                                                                IF (event'[self].state) = IR_DONE /\ RCIRStatus[primary].primary = IR_DONE
                                                                                   THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                   ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![primary].dual = event'[self].state]
                                                                /\ LET destination == getSwitchForIR(event'[self].IR) IN
                                                                     SetScheduledIRs' = [SetScheduledIRs EXCEPT ![destination] = SetScheduledIRs[destination] \ {event'[self].IR}]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << RCIRStatus, 
                                                                                SetScheduledIRs >>
                                                ELSE /\ IF (event'[self].type = IR_FAILED)
                                                           THEN /\ LET destination == getSwitchForIR(event'[self].IR) IN
                                                                     SetScheduledIRs' = [SetScheduledIRs EXCEPT ![destination] = SetScheduledIRs[destination] \ {event'[self].IR}]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED SetScheduledIRs
                                                     /\ UNCHANGED RCIRStatus
                                          /\ UNCHANGED << TEEventQueue, 
                                                          RCSwSuspensionStatus >>
                               /\ RCNIBEventQueue' = Tail(RCNIBEventQueue)
                               /\ pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, DAGState, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               seqWorkerIsBusy, 
                                               eventHandlerCheckpoint, 
                                               eventHandlerTCAMCleared, 
                                               eventHandlerLastIRToReset, 
                                               ofcSubmoduleFailNum, 
                                               FirstInstall, topoChangeEvent, 
                                               currSetDownSw, prev_dag_id, 
                                               init, DAGID, nxtDAG, 
                                               nxtDAGVertices, setRemovableIRs, 
                                               seqEvent, toBeScheduledIRs, 
                                               nextIR, currDAG, IRDoneSet, 
                                               nextIRObjectToSend, index, 
                                               stepOfFailureWP, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailureEH, msg, 
                                               irID, stepOfFailureMS >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ controllerLock' = self
                          /\ IF init[self] = TRUE
                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                     /\ UNCHANGED topoChangeEvent
                                ELSE /\ Len(TEEventQueue) > 0
                                     /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, IRQueueNIB, 
                                          RCNIBEventQueue, DAGState, 
                                          RCSwSuspensionStatus, RCIRStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          SetScheduledIRs, seqWorkerIsBusy, 
                                          eventHandlerCheckpoint, 
                                          eventHandlerTCAMCleared, 
                                          eventHandlerLastIRToReset, 
                                          ofcSubmoduleFailNum, FirstInstall, 
                                          event, currSetDownSw, prev_dag_id, 
                                          init, DAGID, nxtDAG, nxtDAGVertices, 
                                          setRemovableIRs, seqEvent, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRDoneSet, nextIRObjectToSend, index, 
                                          stepOfFailureWP, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailureEH, msg, irID, 
                                          stepOfFailureMS >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF init[self] # TRUE
                                           THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ IF topoChangeEvent[self] = NADIR_NULL
                                                      THEN /\ IF Len(TEEventQueue) > 0
                                                                 THEN /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                                                 ELSE /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = NADIR_NULL]
                                                           /\ IF topoChangeEvent'[self] = NADIR_NULL
                                                                 THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                                      /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                                                      /\ UNCHANGED controllerLock
                                                           /\ UNCHANGED << TEEventQueue, 
                                                                           currSetDownSw >>
                                                      ELSE /\ IF topoChangeEvent[self].state = SW_SUSPEND
                                                                 THEN /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \cup {topoChangeEvent[self].sw}]
                                                                 ELSE /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \ {topoChangeEvent[self].sw}]
                                                           /\ TEEventQueue' = Tail(TEEventQueue)
                                                           /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = NADIR_NULL]
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                                           /\ UNCHANGED controllerLock
                                           ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                /\ UNCHANGED << TEEventQueue, 
                                                                topoChangeEvent, 
                                                                currSetDownSw >>
                                     /\ UNCHANGED << switchLock, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     DAGEventQueue, DAGQueue, 
                                                     IRQueueNIB, 
                                                     RCNIBEventQueue, DAGState, 
                                                     RCSwSuspensionStatus, 
                                                     RCIRStatus, NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     SetScheduledIRs, 
                                                     seqWorkerIsBusy, 
                                                     eventHandlerCheckpoint, 
                                                     eventHandlerTCAMCleared, 
                                                     eventHandlerLastIRToReset, 
                                                     ofcSubmoduleFailNum, 
                                                     FirstInstall, event, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, nxtDAGVertices, 
                                                     setRemovableIRs, seqEvent, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRDoneSet, 
                                                     nextIRObjectToSend, index, 
                                                     stepOfFailureWP, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailureEH, msg, 
                                                     irID, stepOfFailureMS >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ IF DAGID[self] = NADIR_NULL
                                                 THEN /\ DAGID' = [DAGID EXCEPT ![self] = 1]
                                                 ELSE /\ DAGID' = [DAGID EXCEPT ![self] = (DAGID[self] % MaxDAGID) + 1]
                                           /\ nxtDAG' = [nxtDAG EXCEPT ![self] = [id |-> DAGID'[self], dag |-> TOPO_DAG_MAPPING[currSetDownSw[self]]]]
                                           /\ nxtDAGVertices' = [nxtDAGVertices EXCEPT ![self] = nxtDAG'[self].dag.v]
                                           /\ IF init[self] = FALSE
                                                 THEN /\ DAGState' = [DAGState EXCEPT ![prev_dag_id[self]] = DAG_STALE]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerTESendDagStaleNotif"]
                                                      /\ UNCHANGED << prev_dag_id, 
                                                                      init >>
                                                 ELSE /\ init' = [init EXCEPT ![self] = FALSE]
                                                      /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID'[self]]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                      /\ UNCHANGED DAGState
                                           /\ UNCHANGED << switchLock, 
                                                           controllerLock, 
                                                           swSeqChangedStatus, 
                                                           controller2Switch, 
                                                           switch2Controller, 
                                                           TEEventQueue, 
                                                           DAGEventQueue, 
                                                           DAGQueue, 
                                                           IRQueueNIB, 
                                                           RCNIBEventQueue, 
                                                           RCSwSuspensionStatus, 
                                                           RCIRStatus, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           SetScheduledIRs, 
                                                           seqWorkerIsBusy, 
                                                           eventHandlerCheckpoint, 
                                                           eventHandlerTCAMCleared, 
                                                           eventHandlerLastIRToReset, 
                                                           ofcSubmoduleFailNum, 
                                                           FirstInstall, event, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           setRemovableIRs, 
                                                           seqEvent, 
                                                           toBeScheduledIRs, 
                                                           nextIR, currDAG, 
                                                           IRDoneSet, 
                                                           nextIRObjectToSend, 
                                                           index, 
                                                           stepOfFailureWP, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, 
                                                           stepOfFailureEH, 
                                                           msg, irID, 
                                                           stepOfFailureMS >>

ControllerTESendDagStaleNotif(self) == /\ pc[self] = "ControllerTESendDagStaleNotif"
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_STALE, id |-> prev_dag_id[self]]))
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       TEEventQueue, DAGQueue, 
                                                       IRQueueNIB, 
                                                       RCNIBEventQueue, 
                                                       DAGState, 
                                                       RCSwSuspensionStatus, 
                                                       RCIRStatus, NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       SetScheduledIRs, 
                                                       seqWorkerIsBusy, 
                                                       eventHandlerCheckpoint, 
                                                       eventHandlerTCAMCleared, 
                                                       eventHandlerLastIRToReset, 
                                                       ofcSubmoduleFailNum, 
                                                       FirstInstall, event, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       DAGID, nxtDAG, 
                                                       nxtDAGVertices, 
                                                       setRemovableIRs, 
                                                       seqEvent, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, 
                                                       IRDoneSet, 
                                                       nextIRObjectToSend, 
                                                       index, stepOfFailureWP, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailureEH, msg, 
                                                       irID, stepOfFailureMS >>

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ DAGState[prev_dag_id[self]] = DAG_NONE
                                                /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID[self]]
                                                /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = getSetRemovableIRs(SW \ currSetDownSw[self], nxtDAGVertices[self])]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                /\ UNCHANGED << switchLock, 
                                                                controllerLock, 
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
                                                                SetScheduledIRs, 
                                                                seqWorkerIsBusy, 
                                                                eventHandlerCheckpoint, 
                                                                eventHandlerTCAMCleared, 
                                                                eventHandlerLastIRToReset, 
                                                                ofcSubmoduleFailNum, 
                                                                FirstInstall, 
                                                                event, 
                                                                topoChangeEvent, 
                                                                currSetDownSw, 
                                                                init, DAGID, 
                                                                nxtDAG, 
                                                                nxtDAGVertices, 
                                                                seqEvent, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                currDAG, 
                                                                IRDoneSet, 
                                                                nextIRObjectToSend, 
                                                                index, 
                                                                stepOfFailureWP, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, 
                                                                stepOfFailureEH, 
                                                                msg, irID, 
                                                                stepOfFailureMS >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag = CreateTEDAG(setRemovableIRs[self], nxtDAG[self].dag)]
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ SetScheduledIRs' = [x \in SW |-> (SetScheduledIRs[x] \ getSetUnschedulableIRs((nxtDAG'[self].dag.v)))]
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                          /\ UNCHANGED << switchLock, 
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
                                                          seqWorkerIsBusy, 
                                                          eventHandlerCheckpoint, 
                                                          eventHandlerTCAMCleared, 
                                                          eventHandlerLastIRToReset, 
                                                          ofcSubmoduleFailNum, 
                                                          FirstInstall, event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, 
                                                          nxtDAGVertices, 
                                                          setRemovableIRs, 
                                                          seqEvent, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRDoneSet, 
                                                          nextIRObjectToSend, 
                                                          index, 
                                                          stepOfFailureWP, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailureEH, msg, 
                                                          irID, 
                                                          stepOfFailureMS >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_NEW, dag_obj |-> nxtDAG[self]]))
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  TEEventQueue, DAGQueue, 
                                                  IRQueueNIB, RCNIBEventQueue, 
                                                  RCSwSuspensionStatus, 
                                                  RCIRStatus, NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  SetScheduledIRs, 
                                                  seqWorkerIsBusy, 
                                                  eventHandlerCheckpoint, 
                                                  eventHandlerTCAMCleared, 
                                                  eventHandlerLastIRToReset, 
                                                  ofcSubmoduleFailNum, 
                                                  FirstInstall, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  nxtDAGVertices, 
                                                  setRemovableIRs, seqEvent, 
                                                  toBeScheduledIRs, nextIR, 
                                                  currDAG, IRDoneSet, 
                                                  nextIRObjectToSend, index, 
                                                  stepOfFailureWP, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailureEH, msg, irID, 
                                                  stepOfFailureMS >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTESendDagStaleNotif(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTESubmitNewDAG(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               IRQueueNIB, RCNIBEventQueue, 
                                               RCSwSuspensionStatus, 
                                               RCIRStatus, NIBIRStatus, 
                                               SwSuspensionStatus, 
                                               SetScheduledIRs, 
                                               seqWorkerIsBusy, 
                                               eventHandlerCheckpoint, 
                                               eventHandlerTCAMCleared, 
                                               eventHandlerLastIRToReset, 
                                               ofcSubmoduleFailNum, 
                                               FirstInstall, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, nxtDAGVertices, 
                                               setRemovableIRs, 
                                               toBeScheduledIRs, nextIR, 
                                               currDAG, IRDoneSet, 
                                               nextIRObjectToSend, index, 
                                               stepOfFailureWP, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailureEH, msg, 
                                               irID, stepOfFailureMS >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ seqWorkerIsBusy = FALSE
                                     /\ DAGState' = [DAGState EXCEPT ![seqEvent[self].id] = DAG_NONE]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
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
                                                     SetScheduledIRs, 
                                                     seqWorkerIsBusy, 
                                                     eventHandlerCheckpoint, 
                                                     eventHandlerTCAMCleared, 
                                                     eventHandlerLastIRToReset, 
                                                     ofcSubmoduleFailNum, 
                                                     FirstInstall, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, nxtDAGVertices, 
                                                     setRemovableIRs, seqEvent, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRDoneSet, 
                                                     nextIRObjectToSend, index, 
                                                     stepOfFailureWP, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailureEH, msg, 
                                                     irID, stepOfFailureMS >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ Len(DAGQueue) > 0
                                 /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue)]
                                 /\ seqWorkerIsBusy' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 TEEventQueue, DAGEventQueue, 
                                                 DAGQueue, IRQueueNIB, 
                                                 RCNIBEventQueue, DAGState, 
                                                 RCSwSuspensionStatus, 
                                                 RCIRStatus, NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 SetScheduledIRs, 
                                                 eventHandlerCheckpoint, 
                                                 eventHandlerTCAMCleared, 
                                                 eventHandlerLastIRToReset, 
                                                 ofcSubmoduleFailNum, 
                                                 FirstInstall, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 nxtDAGVertices, 
                                                 setRemovableIRs, seqEvent, 
                                                 toBeScheduledIRs, nextIR, 
                                                 IRDoneSet, nextIRObjectToSend, 
                                                 index, stepOfFailureWP, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailureEH, msg, irID, 
                                                 stepOfFailureMS >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF dagObjectShouldBeProcessed(currDAG[self])
                                              THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(currDAG[self].dag)]
                                                   /\ toBeScheduledIRs'[self] # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                   /\ UNCHANGED << controllerLock, 
                                                                   seqWorkerIsBusy, 
                                                                   IRDoneSet >>
                                              ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = self
                                                   /\ seqWorkerIsBusy' = FALSE
                                                   /\ IF allIRsInDAGInstalled(currDAG[self].dag)
                                                         THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = AddDeleteDAGIRDoneSet(currDAG[self].dag.v, IRDoneSet[self])]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED IRDoneSet
                                                   /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]
                                                   /\ UNCHANGED toBeScheduledIRs
                                        /\ UNCHANGED << switchLock, 
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
                                                        SetScheduledIRs, 
                                                        eventHandlerCheckpoint, 
                                                        eventHandlerTCAMCleared, 
                                                        eventHandlerLastIRToReset, 
                                                        ofcSubmoduleFailNum, 
                                                        FirstInstall, event, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        DAGID, nxtDAG, 
                                                        nxtDAGVertices, 
                                                        setRemovableIRs, 
                                                        seqEvent, nextIR, 
                                                        currDAG, 
                                                        nextIRObjectToSend, 
                                                        index, stepOfFailureWP, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailureEH, msg, 
                                                        irID, stepOfFailureMS >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF toBeScheduledIRs[self] = {} \/ isDAGStale(currDAG[self].id)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                       /\ UNCHANGED << IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       toBeScheduledIRs, 
                                                       nextIR, IRDoneSet >>
                                  ELSE /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                                       /\ LET destination == getSwitchForIR(nextIR'[self]) IN
                                            /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![destination] = SetScheduledIRs[destination] \cup {nextIR'[self]}]
                                            /\ IF getIRType(nextIR'[self]) = INSTALL_FLOW
                                                  THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \cup {nextIR'[self]}]
                                                  ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \ {getDualOfIR(nextIR'[self])}]
                                            /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> nextIR'[self], sw |-> destination]), tag |-> NADIR_NULL])
                                            /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR'[self]}]
                                       /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, 
                                            RCNIBEventQueue, DAGState, 
                                            RCSwSuspensionStatus, RCIRStatus, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            seqWorkerIsBusy, 
                                            eventHandlerCheckpoint, 
                                            eventHandlerTCAMCleared, 
                                            eventHandlerLastIRToReset, 
                                            ofcSubmoduleFailNum, FirstInstall, 
                                            event, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            DAGID, nxtDAG, nxtDAGVertices, 
                                            setRemovableIRs, seqEvent, currDAG, 
                                            nextIRObjectToSend, index, 
                                            stepOfFailureWP, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailureEH, msg, irID, 
                                            stepOfFailureMS >>

RemoveDagFromQueue(self) == /\ pc[self] = "RemoveDagFromQueue"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                            /\ DAGQueue' = Tail(DAGQueue)
                            /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                            /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, IRQueueNIB, 
                                            RCNIBEventQueue, DAGState, 
                                            RCSwSuspensionStatus, RCIRStatus, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            SetScheduledIRs, seqWorkerIsBusy, 
                                            eventHandlerCheckpoint, 
                                            eventHandlerTCAMCleared, 
                                            eventHandlerLastIRToReset, 
                                            ofcSubmoduleFailNum, FirstInstall, 
                                            event, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            DAGID, nxtDAG, nxtDAGVertices, 
                                            setRemovableIRs, seqEvent, 
                                            toBeScheduledIRs, nextIR, currDAG, 
                                            IRDoneSet, nextIRObjectToSend, 
                                            index, stepOfFailureWP, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailureEH, msg, 
                                            irID, stepOfFailureMS >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ RemoveDagFromQueue(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ ExistsItemWithTag(IRQueueNIB, NADIR_NULL) \/ ExistsItemWithTag(IRQueueNIB, self)
                          /\ index' = [index EXCEPT ![self] = GetItemIndexWithTag(IRQueueNIB, self)]
                          /\ nextIRObjectToSend' = [nextIRObjectToSend EXCEPT ![self] = IRQueueNIB[index'[self]].data]
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![index'[self]].tag = self]
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, RCNIBEventQueue, DAGState, 
                                          RCSwSuspensionStatus, RCIRStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          SetScheduledIRs, seqWorkerIsBusy, 
                                          eventHandlerCheckpoint, 
                                          eventHandlerTCAMCleared, 
                                          eventHandlerLastIRToReset, 
                                          ofcSubmoduleFailNum, FirstInstall, 
                                          event, topoChangeEvent, 
                                          currSetDownSw, prev_dag_id, init, 
                                          DAGID, nxtDAG, nxtDAGVertices, 
                                          setRemovableIRs, seqEvent, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRDoneSet, stepOfFailureWP, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailureEH, msg, irID, 
                                          stepOfFailureMS >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF isClearIR(nextIRObjectToSend[self].IR)
                                      THEN /\ IF isSwitchSuspended(nextIRObjectToSend[self].sw)
                                                 THEN /\ IF (stepOfFailureWP[self] = 1)
                                                            THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                                 /\ nextIRObjectToSend' = [nextIRObjectToSend EXCEPT ![self] = NADIR_NULL]
                                                                 /\ index' = [index EXCEPT ![self] = 0]
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                                 /\ UNCHANGED << switchLock, 
                                                                                 controller2Switch >>
                                                            ELSE /\ IF isClearIR(nextIRObjectToSend[self].IR)
                                                                       THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                                               type |-> CLEAR_TCAM,
                                                                                                                                                                                                                               flow |-> 0,
                                                                                                                                                                                                                               to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                                               from |-> self[1]
                                                                                                                                                                                                                           ]))]
                                                                       ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                                               type |-> getIRType(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                                               flow |-> getPrimaryOfIR(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                                               to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                                               from |-> self[1]
                                                                                                                                                                                                                           ]))]
                                                                 /\ switchLock' = <<SW_SIMPLE_ID, nextIRObjectToSend[self].sw>>
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                                                 /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                                 nextIRObjectToSend, 
                                                                                 index >>
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                                      /\ UNCHANGED << switchLock, 
                                                                      controller2Switch, 
                                                                      ofcSubmoduleFailNum, 
                                                                      nextIRObjectToSend, 
                                                                      index >>
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                      ELSE /\ IF getNIBIRState(nextIRObjectToSend[self].IR) \in {IR_NONE, IR_SENT}
                                                 THEN /\ IF isSwitchSuspended(nextIRObjectToSend[self].sw)
                                                            THEN /\ IF (stepOfFailureWP[self] = 1)
                                                                       THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                                            /\ nextIRObjectToSend' = [nextIRObjectToSend EXCEPT ![self] = NADIR_NULL]
                                                                            /\ index' = [index EXCEPT ![self] = 0]
                                                                            /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                                            /\ UNCHANGED RCNIBEventQueue
                                                                       ELSE /\ RCNIBEventQueue' =                    Append(
                                                                                                      RCNIBEventQueue,
                                                                                                      [type |-> IR_FAILED, IR |-> nextIRObjectToSend[self].IR, state |-> IR_NONE]
                                                                                                  )
                                                                            /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                                                            /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                                            nextIRObjectToSend, 
                                                                                            index >>
                                                                 /\ UNCHANGED NIBIRStatus
                                                            ELSE /\ IF (stepOfFailureWP[self] = 1)
                                                                       THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                                            /\ nextIRObjectToSend' = [nextIRObjectToSend EXCEPT ![self] = NADIR_NULL]
                                                                            /\ index' = [index EXCEPT ![self] = 0]
                                                                            /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                                            /\ UNCHANGED << RCNIBEventQueue, 
                                                                                            NIBIRStatus >>
                                                                       ELSE /\ IF (isPrimary((nextIRObjectToSend[self].IR)))
                                                                                  THEN /\ IF IR_SENT = IR_DONE /\ NIBIRStatus[(nextIRObjectToSend[self].IR)].dual = IR_DONE
                                                                                             THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend[self].IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                             ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend[self].IR)].primary = IR_SENT]
                                                                                  ELSE /\ LET primary == getPrimaryOfIR((nextIRObjectToSend[self].IR)) IN
                                                                                            IF IR_SENT = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                                                               THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                               ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_SENT]
                                                                            /\ IF (stepOfFailureWP[self] = 2)
                                                                                  THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                                                       /\ nextIRObjectToSend' = [nextIRObjectToSend EXCEPT ![self] = NADIR_NULL]
                                                                                       /\ index' = [index EXCEPT ![self] = 0]
                                                                                       /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                                                       /\ UNCHANGED RCNIBEventQueue
                                                                                  ELSE /\ RCNIBEventQueue' =                    Append(
                                                                                                                 RCNIBEventQueue,
                                                                                                                 [type |-> IR_MOD, IR |-> nextIRObjectToSend[self].IR, state |-> IR_SENT]
                                                                                                             )
                                                                                       /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                                                       /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                                                       nextIRObjectToSend, 
                                                                                                       index >>
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                                      /\ UNCHANGED << RCNIBEventQueue, 
                                                                      NIBIRStatus, 
                                                                      ofcSubmoduleFailNum, 
                                                                      nextIRObjectToSend, 
                                                                      index >>
                                           /\ UNCHANGED << switchLock, 
                                                           controller2Switch >>
                                /\ UNCHANGED << controllerLock, 
                                                swSeqChangedStatus, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, DAGState, 
                                                RCSwSuspensionStatus, 
                                                RCIRStatus, SwSuspensionStatus, 
                                                SetScheduledIRs, 
                                                seqWorkerIsBusy, 
                                                eventHandlerCheckpoint, 
                                                eventHandlerTCAMCleared, 
                                                eventHandlerLastIRToReset, 
                                                FirstInstall, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, nxtDAGVertices, 
                                                setRemovableIRs, seqEvent, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRDoneSet, 
                                                stepOfFailureWP, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailureEH, msg, 
                                                irID, stepOfFailureMS >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (stepOfFailureWP[self] = 1)
                                         THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                              /\ nextIRObjectToSend' = [nextIRObjectToSend EXCEPT ![self] = NADIR_NULL]
                                              /\ index' = [index EXCEPT ![self] = 0]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                              /\ UNCHANGED << switchLock, 
                                                              controller2Switch >>
                                         ELSE /\ IF isClearIR(nextIRObjectToSend[self].IR)
                                                    THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                            type |-> CLEAR_TCAM,
                                                                                                                                                                                                            flow |-> 0,
                                                                                                                                                                                                            to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                            from |-> self[1]
                                                                                                                                                                                                        ]))]
                                                    ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                            type |-> getIRType(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                            flow |-> getPrimaryOfIR(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                            to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                            from |-> self[1]
                                                                                                                                                                                                        ]))]
                                              /\ switchLock' = <<SW_SIMPLE_ID, nextIRObjectToSend[self].sw>>
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                              /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                              nextIRObjectToSend, 
                                                              index >>
                                   /\ UNCHANGED << controllerLock, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   RCNIBEventQueue, DAGState, 
                                                   RCSwSuspensionStatus, 
                                                   RCIRStatus, NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   SetScheduledIRs, 
                                                   seqWorkerIsBusy, 
                                                   eventHandlerCheckpoint, 
                                                   eventHandlerTCAMCleared, 
                                                   eventHandlerLastIRToReset, 
                                                   FirstInstall, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   nxtDAGVertices, 
                                                   setRemovableIRs, seqEvent, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRDoneSet, 
                                                   stepOfFailureWP, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailureEH, msg, irID, 
                                                   stepOfFailureMS >>

ControllerThreadRemoveIRFromQueue(self) == /\ pc[self] = "ControllerThreadRemoveIRFromQueue"
                                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ IF (stepOfFailureWP[self] = 1)
                                                 THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                      /\ nextIRObjectToSend' = [nextIRObjectToSend EXCEPT ![self] = NADIR_NULL]
                                                      /\ index' = [index EXCEPT ![self] = 0]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                      /\ UNCHANGED IRQueueNIB
                                                 ELSE /\ index' = [index EXCEPT ![self] = GetFirstItemIndexWithTag(IRQueueNIB, self)]
                                                      /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index'[self])
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                      /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                      nextIRObjectToSend >>
                                           /\ UNCHANGED << switchLock, 
                                                           controllerLock, 
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
                                                           SetScheduledIRs, 
                                                           seqWorkerIsBusy, 
                                                           eventHandlerCheckpoint, 
                                                           eventHandlerTCAMCleared, 
                                                           eventHandlerLastIRToReset, 
                                                           FirstInstall, event, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           prev_dag_id, init, 
                                                           DAGID, nxtDAG, 
                                                           nxtDAGVertices, 
                                                           setRemovableIRs, 
                                                           seqEvent, 
                                                           toBeScheduledIRs, 
                                                           nextIR, currDAG, 
                                                           IRDoneSet, 
                                                           stepOfFailureWP, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, 
                                                           stepOfFailureEH, 
                                                           msg, irID, 
                                                           stepOfFailureMS >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadRemoveIRFromQueue(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerLock' = self
                                    /\ Len(swSeqChangedStatus) > 0
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendRunningSw(monitoringEvent'[self])
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF shouldClearSuspendedSw(monitoringEvent'[self])
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerRequestTCAMClear"]
                                                     ELSE /\ IF shouldFreeSuspendedSw(monitoringEvent'[self])
                                                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << switchLock, 
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
                                                    SetScheduledIRs, 
                                                    seqWorkerIsBusy, 
                                                    eventHandlerCheckpoint, 
                                                    eventHandlerTCAMCleared, 
                                                    eventHandlerLastIRToReset, 
                                                    ofcSubmoduleFailNum, 
                                                    FirstInstall, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    nxtDAGVertices, 
                                                    setRemovableIRs, seqEvent, 
                                                    toBeScheduledIRs, nextIR, 
                                                    currDAG, IRDoneSet, 
                                                    nextIRObjectToSend, index, 
                                                    stepOfFailureWP, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailureEH, msg, irID, 
                                                    stepOfFailureMS >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (ofcSubmoduleFailNum[self] < maxFailure(self))
                                                         THEN /\ \E num \in 0..2:
                                                                   stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = num]
                                                         ELSE /\ stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = 0]
                                                   /\ IF (stepOfFailureEH'[self] = 1)
                                                         THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                              /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                              /\ UNCHANGED << swSeqChangedStatus, 
                                                                              eventHandlerCheckpoint, 
                                                                              eventHandlerTCAMCleared, 
                                                                              eventHandlerLastIRToReset >>
                                                         ELSE /\ eventHandlerCheckpoint' = FALSE
                                                              /\ eventHandlerTCAMCleared' = FALSE
                                                              /\ eventHandlerLastIRToReset' = NADIR_NULL
                                                              /\ IF (stepOfFailureEH'[self] = 2)
                                                                    THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                                         /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                                                         /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                                         /\ UNCHANGED swSeqChangedStatus
                                                                    ELSE /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                                         /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                                         /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                                         monitoringEvent >>
                                                   /\ UNCHANGED << switchLock, 
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
                                                                   SetScheduledIRs, 
                                                                   seqWorkerIsBusy, 
                                                                   FirstInstall, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, DAGID, 
                                                                   nxtDAG, 
                                                                   nxtDAGVertices, 
                                                                   setRemovableIRs, 
                                                                   seqEvent, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   currDAG, 
                                                                   IRDoneSet, 
                                                                   nextIRObjectToSend, 
                                                                   index, 
                                                                   stepOfFailureWP, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   stepOfFailureMS >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ IF (ofcSubmoduleFailNum[self] < maxFailure(self))
                                   THEN /\ \E num \in 0..2:
                                             stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = num]
                                   ELSE /\ stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = 0]
                             /\ eventHandlerCheckpoint' = TRUE
                             /\ IF (stepOfFailureEH'[self] = 1)
                                   THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                        /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED << RCNIBEventQueue, 
                                                        SwSuspensionStatus >>
                                   ELSE /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                                        /\ IF (stepOfFailureEH'[self] = 2)
                                              THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                   /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                   /\ UNCHANGED RCNIBEventQueue
                                              ELSE /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND]))
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                   /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                   monitoringEvent >>
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, DAGState, 
                                             RCSwSuspensionStatus, RCIRStatus, 
                                             NIBIRStatus, SetScheduledIRs, 
                                             seqWorkerIsBusy, 
                                             eventHandlerTCAMCleared, 
                                             eventHandlerLastIRToReset, 
                                             FirstInstall, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, nxtDAG, 
                                             nxtDAGVertices, setRemovableIRs, 
                                             seqEvent, toBeScheduledIRs, 
                                             nextIR, currDAG, IRDoneSet, 
                                             nextIRObjectToSend, index, 
                                             stepOfFailureWP, setIRsToReset, 
                                             resetIR, msg, irID, 
                                             stepOfFailureMS >>

ControllerRequestTCAMClear(self) == /\ pc[self] = "ControllerRequestTCAMClear"
                                    /\ IF (ofcSubmoduleFailNum[self] < maxFailure(self))
                                          THEN /\ \E num \in 0..1:
                                                    stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = num]
                                          ELSE /\ stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = 0]
                                    /\ IF (stepOfFailureEH'[self] = 1)
                                          THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                               /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                               /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                               /\ UNCHANGED IRQueueNIB
                                          ELSE /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                     THEN /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> 0, sw |-> monitoringEvent[self].swID]), tag |-> NADIR_NULL])
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED IRQueueNIB
                                               /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                               /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                               monitoringEvent >>
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    RCNIBEventQueue, DAGState, 
                                                    RCSwSuspensionStatus, 
                                                    RCIRStatus, NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    SetScheduledIRs, 
                                                    seqWorkerIsBusy, 
                                                    eventHandlerCheckpoint, 
                                                    eventHandlerTCAMCleared, 
                                                    eventHandlerLastIRToReset, 
                                                    FirstInstall, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    nxtDAGVertices, 
                                                    setRemovableIRs, seqEvent, 
                                                    toBeScheduledIRs, nextIR, 
                                                    currDAG, IRDoneSet, 
                                                    nextIRObjectToSend, index, 
                                                    stepOfFailureWP, 
                                                    setIRsToReset, resetIR, 
                                                    msg, irID, stepOfFailureMS >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self]) /\ ~eventHandlerTCAMCleared
                                                THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                          /\ UNCHANGED << switchLock, 
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
                                                          SetScheduledIRs, 
                                                          seqWorkerIsBusy, 
                                                          eventHandlerCheckpoint, 
                                                          eventHandlerTCAMCleared, 
                                                          eventHandlerLastIRToReset, 
                                                          ofcSubmoduleFailNum, 
                                                          FirstInstall, event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, nxtDAG, 
                                                          nxtDAGVertices, 
                                                          setRemovableIRs, 
                                                          seqEvent, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRDoneSet, 
                                                          nextIRObjectToSend, 
                                                          index, 
                                                          stepOfFailureWP, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailureEH, msg, 
                                                          irID, 
                                                          stepOfFailureMS >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = getIRSetToReset(monitoringEvent[self].swID)]
                           /\ IF (setIRsToReset'[self] = {})
                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, IRQueueNIB, 
                                           RCNIBEventQueue, DAGState, 
                                           RCSwSuspensionStatus, RCIRStatus, 
                                           NIBIRStatus, SwSuspensionStatus, 
                                           SetScheduledIRs, seqWorkerIsBusy, 
                                           eventHandlerCheckpoint, 
                                           eventHandlerTCAMCleared, 
                                           eventHandlerLastIRToReset, 
                                           ofcSubmoduleFailNum, FirstInstall, 
                                           event, topoChangeEvent, 
                                           currSetDownSw, prev_dag_id, init, 
                                           DAGID, nxtDAG, nxtDAGVertices, 
                                           setRemovableIRs, seqEvent, 
                                           toBeScheduledIRs, nextIR, currDAG, 
                                           IRDoneSet, nextIRObjectToSend, 
                                           index, stepOfFailureWP, 
                                           monitoringEvent, resetIR, 
                                           stepOfFailureEH, msg, irID, 
                                           stepOfFailureMS >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ IF (ofcSubmoduleFailNum[self] < maxFailure(self))
                           THEN /\ \E num \in 0..2:
                                     stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = num]
                           ELSE /\ stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = 0]
                     /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                     /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                     /\ IF (stepOfFailureEH'[self] = 1)
                           THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                /\ UNCHANGED << RCNIBEventQueue, NIBIRStatus, 
                                                eventHandlerLastIRToReset >>
                           ELSE /\ eventHandlerLastIRToReset' = resetIR'[self]
                                /\ IF (isPrimary(resetIR'[self]))
                                      THEN /\ IF IR_NONE = IR_DONE /\ NIBIRStatus[resetIR'[self]].dual = IR_DONE
                                                 THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                 ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]].primary = IR_NONE]
                                      ELSE /\ LET primary == getPrimaryOfIR(resetIR'[self]) IN
                                                IF IR_NONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                   THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                   ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_NONE]
                                /\ IF (stepOfFailureEH'[self] = 2)
                                      THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                           /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                           /\ UNCHANGED RCNIBEventQueue
                                      ELSE /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> resetIR'[self], state |-> IR_NONE]))
                                           /\ IF setIRsToReset'[self] = {}
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                           /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                           monitoringEvent >>
                     /\ UNCHANGED << switchLock, controllerLock, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, IRQueueNIB, 
                                     DAGState, RCSwSuspensionStatus, 
                                     RCIRStatus, SwSuspensionStatus, 
                                     SetScheduledIRs, seqWorkerIsBusy, 
                                     eventHandlerCheckpoint, 
                                     eventHandlerTCAMCleared, FirstInstall, 
                                     event, topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     nxtDAGVertices, setRemovableIRs, seqEvent, 
                                     toBeScheduledIRs, nextIR, currDAG, 
                                     IRDoneSet, nextIRObjectToSend, index, 
                                     stepOfFailureWP, msg, irID, 
                                     stepOfFailureMS >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerLock' = self
                                   /\ IF (ofcSubmoduleFailNum[self] < maxFailure(self))
                                         THEN /\ \E num \in 0..3:
                                                   stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailureEH' = [stepOfFailureEH EXCEPT ![self] = 0]
                                   /\ eventHandlerCheckpoint' = TRUE
                                   /\ eventHandlerLastIRToReset' = NADIR_NULL
                                   /\ IF (stepOfFailureEH'[self] = 1)
                                         THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                              /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                              SwSuspensionStatus, 
                                                              eventHandlerTCAMCleared >>
                                         ELSE /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                              /\ IF (stepOfFailureEH'[self] = 2)
                                                    THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                         /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                                         /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                         /\ UNCHANGED << RCNIBEventQueue, 
                                                                         eventHandlerTCAMCleared >>
                                                    ELSE /\ eventHandlerTCAMCleared' = TRUE
                                                         /\ IF (stepOfFailureEH'[self] = 3)
                                                               THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = NADIR_NULL]
                                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                                    /\ UNCHANGED RCNIBEventQueue
                                                               ELSE /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_RUN]))
                                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                                    /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                                    monitoringEvent >>
                                   /\ UNCHANGED << switchLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   DAGState, 
                                                   RCSwSuspensionStatus, 
                                                   RCIRStatus, NIBIRStatus, 
                                                   SetScheduledIRs, 
                                                   seqWorkerIsBusy, 
                                                   FirstInstall, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   nxtDAGVertices, 
                                                   setRemovableIRs, seqEvent, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRDoneSet, 
                                                   nextIRObjectToSend, index, 
                                                   stepOfFailureWP, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, stepOfFailureMS >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ LET lastIR == eventHandlerLastIRToReset IN
                                                        IF lastIR # NADIR_NULL
                                                           THEN /\ IF (isPrimary(lastIR))
                                                                      THEN /\ IF IR_NONE = IR_DONE /\ NIBIRStatus[lastIR].dual = IR_DONE
                                                                                 THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![lastIR] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                 ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![lastIR].primary = IR_NONE]
                                                                      ELSE /\ LET primary == getPrimaryOfIR(lastIR) IN
                                                                                IF IR_NONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                                                   THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                   ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_NONE]
                                                                /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> lastIR, state |-> IR_NONE]))
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << RCNIBEventQueue, 
                                                                                NIBIRStatus >>
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   controllerLock, 
                                                                   swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   IRQueueNIB, 
                                                                   DAGState, 
                                                                   RCSwSuspensionStatus, 
                                                                   RCIRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   SetScheduledIRs, 
                                                                   seqWorkerIsBusy, 
                                                                   eventHandlerCheckpoint, 
                                                                   eventHandlerTCAMCleared, 
                                                                   eventHandlerLastIRToReset, 
                                                                   ofcSubmoduleFailNum, 
                                                                   FirstInstall, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, DAGID, 
                                                                   nxtDAG, 
                                                                   nxtDAGVertices, 
                                                                   setRemovableIRs, 
                                                                   seqEvent, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   currDAG, 
                                                                   IRDoneSet, 
                                                                   nextIRObjectToSend, 
                                                                   index, 
                                                                   stepOfFailureWP, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailureEH, 
                                                                   msg, irID, 
                                                                   stepOfFailureMS >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerRequestTCAMClear(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = self
                                       /\ Len(switch2Controller) > 0
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ IF msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerProcessIRMod"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ForwardToEH"]
                                       /\ UNCHANGED << switchLock, 
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
                                                       SetScheduledIRs, 
                                                       seqWorkerIsBusy, 
                                                       eventHandlerCheckpoint, 
                                                       eventHandlerTCAMCleared, 
                                                       eventHandlerLastIRToReset, 
                                                       ofcSubmoduleFailNum, 
                                                       FirstInstall, event, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       DAGID, nxtDAG, 
                                                       nxtDAGVertices, 
                                                       setRemovableIRs, 
                                                       seqEvent, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, 
                                                       IRDoneSet, 
                                                       nextIRObjectToSend, 
                                                       index, stepOfFailureWP, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailureEH, irID, 
                                                       stepOfFailureMS >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                         /\ IF (stepOfFailureMS[self] = 1)
                                               THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                    /\ msg' = [msg EXCEPT ![self] = NADIR_NULL]
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                    /\ UNCHANGED switch2Controller
                                               ELSE /\ switch2Controller' = Tail(switch2Controller)
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                    /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                    msg >>
                                         /\ UNCHANGED << switchLock, 
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
                                                         SetScheduledIRs, 
                                                         seqWorkerIsBusy, 
                                                         eventHandlerCheckpoint, 
                                                         eventHandlerTCAMCleared, 
                                                         eventHandlerLastIRToReset, 
                                                         FirstInstall, event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         DAGID, nxtDAG, 
                                                         nxtDAGVertices, 
                                                         setRemovableIRs, 
                                                         seqEvent, 
                                                         toBeScheduledIRs, 
                                                         nextIR, currDAG, 
                                                         IRDoneSet, 
                                                         nextIRObjectToSend, 
                                                         index, 
                                                         stepOfFailureWP, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailureEH, irID, 
                                                         stepOfFailureMS >>

ControllerProcessIRMod(self) == /\ pc[self] = "ControllerProcessIRMod"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg[self].flow, msg[self].type)]
                                /\ FirstInstall' = [FirstInstall EXCEPT ![irID'[self]] = 1]
                                /\ IF (stepOfFailureMS[self] = 1)
                                      THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                           /\ msg' = [msg EXCEPT ![self] = NADIR_NULL]
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                      ELSE /\ IF (isPrimary(irID'[self]))
                                                 THEN /\ IF IR_DONE = IR_DONE /\ NIBIRStatus[irID'[self]].dual = IR_DONE
                                                            THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID'[self]] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                            ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID'[self]].primary = IR_DONE]
                                                 ELSE /\ LET primary == getPrimaryOfIR(irID'[self]) IN
                                                           IF IR_DONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                              THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                              ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_DONE]
                                           /\ IF (stepOfFailureMS[self] = 2)
                                                 THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                                      /\ msg' = [msg EXCEPT ![self] = NADIR_NULL]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                      /\ UNCHANGED RCNIBEventQueue
                                                 ELSE /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> irID'[self], state |-> IR_DONE]))
                                                      /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                                      /\ UNCHANGED << ofcSubmoduleFailNum, 
                                                                      msg >>
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, DAGState, 
                                                RCSwSuspensionStatus, 
                                                RCIRStatus, SwSuspensionStatus, 
                                                SetScheduledIRs, 
                                                seqWorkerIsBusy, 
                                                eventHandlerCheckpoint, 
                                                eventHandlerTCAMCleared, 
                                                eventHandlerLastIRToReset, 
                                                event, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, DAGID, nxtDAG, 
                                                nxtDAGVertices, 
                                                setRemovableIRs, seqEvent, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRDoneSet, 
                                                nextIRObjectToSend, index, 
                                                stepOfFailureWP, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailureEH, 
                                                stepOfFailureMS >>

ForwardToEH(self) == /\ pc[self] = "ForwardToEH"
                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ IF (stepOfFailureMS[self] = 1)
                           THEN /\ ofcSubmoduleFailNum' = [ofcSubmoduleFailNum EXCEPT ![self] = ofcSubmoduleFailNum[self] + 1]
                                /\ msg' = [msg EXCEPT ![self] = NADIR_NULL]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                /\ UNCHANGED swSeqChangedStatus
                           ELSE /\ swSeqChangedStatus' = Append(swSeqChangedStatus, msg[self])
                                /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                /\ UNCHANGED << ofcSubmoduleFailNum, msg >>
                     /\ UNCHANGED << switchLock, controllerLock, 
                                     controller2Switch, switch2Controller, 
                                     TEEventQueue, DAGEventQueue, DAGQueue, 
                                     IRQueueNIB, RCNIBEventQueue, DAGState, 
                                     RCSwSuspensionStatus, RCIRStatus, 
                                     NIBIRStatus, SwSuspensionStatus, 
                                     SetScheduledIRs, seqWorkerIsBusy, 
                                     eventHandlerCheckpoint, 
                                     eventHandlerTCAMCleared, 
                                     eventHandlerLastIRToReset, FirstInstall, 
                                     event, topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     nxtDAGVertices, setRemovableIRs, seqEvent, 
                                     toBeScheduledIRs, nextIR, currDAG, 
                                     IRDoneSet, nextIRObjectToSend, index, 
                                     stepOfFailureWP, monitoringEvent, 
                                     setIRsToReset, resetIR, stepOfFailureEH, 
                                     irID, stepOfFailureMS >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerProcessIRMod(self)
                                       \/ ForwardToEH(self)

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

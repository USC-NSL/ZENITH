------------------- MODULE zenith_nr_simplified -------------------
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
        switchLock = <<NO_LOCK, NO_LOCK>>,
        controllerLock = <<NO_LOCK, NO_LOCK>>, 

        controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0],
        controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed],

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
        
        ir2sw = IR2SW,
        seqWorkerIsBusy = FALSE
    define
        moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
        getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                                     [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0
        returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                                   /\ controllerSubmoduleFailStat[x] = Failed}
        
        getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}
        getSetRemovableIRs(swSet, nxtDAGV) == {x \in DOMAIN RCIRStatus: /\ x \leq MaxNumIRs
                                                                        /\ x \notin nxtDAGV
                                                                        /\ ir2sw[x] \in swSet
                                                                        /\ \/ RCIRStatus[x] # IR_NONE
                                                                           \/ x \in SetScheduledIRs[ir2sw[x]]}
        getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: ir2sw[x] = swID}
        isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                           /\ RCIRStatus[y] # IR_DONE
        getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ RCIRStatus[x] = IR_NONE
                                                           /\ isDependencySatisfied(DAG, x)
                                                           /\ RCSwSuspensionStatus[ir2sw[x]] = SW_RUN
                                                           /\ x \notin SetScheduledIRs[ir2sw[x]]}
        getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN ir + MaxNumIRs
                                                ELSE ir - MaxNumIRs
        getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW
                                                  ELSE DELETE_FLOW
        getIRFlow(irID) == IF irID \leq MaxNumIRs THEN irID
                                                  ELSE irID - MaxNumIRs
        getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                             ELSE flowID + MaxNumIRs
        allIRsInDAGInstalled(DAG) == ~\E y \in DOMAIN RCIRStatus: /\ y \leq MaxNumIRs
                                                                  /\ y \in DAG.v
                                                                  /\ RCIRStatus[y] # IR_DONE
        allIRsInDAGAreStable(DAG) == ~\E y \in DOMAIN RCIRStatus: /\ y \leq MaxNumIRs
                                                                  /\ y \in DAG.v
                                                                  /\ getIRType(y) = INSTALL_FLOW
                                                                  /\ RCIRStatus[y] = IR_DONE
                                                                  /\ getDualOfIR(y) \in DOMAIN RCIRStatus
                                                                  /\ \/ RCIRStatus[getDualOfIR(y)] # IR_NONE
                                                                     \/ getDualOfIR(y) \in SetScheduledIRs[ir2sw[getDualOfIR(y)]]
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
        getIRSetToReset(SID) == {x \in DOMAIN NIBIRStatus: /\ x \leq MaxNumIRs
                                                           /\ ir2sw[x] = SID
                                                           /\ NIBIRStatus[x] \notin {IR_NONE}}
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

    macro controllerModuleFails()
    begin
        controllerSubmoduleFailStat[self] := Failed;
        controllerSubmoduleFailNum[self[1]] := controllerSubmoduleFailNum[self[1]] + 1;
    end macro;

    macro controllerModuleFailOrNot()
    begin
        if (controllerSubmoduleFailStat[self] = NotFailed /\ 
                    controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])) then           
            either
                controllerModuleFails();
            or
                skip;
            end either;
        end if;
    end macro;

    macro whichStepToFail(numSteps)
    begin
        if (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])) then
            with num \in 0..numSteps do
                stepOfFailure := num;
            end with;
        else
            stepOfFailure := 0;
        end if;
    end macro;

    macro controllerSendIR(irID)
    begin
        with destination = ir2sw[irID] do
            NadirFanoutFIFOPut(
                controller2Switch,
                destination,
                [type |-> getIRType(irID), flow |-> getIRFlow(irID), to |-> destination, from |-> self[1]]
            );
        end with; 
    end macro;

    macro prepareDeletionIR(forWhat, DID)
    begin
        if (DID \notin DOMAIN RCIRStatus) then
            RCIRStatus    := RCIRStatus    @@ (DID :> IR_NONE);
            NIBIRStatus   := NIBIRStatus   @@ (DID :> IR_NONE);
            ir2sw         := ir2sw         @@ (DID :> ir2sw[forWhat]);
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

    fair process rcNibEventHandler \in ({rc0} \X {NIB_EVENT_HANDLER})
    variables event = NADIR_NULL;
    begin
    RCSNIBEventHndlerProc:
    while TRUE do
        await moduleIsUp(self);
        NadirFIFOPeek(RCNIBEventQueue, event);
        controllerWaitForLockFree();
        if (event.type = TOPO_MOD) then
            if RCSwSuspensionStatus[event.sw] # event.state then    
                RCSwSuspensionStatus[event.sw] := event.state;
                NadirFIFOPut(TEEventQueue, event);
            end if;
        elsif (event.type = IR_MOD) then
            if RCIRStatus[event.IR] # event.state then
                RCIRStatus[event.IR] := event.state;
                SetScheduledIRs[ir2sw[event.IR]] := SetScheduledIRs[ir2sw[event.IR]]\{event.IR};
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
        await moduleIsUp(self);
        controllerAcquireLock();
        if init = 1 then
            goto ControllerTEComputeDagBasedOnTopo;
        else
            NadirFIFOPeek(TEEventQueue, topoChangeEvent);
        end if;
        
        ControllerTEEventProcessing:
            while topoChangeEvent # NADIR_NULL do 
                controllerWaitForLockFree();
                if topoChangeEvent.state = SW_SUSPEND then
                    currSetDownSw := currSetDownSw \cup {topoChangeEvent.sw};
                else
                    currSetDownSw := currSetDownSw \ {topoChangeEvent.sw};
                end if; 
                NadirFIFOPop(TEEventQueue);
                NadirFIFOPeekWithTimeout(TEEventQueue, topoChangeEvent);
            end while;
            controllerReleaseLock();
        
        ControllerTEComputeDagBasedOnTopo:
            controllerWaitForLockFree();
            getNextDAGID();
            nxtDAG := [id |-> DAGID, dag |-> TOPO_DAG_MAPPING[currSetDownSw]];
            if prev_dag = nxtDAG.dag then
                goto ControllerTEProc;
            else
                nxtDAGVertices := nxtDAG.dag.v;
                if init = 0 then
                    DAGState[prev_dag_id] := DAG_STALE;
                
                    ControllerTESendDagStaleNotif:
                        controllerWaitForLockFree();
                        NadirFIFOPut(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id]);
                
                    ControllerTEWaitForStaleDAGToBeRemoved:
                        controllerWaitForLockFree();
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
                controllerAcquireLock();
                currIR := CHOOSE x \in setRemovableIRs: TRUE;
                setRemovableIRs := setRemovableIRs \ {currIR};
                deleterID := getDualOfIR(currIR);
                prepareDeletionIR(currIR, deleterID);
                nxtDAG.dag.v := nxtDAG.dag.v \cup {deleterID};
                setIRsInDAG := getSetIRsForSwitchInDAG(ir2sw[currIR], nxtDAGVertices); 
                
                ControllerTEAddEdge:
                    while setIRsInDAG # {} do
                        controllerAcquireLock();
                        currIRInDAG := CHOOSE x \in setIRsInDAG: TRUE;
                        setIRsInDAG := setIRsInDAG \ {currIRInDAG};
                        nxtDAG.dag.e := nxtDAG.dag.e \cup {<<deleterID, currIRInDAG>>};
                    end while;           
                    controllerAcquireLock();  
            end while;
            controllerReleaseLock();
            SetScheduledIRs := [x \in SW |-> (SetScheduledIRs[x] \ nxtDAG.dag.v)];
            
        ControllerTESubmitNewDAG:
            controllerWaitForLockFree();
            DAGState[nxtDAG.id] := DAG_SUBMIT;
            NadirFIFOPut(DAGEventQueue, [type |-> DAG_NEW, dag_obj |-> nxtDAG]);
    
    end while;
    end process

    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    variables seqEvent = NADIR_NULL, worker = NADIR_NULL;
    begin
    ControllerBossSeqProc:
    while TRUE do
        await moduleIsUp(self);
        NadirFIFOGet(DAGEventQueue, seqEvent);
        controllerWaitForLockFree();
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
    variables toBeScheduledIRs = {}, nextIR = NADIR_NULL, currDAG = NADIR_NULL, IRSet = {}, IRDoneSet = {}, stepOfFailure = 0;
    begin
    ControllerWorkerSeqProc:
    while TRUE do
        await moduleIsUp(self);
        NadirFIFOPeek(DAGQueue, currDAG);
        controllerWaitForLockFree();
        seqWorkerIsBusy := TRUE;
        
        ControllerWorkerSeqScheduleDAG:
        while dagObjectShouldBeProcessed(currDAG) do
            controllerWaitForLockFree();
            toBeScheduledIRs := getSetIRsCanBeScheduledNext(currDAG.dag);
            await toBeScheduledIRs # {};

            SchedulerMechanism:
            while TRUE do
                controllerWaitForLockFree();
                whichStepToFail(3);
                if (stepOfFailure # 1) then
                    nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                    if (stepOfFailure # 2) then
                        rcInternalState[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
                        if (stepOfFailure # 3) then
                            SetScheduledIRs[ir2sw[nextIR]] := SetScheduledIRs[ir2sw[nextIR]] \cup {nextIR};                    
                        end if;
                    end if;
                end if;
        
                if (stepOfFailure # 0) then    
                    controllerModuleFails();
                    goto ControllerSeqStateReconciliation; 
                end if;
                
                AddDeleteIRIRDoneSet:      
                    if getIRType(nextIR) = INSTALL_FLOW then
                        IRDoneSet := IRDoneSet \cup {nextIR};
                    else
                        IRDoneSet := IRDoneSet \ {getDualOfIR(nextIR)}
                    end if;

                ScheduleTheIR: 
                    controllerWaitForLockFree();
                    whichStepToFail(2);
                    if (stepOfFailure # 1) then
                        NadirAckQueuePut(IRQueueNIB, nextIR);
                        toBeScheduledIRs := toBeScheduledIRs \ {nextIR};
                        if (stepOfFailure # 2) then
                            rcInternalState[self] := [type |-> NO_STATUS];    
                        end if;
                    end if;
            
                    if (stepOfFailure # 0) then    
                        controllerModuleFails();
                        goto ControllerSeqStateReconciliation;
                    elsif toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then
                        goto ControllerWorkerSeqScheduleDAG;
                    end if;
            end while;                                                
        end while;

        controllerAcquireLock();
        seqWorkerIsBusy := FALSE;
        IRSet := currDAG.dag.v;
        
        AddDeleteDAGIRDoneSet:
        while IRSet # {} /\ allIRsInDAGInstalled(currDAG.dag) do
            controllerWaitForLockFree();
            nextIR := CHOOSE x \in IRSet: TRUE;
            if getIRType(nextIR) = INSTALL_FLOW then
                IRDoneSet := IRDoneSet \cup {nextIR};
            else
                IRDoneSet := IRDoneSet \ {getDualOfIR(nextIR)}
            end if;
            IRSet := IRSet \ {nextIR};
        end while;
        NadirFIFOPop(DAGQueue);
    end while;
    
    ControllerSeqStateReconciliation:
        await moduleIsUp(self);
        controllerReleaseLock();
        if(rcInternalState[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[ir2sw[rcInternalState[self].next]] := 
                        SetScheduledIRs[ir2sw[rcInternalState[self].next]] \ {rcInternalState[self].next};
        end if;
        goto ControllerWorkerSeqProc;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRIDToSend = NADIR_NULL, index = NADIR_NULL, stepOfFailure = 0;
    begin
    ControllerThread:
    while TRUE do
        await moduleIsUp(self);
        controllerWaitForLockFree();
        NadirAckQueueGet(IRQueueNIB, self, index, nextIRIDToSend);

        whichStepToFail(1);
        if (stepOfFailure = 1) then
            controllerModuleFails();
            goto ControllerThreadStateReconciliation;
        else
            ofcInternalState[self] := [type |-> STATUS_LOCKING, next |-> nextIRIDToSend];
        end if;
        
        ControllerThreadSendIR:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                if ~isSwitchSuspended(ir2sw[nextIRIDToSend]) /\ NIBIRStatus[nextIRIDToSend] = IR_NONE then
                    NIBIRStatus[nextIRIDToSend] := IR_SENT;
                    NadirFIFOPut(
                        RCNIBEventQueue,
                        [type |-> IR_MOD, IR |-> nextIRIDToSend, state |-> IR_SENT]
                    );
                    
                    ControllerThreadForwardIR:
                        controllerWaitForLockFree();
                        whichStepToFail(2);
                        if (stepOfFailure # 1) then
                            controllerSendIR(nextIRIDToSend);
                            if (stepOfFailure # 2) then
                               ofcInternalState[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRIDToSend];
                            end if;
                        end if;                          
                        if (stepOfFailure # 0) then
                            controllerModuleFails();
                            goto ControllerThreadStateReconciliation;
                        end if;
                end if;
            else
                goto ControllerThreadStateReconciliation;
            end if;
        
        RemoveFromScheduledIRSet:
            controllerWaitForLockFree();
            whichStepToFail(2);
            if (stepOfFailure # 1) then
                ofcInternalState[self] := [type |-> NO_STATUS];
                if (stepOfFailure # 2) then
                    NadirAckQueueAck(IRQueueNIB, self, index);
                end if;
            end if;
            
            if (stepOfFailure # 0) then
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            end if;
    end while;
    
    ControllerThreadStateReconciliation:
        await moduleIsUp(self);
        controllerReleaseLock();
        if (ofcInternalState[self].type = STATUS_LOCKING) then
            if (NIBIRStatus[ofcInternalState[self].next] = IR_SENT) then
                NIBIRStatus[ofcInternalState[self].next] := IR_NONE;
            end if;
        end if;
        goto ControllerThread;
    end process

    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = NADIR_NULL, setIRsToReset = {}, resetIR = NADIR_NULL, stepOfFailure = 0;
    begin
    ControllerEventHandlerProc:
    while TRUE do  
        await moduleIsUp(self);
        controllerAcquireLock();
        NadirFIFOPeek(swSeqChangedStatus, monitoringEvent);
        if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            ControllerEventHandlerSuspendSW:
                controllerWaitForLockFree();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                    NadirFIFOPut(
                        RCNIBEventQueue,
                        [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]
                    );
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
                
        elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            ControllerCheckIfThisIsLastEvent:
                controllerReleaseLock();
                controllerModuleFailOrNot();
                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    getIRsToBeChecked:
                        controllerWaitForLockFree();
                        controllerModuleFailOrNot();
                        if (controllerSubmoduleFailStat[self] = NotFailed) then
                            setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                            if (setIRsToReset = {}) then
                                goto ControllerFreeSuspendedSW;
                            end if;
                        else
                            goto ControllerEventHandlerStateReconciliation;
                        end if;

                    ResetAllIRs:
                    while TRUE do
                        controllerWaitForLockFree();
                        controllerModuleFailOrNot();
                        if (controllerSubmoduleFailStat[self] = NotFailed) then
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
                        else
                            goto ControllerEventHandlerStateReconciliation;
                        end if;
                    end while;
                end if;

            
            ControllerFreeSuspendedSW:
                controllerAcquireLock();
                whichStepToFail(2);
                if (stepOfFailure # 1) then
                    ofcInternalState[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                    if (stepOfFailure # 2) then
                        SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                        NadirFIFOPut(
                            RCNIBEventQueue,
                            [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]
                        );
                    end if;
                end if;

                if (stepOfFailure # 0) then
                    controllerModuleFails();
                    goto ControllerEventHandlerStateReconciliation;
                end if;
        end if;
        
        ControllerEvenHanlderRemoveEventFromQueue:
            controllerReleaseLock();
            whichStepToFail(2);
            if (stepOfFailure # 1) then 
                ofcInternalState[self] := [type |-> NO_STATUS]; 
                if (stepOfFailure # 2) then
                    NadirFIFOPop(swSeqChangedStatus);
                end if;
            end if;
            
            if (stepOfFailure # 0) then
                controllerModuleFails();
                goto ControllerEventHandlerStateReconciliation;
            end if;
    end while;

    ControllerEventHandlerStateReconciliation:
        await moduleIsUp(self);
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
        await moduleIsUp(self);
        NadirFIFOPeek(switch2Controller, msg);
        irID := getIRIDForFlow(msg.flow, msg.type);
        
        ControllerUpdateIRDone:
            controllerWaitForLockFree(); 
            controllerModuleFailOrNot();
            if NIBIRStatus[irID] = IR_SENT then
                NIBIRStatus[irID] := IR_DONE; 
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                );
            end if;
            
            if msg.type = DELETED_SUCCESSFULLY then 
                removedIR := msg.flow;
                ControllerMonUpdateIRNone:
                    controllerWaitForLockFree(); 
                    controllerModuleFailOrNot();
                    NIBIRStatus[removedIR] := IR_NONE; 
                    NadirFIFOPut(
                        RCNIBEventQueue,
                        [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]
                    );
            end if;

        MonitoringServerRemoveFromQueue:
            controllerReleaseLock();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                NadirFIFOPop(switch2Controller);
            else
                goto ControllerMonitorCheckIfMastr;
            end if; 
    end while
    end process

    fair process watchDog \in ({ofc0, rc0} \X {WATCH_DOG})
    variable controllerFailedModules = {};
    begin
    ControllerWatchDogProc:
    while TRUE do
        controllerWaitForLockFree();
        controllerFailedModules := returnControllerFailedModules(self[1]);
        await Cardinality(controllerFailedModules) > 0;
        with module \in controllerFailedModules do
            assert controllerSubmoduleFailStat[module] = Failed;
            controllerLock := module;
            controllerSubmoduleFailStat[module] := NotFailed;   
        end with;
    end while; 
    end process  
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "307d958")
\* Process variable stepOfFailure of process controllerSequencer at line 367 col 109 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 457 col 64 changed to stepOfFailure_c
VARIABLES switchLock, controllerLock, controllerSubmoduleFailNum, 
          controllerSubmoduleFailStat, swSeqChangedStatus, controller2Switch, 
          switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
          IRQueueNIB, RCNIBEventQueue, DAGState, RCIRStatus, 
          RCSwSuspensionStatus, NIBIRStatus, SwSuspensionStatus, 
          rcInternalState, ofcInternalState, SetScheduledIRs, ir2sw, 
          seqWorkerIsBusy, pc

(* define statement *)
moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                             [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0
returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                           /\ controllerSubmoduleFailStat[x] = Failed}

getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}
getSetRemovableIRs(swSet, nxtDAGV) == {x \in DOMAIN RCIRStatus: /\ x \leq MaxNumIRs
                                                                /\ x \notin nxtDAGV
                                                                /\ ir2sw[x] \in swSet
                                                                /\ \/ RCIRStatus[x] # IR_NONE
                                                                   \/ x \in SetScheduledIRs[ir2sw[x]]}
getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: ir2sw[x] = swID}
isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                   /\ RCIRStatus[y] # IR_DONE
getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ RCIRStatus[x] = IR_NONE
                                                   /\ isDependencySatisfied(DAG, x)
                                                   /\ RCSwSuspensionStatus[ir2sw[x]] = SW_RUN
                                                   /\ x \notin SetScheduledIRs[ir2sw[x]]}
getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN ir + MaxNumIRs
                                        ELSE ir - MaxNumIRs
getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW
                                          ELSE DELETE_FLOW
getIRFlow(irID) == IF irID \leq MaxNumIRs THEN irID
                                          ELSE irID - MaxNumIRs
getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                     ELSE flowID + MaxNumIRs
allIRsInDAGInstalled(DAG) == ~\E y \in DOMAIN RCIRStatus: /\ y \leq MaxNumIRs
                                                          /\ y \in DAG.v
                                                          /\ RCIRStatus[y] # IR_DONE
allIRsInDAGAreStable(DAG) == ~\E y \in DOMAIN RCIRStatus: /\ y \leq MaxNumIRs
                                                          /\ y \in DAG.v
                                                          /\ getIRType(y) = INSTALL_FLOW
                                                          /\ RCIRStatus[y] = IR_DONE
                                                          /\ getDualOfIR(y) \in DOMAIN RCIRStatus
                                                          /\ \/ RCIRStatus[getDualOfIR(y)] # IR_NONE
                                                             \/ getDualOfIR(y) \in SetScheduledIRs[ir2sw[getDualOfIR(y)]]
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
getIRSetToReset(SID) == {x \in DOMAIN NIBIRStatus: /\ x \leq MaxNumIRs
                                                   /\ ir2sw[x] = SID
                                                   /\ NIBIRStatus[x] \notin {IR_NONE}}
dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag)
                                            /\ ~isDAGStale(dagObject.id)
                                         \/ ~allIRsInDAGAreStable(dagObject.dag)

VARIABLES event, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, 
          nxtDAG, deleterID, setRemovableIRs, currIR, currIRInDAG, 
          nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, worker, 
          toBeScheduledIRs, nextIR, currDAG, IRSet, IRDoneSet, stepOfFailure_, 
          nextIRIDToSend, index, stepOfFailure_c, monitoringEvent, 
          setIRsToReset, resetIR, stepOfFailure, msg, irID, removedIR, 
          controllerFailedModules

vars == << switchLock, controllerLock, controllerSubmoduleFailNum, 
           controllerSubmoduleFailStat, swSeqChangedStatus, controller2Switch, 
           switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
           IRQueueNIB, RCNIBEventQueue, DAGState, RCIRStatus, 
           RCSwSuspensionStatus, NIBIRStatus, SwSuspensionStatus, 
           rcInternalState, ofcInternalState, SetScheduledIRs, ir2sw, 
           seqWorkerIsBusy, pc, event, topoChangeEvent, currSetDownSw, 
           prev_dag_id, init, DAGID, nxtDAG, deleterID, setRemovableIRs, 
           currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, 
           seqEvent, worker, toBeScheduledIRs, nextIR, currDAG, IRSet, 
           IRDoneSet, stepOfFailure_, nextIRIDToSend, index, stepOfFailure_c, 
           monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, irID, 
           removedIR, controllerFailedModules >>

ProcSet == (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})) \cup (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
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
        /\ ir2sw = IR2SW
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
        /\ worker = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ IRDoneSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        (* Process controllerWorkerThreads *)
        /\ nextIRIDToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ stepOfFailure_c = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ stepOfFailure = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ removedIR = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        (* Process watchDog *)
        /\ controllerFailedModules = [self \in ({ofc0, rc0} \X {WATCH_DOG}) |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({ofc0, rc0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ moduleIsUp(self)
                               /\ Len(RCNIBEventQueue) > 0
                               /\ event' = [event EXCEPT ![self] = Head(RCNIBEventQueue)]
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                                /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[event'[self].IR]] = SetScheduledIRs[ir2sw[event'[self].IR]]\{event'[self].IR}]
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
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, DAGState, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, ir2sw, 
                                               seqWorkerIsBusy, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, currDAG, IRSet, 
                                               IRDoneSet, stepOfFailure_, 
                                               nextIRIDToSend, index, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ moduleIsUp(self)
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ controllerLock' = self
                          /\ IF init[self] = 1
                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                     /\ UNCHANGED topoChangeEvent
                                ELSE /\ Len(TEEventQueue) > 0
                                     /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << switchLock, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, IRQueueNIB, 
                                          RCNIBEventQueue, DAGState, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          rcInternalState, ofcInternalState, 
                                          SetScheduledIRs, ir2sw, 
                                          seqWorkerIsBusy, event, 
                                          currSetDownSw, prev_dag_id, init, 
                                          DAGID, nxtDAG, deleterID, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRSet, IRDoneSet, stepOfFailure_, 
                                          nextIRIDToSend, index, 
                                          stepOfFailure_c, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure, msg, irID, removedIR, 
                                          controllerFailedModules >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF topoChangeEvent[self] # NADIR_NULL
                                           THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ IF topoChangeEvent[self].state = SW_SUSPEND
                                                      THEN /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \cup {topoChangeEvent[self].sw}]
                                                      ELSE /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \ {topoChangeEvent[self].sw}]
                                                /\ TEEventQueue' = Tail(TEEventQueue)
                                                /\ IF Len(TEEventQueue') > 0
                                                      THEN /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue')]
                                                      ELSE /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = NADIR_NULL]
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
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     swSeqChangedStatus, 
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
                                                     SetScheduledIRs, ir2sw, 
                                                     seqWorkerIsBusy, event, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRSet, IRDoneSet, 
                                                     stepOfFailure_, 
                                                     nextIRIDToSend, index, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ IF DAGID[self] = NADIR_NULL
                                                 THEN /\ DAGID' = [DAGID EXCEPT ![self] = 1]
                                                 ELSE /\ DAGID' = [DAGID EXCEPT ![self] = (DAGID[self] % MaxDAGID) + 1]
                                           /\ nxtDAG' = [nxtDAG EXCEPT ![self] = [id |-> DAGID'[self], dag |-> TOPO_DAG_MAPPING[currSetDownSw[self]]]]
                                           /\ IF prev_dag[self] = nxtDAG'[self].dag
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                                      /\ UNCHANGED << DAGState, 
                                                                      prev_dag_id, 
                                                                      init, 
                                                                      nxtDAGVertices >>
                                                 ELSE /\ nxtDAGVertices' = [nxtDAGVertices EXCEPT ![self] = nxtDAG'[self].dag.v]
                                                      /\ IF init[self] = 0
                                                            THEN /\ DAGState' = [DAGState EXCEPT ![prev_dag_id[self]] = DAG_STALE]
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTESendDagStaleNotif"]
                                                                 /\ UNCHANGED << prev_dag_id, 
                                                                                 init >>
                                                            ELSE /\ init' = [init EXCEPT ![self] = 0]
                                                                 /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID'[self]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                                 /\ UNCHANGED DAGState
                                           /\ UNCHANGED << switchLock, 
                                                           controllerLock, 
                                                           controllerSubmoduleFailNum, 
                                                           controllerSubmoduleFailStat, 
                                                           swSeqChangedStatus, 
                                                           controller2Switch, 
                                                           switch2Controller, 
                                                           TEEventQueue, 
                                                           DAGEventQueue, 
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
                                                           ir2sw, 
                                                           seqWorkerIsBusy, 
                                                           event, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           deleterID, 
                                                           setRemovableIRs, 
                                                           currIR, currIRInDAG, 
                                                           setIRsInDAG, 
                                                           prev_dag, seqEvent, 
                                                           worker, 
                                                           toBeScheduledIRs, 
                                                           nextIR, currDAG, 
                                                           IRSet, IRDoneSet, 
                                                           stepOfFailure_, 
                                                           nextIRIDToSend, 
                                                           index, 
                                                           stepOfFailure_c, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, 
                                                           stepOfFailure, msg, 
                                                           irID, removedIR, 
                                                           controllerFailedModules >>

ControllerTESendDagStaleNotif(self) == /\ pc[self] = "ControllerTESendDagStaleNotif"
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_STALE, id |-> prev_dag_id[self]]))
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       TEEventQueue, DAGQueue, 
                                                       IRQueueNIB, 
                                                       RCNIBEventQueue, 
                                                       DAGState, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       SetScheduledIRs, ir2sw, 
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
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, IRSet, 
                                                       IRDoneSet, 
                                                       stepOfFailure_, 
                                                       nextIRIDToSend, index, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, msg, 
                                                       irID, removedIR, 
                                                       controllerFailedModules >>

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ DAGState[prev_dag_id[self]] = DAG_NONE
                                                /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID[self]]
                                                /\ prev_dag' = [prev_dag EXCEPT ![self] = nxtDAG[self].dag]
                                                /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = getSetRemovableIRs(SW \ currSetDownSw[self], nxtDAGVertices[self])]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                /\ UNCHANGED << switchLock, 
                                                                controllerLock, 
                                                                controllerSubmoduleFailNum, 
                                                                controllerSubmoduleFailStat, 
                                                                swSeqChangedStatus, 
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
                                                                ir2sw, 
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
                                                                worker, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                currDAG, IRSet, 
                                                                IRDoneSet, 
                                                                stepOfFailure_, 
                                                                nextIRIDToSend, 
                                                                index, 
                                                                stepOfFailure_c, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, 
                                                                stepOfFailure, 
                                                                msg, irID, 
                                                                removedIR, 
                                                                controllerFailedModules >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF setRemovableIRs[self] # {}
                                                THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = self
                                                     /\ currIR' = [currIR EXCEPT ![self] = CHOOSE x \in setRemovableIRs[self]: TRUE]
                                                     /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = setRemovableIRs[self] \ {currIR'[self]}]
                                                     /\ deleterID' = [deleterID EXCEPT ![self] = getDualOfIR(currIR'[self])]
                                                     /\ IF (deleterID'[self] \notin DOMAIN RCIRStatus)
                                                           THEN /\ RCIRStatus' = RCIRStatus    @@ (deleterID'[self] :> IR_NONE)
                                                                /\ NIBIRStatus' = NIBIRStatus   @@ (deleterID'[self] :> IR_NONE)
                                                                /\ ir2sw' = ir2sw         @@ (deleterID'[self] :> ir2sw[currIR'[self]])
                                                           ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                                /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                                /\ ir2sw' = ir2sw
                                                     /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {deleterID'[self]}]
                                                     /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(ir2sw'[currIR'[self]], nxtDAGVertices[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                                     /\ UNCHANGED SetScheduledIRs
                                                ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                     /\ SetScheduledIRs' = [x \in SW |-> (SetScheduledIRs[x] \ nxtDAG[self].dag.v)]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                                     /\ UNCHANGED << RCIRStatus, 
                                                                     NIBIRStatus, 
                                                                     ir2sw, 
                                                                     nxtDAG, 
                                                                     deleterID, 
                                                                     setRemovableIRs, 
                                                                     currIR, 
                                                                     setIRsInDAG >>
                                          /\ UNCHANGED << switchLock, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          DAGState, 
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
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRSet, IRDoneSet, 
                                                          stepOfFailure_, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

ControllerTEAddEdge(self) == /\ pc[self] = "ControllerTEAddEdge"
                             /\ IF setIRsInDAG[self] # {}
                                   THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ controllerLock' = self
                                        /\ currIRInDAG' = [currIRInDAG EXCEPT ![self] = CHOOSE x \in setIRsInDAG[self]: TRUE]
                                        /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = setIRsInDAG[self] \ {currIRInDAG'[self]}]
                                        /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.e = nxtDAG[self].dag.e \cup {<<deleterID[self], currIRInDAG'[self]>>}]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                   ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ controllerLock' = self
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                        /\ UNCHANGED << nxtDAG, currIRInDAG, 
                                                        setIRsInDAG >>
                             /\ UNCHANGED << switchLock, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, RCNIBEventQueue, 
                                             DAGState, RCIRStatus, 
                                             RCSwSuspensionStatus, NIBIRStatus, 
                                             SwSuspensionStatus, 
                                             rcInternalState, ofcInternalState, 
                                             SetScheduledIRs, ir2sw, 
                                             seqWorkerIsBusy, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, 
                                             deleterID, setRemovableIRs, 
                                             currIR, nxtDAGVertices, prev_dag, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, currDAG, 
                                             IRSet, IRDoneSet, stepOfFailure_, 
                                             nextIRIDToSend, index, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_NEW, dag_obj |-> nxtDAG[self]]))
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  TEEventQueue, DAGQueue, 
                                                  IRQueueNIB, RCNIBEventQueue, 
                                                  RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  rcInternalState, 
                                                  ofcInternalState, 
                                                  SetScheduledIRs, ir2sw, 
                                                  seqWorkerIsBusy, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  deleterID, setRemovableIRs, 
                                                  currIR, currIRInDAG, 
                                                  nxtDAGVertices, setIRsInDAG, 
                                                  prev_dag, seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  currDAG, IRSet, IRDoneSet, 
                                                  stepOfFailure_, 
                                                  nextIRIDToSend, index, 
                                                  stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR, 
                                                  controllerFailedModules >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTESendDagStaleNotif(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTEAddEdge(self)
                                         \/ ControllerTESubmitNewDAG(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ moduleIsUp(self)
                               /\ Len(DAGEventQueue) > 0
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue)]
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               IRQueueNIB, RCNIBEventQueue, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, ir2sw, 
                                               seqWorkerIsBusy, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, worker, 
                                               toBeScheduledIRs, nextIR, 
                                               currDAG, IRSet, IRDoneSet, 
                                               stepOfFailure_, nextIRIDToSend, 
                                               index, stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ seqWorkerIsBusy = FALSE
                                     /\ DAGState' = [DAGState EXCEPT ![seqEvent[self].id] = DAG_NONE]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     swSeqChangedStatus, 
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
                                                     SetScheduledIRs, ir2sw, 
                                                     seqWorkerIsBusy, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRSet, IRDoneSet, 
                                                     stepOfFailure_, 
                                                     nextIRIDToSend, index, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ moduleIsUp(self)
                                 /\ Len(DAGQueue) > 0
                                 /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue)]
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ seqWorkerIsBusy' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 swSeqChangedStatus, 
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
                                                 SetScheduledIRs, ir2sw, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 deleterID, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 IRSet, IRDoneSet, 
                                                 stepOfFailure_, 
                                                 nextIRIDToSend, index, 
                                                 stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF dagObjectShouldBeProcessed(currDAG[self])
                                              THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(currDAG[self].dag)]
                                                   /\ toBeScheduledIRs'[self] # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                   /\ UNCHANGED << controllerLock, 
                                                                   seqWorkerIsBusy, 
                                                                   IRSet >>
                                              ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = self
                                                   /\ seqWorkerIsBusy' = FALSE
                                                   /\ IRSet' = [IRSet EXCEPT ![self] = currDAG[self].dag.v]
                                                   /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                                   /\ UNCHANGED toBeScheduledIRs
                                        /\ UNCHANGED << switchLock, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        swSeqChangedStatus, 
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
                                                        SetScheduledIRs, ir2sw, 
                                                        event, topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        DAGID, nxtDAG, 
                                                        deleterID, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, worker, 
                                                        nextIR, currDAG, 
                                                        IRDoneSet, 
                                                        stepOfFailure_, 
                                                        nextIRIDToSend, index, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        irID, removedIR, 
                                                        controllerFailedModules >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                  THEN /\ \E num \in 0..3:
                                            stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                                  ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                            /\ IF (stepOfFailure_'[self] # 1)
                                  THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                                       /\ IF (stepOfFailure_'[self] # 2)
                                             THEN /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> STATUS_START_SCHEDULING, next |-> nextIR'[self]]]
                                                  /\ IF (stepOfFailure_'[self] # 3)
                                                        THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[nextIR'[self]]] = SetScheduledIRs[ir2sw[nextIR'[self]]] \cup {nextIR'[self]}]
                                                        ELSE /\ TRUE
                                                             /\ UNCHANGED SetScheduledIRs
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << rcInternalState, 
                                                                  SetScheduledIRs >>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << rcInternalState, 
                                                       SetScheduledIRs, nextIR >>
                            /\ IF (stepOfFailure_'[self] # 0)
                                  THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                       /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "AddDeleteIRIRDoneSet"]
                                       /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat >>
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, 
                                            IRQueueNIB, RCNIBEventQueue, 
                                            DAGState, RCIRStatus, 
                                            RCSwSuspensionStatus, NIBIRStatus, 
                                            SwSuspensionStatus, 
                                            ofcInternalState, ir2sw, 
                                            seqWorkerIsBusy, event, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, DAGID, nxtDAG, 
                                            deleterID, setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, currDAG, 
                                            IRSet, IRDoneSet, nextIRIDToSend, 
                                            index, stepOfFailure_c, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, msg, irID, 
                                            removedIR, controllerFailedModules >>

AddDeleteIRIRDoneSet(self) == /\ pc[self] = "AddDeleteIRIRDoneSet"
                              /\ IF getIRType(nextIR[self]) = INSTALL_FLOW
                                    THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \cup {nextIR[self]}]
                                    ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \ {getDualOfIR(nextIR[self])}]
                              /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, 
                                              IRQueueNIB, RCNIBEventQueue, 
                                              DAGState, RCIRStatus, 
                                              RCSwSuspensionStatus, 
                                              NIBIRStatus, SwSuspensionStatus, 
                                              rcInternalState, 
                                              ofcInternalState, 
                                              SetScheduledIRs, ir2sw, 
                                              seqWorkerIsBusy, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, DAGID, nxtDAG, 
                                              deleterID, setRemovableIRs, 
                                              currIR, currIRInDAG, 
                                              nxtDAGVertices, setIRsInDAG, 
                                              prev_dag, seqEvent, worker, 
                                              toBeScheduledIRs, nextIR, 
                                              currDAG, IRSet, stepOfFailure_, 
                                              nextIRIDToSend, index, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR, 
                                              controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                             THEN /\ \E num \in 0..2:
                                       stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                             ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                       /\ IF (stepOfFailure_'[self] # 1)
                             THEN /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> nextIR[self], tag |-> NADIR_NULL])
                                  /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self] \ {nextIR[self]}]
                                  /\ IF (stepOfFailure_'[self] # 2)
                                        THEN /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> NO_STATUS]]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED rcInternalState
                             ELSE /\ TRUE
                                  /\ UNCHANGED << IRQueueNIB, rcInternalState, 
                                                  toBeScheduledIRs >>
                       /\ IF (stepOfFailure_'[self] # 0)
                             THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                  /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                             ELSE /\ IF toBeScheduledIRs'[self] = {} \/ isDAGStale(currDAG[self].id)
                                        THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                  /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat >>
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, TEEventQueue, 
                                       DAGEventQueue, DAGQueue, 
                                       RCNIBEventQueue, DAGState, RCIRStatus, 
                                       RCSwSuspensionStatus, NIBIRStatus, 
                                       SwSuspensionStatus, ofcInternalState, 
                                       SetScheduledIRs, ir2sw, seqWorkerIsBusy, 
                                       event, topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, DAGID, nxtDAG, 
                                       deleterID, setRemovableIRs, currIR, 
                                       currIRInDAG, nxtDAGVertices, 
                                       setIRsInDAG, prev_dag, seqEvent, worker, 
                                       nextIR, currDAG, IRSet, IRDoneSet, 
                                       nextIRIDToSend, index, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, irID, removedIR, 
                                       controllerFailedModules >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {} /\ allIRsInDAGInstalled(currDAG[self].dag)
                                     THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF getIRType(nextIR'[self]) = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \cup {nextIR'[self]}]
                                                ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \ {getDualOfIR(nextIR'[self])}]
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                          /\ UNCHANGED DAGQueue
                                     ELSE /\ DAGQueue' = Tail(DAGQueue)
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << nextIR, IRSet, 
                                                          IRDoneSet >>
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               DAGEventQueue, IRQueueNIB, 
                                               RCNIBEventQueue, DAGState, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, ir2sw, 
                                               seqWorkerIsBusy, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               currDAG, stepOfFailure_, 
                                               nextIRIDToSend, index, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ moduleIsUp(self)
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (rcInternalState[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[rcInternalState[self].next]] = SetScheduledIRs[ir2sw[rcInternalState[self].next]] \ {rcInternalState[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          swSeqChangedStatus, 
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
                                                          ir2sw, 
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
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRSet, IRDoneSet, 
                                                          stepOfFailure_, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteIRIRDoneSet(self)
                                \/ ScheduleTheIR(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ ControllerSeqStateReconciliation(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ moduleIsUp(self)
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ ExistsItemWithTag(IRQueueNIB, NADIR_NULL) \/ ExistsItemWithTag(IRQueueNIB, self)
                          /\ index' = [index EXCEPT ![self] = GetItemIndexWithTag(IRQueueNIB, self)]
                          /\ nextIRIDToSend' = [nextIRIDToSend EXCEPT ![self] = IRQueueNIB[index'[self]].data]
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![index'[self]].tag = self]
                          /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                THEN /\ \E num \in 0..1:
                                          stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                          /\ IF (stepOfFailure_c'[self] = 1)
                                THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                     /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                     /\ UNCHANGED ofcInternalState
                                ELSE /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRIDToSend'[self]]]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                     /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat >>
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, RCNIBEventQueue, DAGState, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          rcInternalState, SetScheduledIRs, 
                                          ir2sw, seqWorkerIsBusy, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, DAGID, nxtDAG, 
                                          deleterID, setRemovableIRs, currIR, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          worker, toBeScheduledIRs, nextIR, 
                                          currDAG, IRSet, IRDoneSet, 
                                          stepOfFailure_, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure, msg, irID, removedIR, 
                                          controllerFailedModules >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                               controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                      THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                 /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              \/ /\ TRUE
                                                 /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                           controllerSubmoduleFailStat >>
                                /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                      THEN /\ IF ~isSwitchSuspended(ir2sw[nextIRIDToSend[self]]) /\ NIBIRStatus[nextIRIDToSend[self]] = IR_NONE
                                                 THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![nextIRIDToSend[self]] = IR_SENT]
                                                      /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> nextIRIDToSend[self], state |-> IR_SENT]))
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                                      /\ UNCHANGED << RCNIBEventQueue, 
                                                                      NIBIRStatus >>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, DAGState, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, ir2sw, 
                                                seqWorkerIsBusy, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRSet, IRDoneSet, 
                                                stepOfFailure_, nextIRIDToSend, 
                                                index, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR, 
                                                controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..2:
                                                   stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure_c'[self] # 1)
                                         THEN /\ LET destination == ir2sw[nextIRIDToSend[self]] IN
                                                   controller2Switch' = [controller2Switch EXCEPT ![destination] = Append(controller2Switch[destination], ([type |-> getIRType(nextIRIDToSend[self]), flow |-> getIRFlow(nextIRIDToSend[self]), to |-> destination, from |-> self[1]]))]
                                              /\ IF (stepOfFailure_c'[self] # 2)
                                                    THEN /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_SENT_DONE, next |-> nextIRIDToSend[self]]]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED ofcInternalState
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controller2Switch, 
                                                              ofcInternalState >>
                                   /\ IF (stepOfFailure_c'[self] # 0)
                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   RCNIBEventQueue, DAGState, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   rcInternalState, 
                                                   SetScheduledIRs, ir2sw, 
                                                   seqWorkerIsBusy, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, IRDoneSet, 
                                                   stepOfFailure_, 
                                                   nextIRIDToSend, index, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                        THEN /\ \E num \in 0..2:
                                                  stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                        ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                  /\ IF (stepOfFailure_c'[self] # 1)
                                        THEN /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NO_STATUS]]
                                             /\ IF (stepOfFailure_c'[self] # 2)
                                                   THEN /\ index' = [index EXCEPT ![self] = GetFirstItemIndexWithTag(IRQueueNIB, self)]
                                                        /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index'[self])
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << IRQueueNIB, 
                                                                        index >>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << IRQueueNIB, 
                                                             ofcInternalState, 
                                                             index >>
                                  /\ IF (stepOfFailure_c'[self] # 0)
                                        THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                             /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat >>
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, RCNIBEventQueue, 
                                                  DAGState, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  rcInternalState, 
                                                  SetScheduledIRs, ir2sw, 
                                                  seqWorkerIsBusy, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  deleterID, setRemovableIRs, 
                                                  currIR, currIRInDAG, 
                                                  nxtDAGVertices, setIRsInDAG, 
                                                  prev_dag, seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  currDAG, IRSet, IRDoneSet, 
                                                  stepOfFailure_, 
                                                  nextIRIDToSend, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR, 
                                                  controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ moduleIsUp(self)
                                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (ofcInternalState[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (NIBIRStatus[ofcInternalState[self].next] = IR_SENT)
                                                              THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![ofcInternalState[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED NIBIRStatus
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED NIBIRStatus
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << switchLock, 
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             swSeqChangedStatus, 
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
                                                             ir2sw, 
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
                                                             seqEvent, worker, 
                                                             toBeScheduledIRs, 
                                                             nextIR, currDAG, 
                                                             IRSet, IRDoneSet, 
                                                             stepOfFailure_, 
                                                             nextIRIDToSend, 
                                                             index, 
                                                             stepOfFailure_c, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, 
                                                             stepOfFailure, 
                                                             msg, irID, 
                                                             removedIR, 
                                                             controllerFailedModules >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ moduleIsUp(self)
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerLock' = self
                                    /\ Len(swSeqChangedStatus) > 0
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << switchLock, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    swSeqChangedStatus, 
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
                                                    SetScheduledIRs, ir2sw, 
                                                    seqWorkerIsBusy, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    deleterID, setRemovableIRs, 
                                                    currIR, currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    currDAG, IRSet, IRDoneSet, 
                                                    stepOfFailure_, 
                                                    nextIRIDToSend, index, 
                                                    stepOfFailure_c, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    removedIR, 
                                                    controllerFailedModules >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                                         THEN /\ \E num \in 0..2:
                                                                   stepOfFailure' = [stepOfFailure EXCEPT ![self] = num]
                                                         ELSE /\ stepOfFailure' = [stepOfFailure EXCEPT ![self] = 0]
                                                   /\ IF (stepOfFailure'[self] # 1)
                                                         THEN /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NO_STATUS]]
                                                              /\ IF (stepOfFailure'[self] # 2)
                                                                    THEN /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED swSeqChangedStatus
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << swSeqChangedStatus, 
                                                                              ofcInternalState >>
                                                   /\ IF (stepOfFailure'[self] # 0)
                                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                              controllerSubmoduleFailStat >>
                                                   /\ UNCHANGED << switchLock, 
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
                                                                   SetScheduledIRs, 
                                                                   ir2sw, 
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
                                                                   worker, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   IRDoneSet, 
                                                                   stepOfFailure_, 
                                                                   nextIRIDToSend, 
                                                                   index, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   removedIR, 
                                                                   controllerFailedModules >>

ControllerEventHandlerSuspendSW(self) == /\ pc[self] = "ControllerEventHandlerSuspendSW"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                                        controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                               THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                          /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                       \/ /\ TRUE
                                                          /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                    controllerSubmoduleFailStat >>
                                         /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                               THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                                                    /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND]))
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                    /\ UNCHANGED << RCNIBEventQueue, 
                                                                    SwSuspensionStatus >>
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         DAGState, RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         NIBIRStatus, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         SetScheduledIRs, 
                                                         ir2sw, 
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
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, currDAG, 
                                                         IRSet, IRDoneSet, 
                                                         stepOfFailure_, 
                                                         nextIRIDToSend, index, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
                                                         controllerFailedModules >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                                         controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                                THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                           /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                        \/ /\ TRUE
                                                           /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                     controllerSubmoduleFailStat >>
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
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
                                                          DAGState, RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          SetScheduledIRs, 
                                                          ir2sw, 
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
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRSet, IRDoneSet, 
                                                          stepOfFailure_, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                          controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                 THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                            /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                         \/ /\ TRUE
                                            /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat >>
                           /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                 THEN /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = getIRSetToReset(monitoringEvent[self].swID)]
                                      /\ IF (setIRsToReset'[self] = {})
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                      /\ UNCHANGED setIRsToReset
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, IRQueueNIB, 
                                           RCNIBEventQueue, DAGState, 
                                           RCIRStatus, RCSwSuspensionStatus, 
                                           NIBIRStatus, SwSuspensionStatus, 
                                           rcInternalState, ofcInternalState, 
                                           SetScheduledIRs, ir2sw, 
                                           seqWorkerIsBusy, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, DAGID, nxtDAG, 
                                           deleterID, setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           currDAG, IRSet, IRDoneSet, 
                                           stepOfFailure_, nextIRIDToSend, 
                                           index, stepOfFailure_c, 
                                           monitoringEvent, resetIR, 
                                           stepOfFailure, msg, irID, removedIR, 
                                           controllerFailedModules >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                    controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                           THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                      /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                   \/ /\ TRUE
                                      /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                           ELSE /\ TRUE
                                /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat >>
                     /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                           THEN /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                                /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                                /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]] = IR_NONE]
                                /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> resetIR'[self], state |-> IR_NONE]))
                                /\ IF setIRsToReset'[self] = {}
                                      THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                /\ UNCHANGED << RCNIBEventQueue, NIBIRStatus, 
                                                setIRsToReset, resetIR >>
                     /\ UNCHANGED << switchLock, controllerLock, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, IRQueueNIB, 
                                     DAGState, RCIRStatus, 
                                     RCSwSuspensionStatus, SwSuspensionStatus, 
                                     rcInternalState, ofcInternalState, 
                                     SetScheduledIRs, ir2sw, seqWorkerIsBusy, 
                                     event, topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     deleterID, setRemovableIRs, currIR, 
                                     currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                     prev_dag, seqEvent, worker, 
                                     toBeScheduledIRs, nextIR, currDAG, IRSet, 
                                     IRDoneSet, stepOfFailure_, nextIRIDToSend, 
                                     index, stepOfFailure_c, monitoringEvent, 
                                     stepOfFailure, msg, irID, removedIR, 
                                     controllerFailedModules >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerLock' = self
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..2:
                                                   stepOfFailure' = [stepOfFailure EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure' = [stepOfFailure EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure'[self] # 1)
                                         THEN /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                              /\ IF (stepOfFailure'[self] # 2)
                                                    THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                                         /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_RUN]))
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED << RCNIBEventQueue, 
                                                                         SwSuspensionStatus >>
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                              SwSuspensionStatus, 
                                                              ofcInternalState >>
                                   /\ IF (stepOfFailure'[self] # 0)
                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ UNCHANGED << switchLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   NIBIRStatus, 
                                                   rcInternalState, 
                                                   SetScheduledIRs, ir2sw, 
                                                   seqWorkerIsBusy, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, IRDoneSet, 
                                                   stepOfFailure_, 
                                                   nextIRIDToSend, index, 
                                                   stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR, 
                                                   controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ moduleIsUp(self)
                                                   /\ IF (ofcInternalState[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![ofcInternalState[self].sw] = SW_SUSPEND]
                                                              /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND]))
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                                              SwSuspensionStatus >>
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   controllerLock, 
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   swSeqChangedStatus, 
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
                                                                   ir2sw, 
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
                                                                   worker, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   IRDoneSet, 
                                                                   stepOfFailure_, 
                                                                   nextIRIDToSend, 
                                                                   index, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
                                                                   msg, irID, 
                                                                   removedIR, 
                                                                   controllerFailedModules >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerEventHandlerSuspendSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ moduleIsUp(self)
                                       /\ Len(switch2Controller) > 0
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg'[self].flow, msg'[self].type)]
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone"]
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       swSeqChangedStatus, 
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
                                                       SetScheduledIRs, ir2sw, 
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
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, IRSet, 
                                                       IRDoneSet, 
                                                       stepOfFailure_, 
                                                       nextIRIDToSend, index, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, 
                                                       removedIR, 
                                                       controllerFailedModules >>

ControllerUpdateIRDone(self) == /\ pc[self] = "ControllerUpdateIRDone"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                               controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                      THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                 /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              \/ /\ TRUE
                                                 /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                           controllerSubmoduleFailStat >>
                                /\ IF NIBIRStatus[irID[self]] = IR_SENT
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID[self]] = IR_DONE]
                                           /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> irID[self], state |-> IR_DONE]))
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                /\ IF msg[self].type = DELETED_SUCCESSFULLY
                                      THEN /\ removedIR' = [removedIR EXCEPT ![self] = msg[self].flow]
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerMonUpdateIRNone"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                           /\ UNCHANGED removedIR
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, DAGState, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, ir2sw, 
                                                seqWorkerIsBusy, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRSet, IRDoneSet, 
                                                stepOfFailure_, nextIRIDToSend, 
                                                index, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, controllerFailedModules >>

ControllerMonUpdateIRNone(self) == /\ pc[self] = "ControllerMonUpdateIRNone"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                                  controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                    /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                 \/ /\ TRUE
                                                    /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![removedIR[self]] = IR_NONE]
                                   /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> removedIR[self], state |-> IR_NONE]))
                                   /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   SwSuspensionStatus, 
                                                   rcInternalState, 
                                                   ofcInternalState, 
                                                   SetScheduledIRs, ir2sw, 
                                                   seqWorkerIsBusy, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, IRDoneSet, 
                                                   stepOfFailure_, 
                                                   nextIRIDToSend, index, 
                                                   stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                         /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                                        controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                               THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                          /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                       \/ /\ TRUE
                                                          /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                    controllerSubmoduleFailStat >>
                                         /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                               THEN /\ switch2Controller' = Tail(switch2Controller)
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                    /\ UNCHANGED switch2Controller
                                         /\ UNCHANGED << switchLock, 
                                                         swSeqChangedStatus, 
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
                                                         ir2sw, 
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
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, currDAG, 
                                                         IRSet, IRDoneSet, 
                                                         stepOfFailure_, 
                                                         nextIRIDToSend, index, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
                                                         controllerFailedModules >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ ControllerUpdateIRDone(self)
                                       \/ ControllerMonUpdateIRNone(self)
                                       \/ MonitoringServerRemoveFromQueue(self)

ControllerWatchDogProc(self) == /\ pc[self] = "ControllerWatchDogProc"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerFailedModules' = [controllerFailedModules EXCEPT ![self] = returnControllerFailedModules(self[1])]
                                /\ Cardinality(controllerFailedModules'[self]) > 0
                                /\ \E module \in controllerFailedModules'[self]:
                                     /\ Assert(controllerSubmoduleFailStat[module] = Failed, 
                                               "Failure of assertion at line 690, column 13.")
                                     /\ controllerLock' = module
                                     /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![module] = NotFailed]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerWatchDogProc"]
                                /\ UNCHANGED << switchLock, 
                                                controllerSubmoduleFailNum, 
                                                swSeqChangedStatus, 
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
                                                SetScheduledIRs, ir2sw, 
                                                seqWorkerIsBusy, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRSet, IRDoneSet, 
                                                stepOfFailure_, nextIRIDToSend, 
                                                index, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR >>

watchDog(self) == ControllerWatchDogProc(self)

Next == (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))
           \/ (\E self \in ({ofc0, rc0} \X {WATCH_DOG}): watchDog(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in ({ofc0, rc0} \X {WATCH_DOG}) : WF_vars(watchDog(self))

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
                ("EnumRCShcedulerInternalState" :> ENUM_SET_RC_SCHEDULER_INTERNAL_STATE) @@
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

MSG_SET_TE_EVENT == [
    type: {TOPO_MOD}, 
    sw: SW, state: 
    ENUM_SET_SW_STATE] \cup [
    type: {IR_MOD}, 
    state: ENUM_SET_IR_STATE, 
    IR: NADIR_INT_ID_SET]

MSG_SET_DAG_EVENT == [
    type: {DAG_STALE}, 
    id: NADIR_INT_ID_SET] \cup [
    type: {DAG_NEW}, 
    dag_obj: STRUCT_SET_DAG_OBJECT]
        
NadirMessageSet == ("MessageSwitchTimeout" :> MSG_SET_TIMEOUT) @@
                   ("MessageSwitchKeepalive" :> MSG_SET_KEEPALIVE) @@
                   ("MessageOpenFlowCMD" :> MSG_SET_OF_CMD) @@
                   ("MessageOpenFlowACK" :> MSG_SET_OF_ACK) @@
                   ("MessageTEEvent" :> MSG_SET_TE_EVENT) @@
                   ("MessageDAGEvent" :> MSG_SET_DAG_EVENT)

TypeOK ==  /\ NadirFIFO(MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE, swSeqChangedStatus)
           /\ NadirFIFO(MSG_SET_OF_ACK, switch2Controller)
           /\ NadirFIFO(MSG_SET_TE_EVENT, TEEventQueue)
           /\ NadirFIFO(MSG_SET_DAG_EVENT, DAGEventQueue)
           /\ NadirFIFO(STRUCT_SET_DAG_OBJECT, DAGQueue)
           /\ NadirFIFO(MSG_SET_TE_EVENT, RCNIBEventQueue)
           /\ NadirAckQueue(STRUCT_SET_NIB_TAGGED_IR, IRQueueNIB)
           /\ NadirFanoutFIFO(SW, MSG_SET_OF_CMD, controller2Switch)
           /\ NadirFunctionTypeCheck(Nat, ENUM_SET_DAG_STATE, DAGState)
           /\ NadirFunctionTypeCheck(Nat, SW, ir2sw)
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
           /\ NadirLocalVariableTypeCheck(NadirNullable({CONT_WORKER_SEQ}), worker)
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

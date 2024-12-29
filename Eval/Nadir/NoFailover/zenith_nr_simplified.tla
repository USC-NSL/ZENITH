------------------- MODULE zenith_nr_simplified -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag, NadirTypes

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR, CONT_EVENT, 
          WATCH_DOG, NIB_EVENT_HANDLER, CONT_TE
CONSTANTS TOPO_DAG_MAPPING, IR2SW

ASSUME MaxNumIRs >= Cardinality({TOPO_DAG_MAPPING[i]: i \in DOMAIN TOPO_DAG_MAPPING})
ASSUME {"ofc0", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE
ASSUME \A x \in DOMAIN TOPO_DAG_MAPPING: /\ "v" \in DOMAIN TOPO_DAG_MAPPING[x]
                                         /\ "e" \in DOMAIN TOPO_DAG_MAPPING[x]
ASSUME \A x \in 1..MaxNumIRs: x \in DOMAIN IR2SW

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

        FirstInstall = [x \in 1..MaxNumIRs |-> 0],

        RCProcSet = ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, NIB_EVENT_HANDLER, CONT_TE, CONT_MONITOR}),
        OFCProcSet = (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup 
                     (({ofc0} \X {CONT_EVENT})) \cup 
                     (({ofc0} \X {CONT_MONITOR})),
        ContProcSet = RCProcSet \cup OFCProcSet,

        DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
        RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE],
        RCSwSuspensionStatus = [y \in SW |-> SW_RUN],
        NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE],
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        rcInternalState = [x \in RCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]],
        ofcInternalState = [x \in OFCProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]],
        SetScheduledIRs = [y \in SW |-> {}],
        
        ir2sw = IR2SW,
        seqWorkerIsBusy = FALSE,
        IRDoneSet = {},
        idThreadWorkingOnIR = [x \in 1..2*MaxNumIRs |-> NADIR_NULL]
    define
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
        getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}                 
        ExistsEntryWithTag(tag) == \E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].tag = tag
        FirstUntaggedEntry(num) == ~\E x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = NADIR_NULL
                                                                /\ x < num
        getFirstIRIndexToRead(threadID) == CHOOSE x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                                           \/ /\ ~ExistsEntryWithTag(threadID)
                                                                              /\ FirstUntaggedEntry(x)
        getFirstIndexWith(RID, threadID) == CHOOSE x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = threadID
                                                                            /\ IRQueueNIB[x].IR = RID
        
        getSetRemovableIRs(swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ RCIRStatus[x] # IR_NONE
                                                                      \/ x \in SetScheduledIRs[ir2sw[x]]
                                                                   /\ x \notin nxtDAGV
                                                                   /\ ir2sw[x] \in swSet}
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
        allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: RCIRStatus[y] # IR_DONE
        allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getIRType(y) = INSTALL_FLOW
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
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                                     /\ NIBIRStatus[x] \notin {IR_NONE}}
        isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE
        dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag) 
                                                    /\ ~isDAGStale(dagObject.id) 
                                                 \/ ~allIRsInDAGAreStable(dagObject.dag)
    end define
    
    macro removeFromSeqSet(SeqSet, obj)
    begin
        assert obj \in Head(SeqSet);
        if Cardinality(Head(SeqSet)) = 1 then
            SeqSet := Tail(SeqSet)
        else
            SeqSet := <<(Head(SeqSet)\{obj})>> \o Tail(SeqSet);
        end if; 
    end macro

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

    macro controllerSendIR(irID)
    begin
        assert irID \in 1..2*MaxNumIRs;
        with destination = ir2sw[irID] do
            controller2Switch[destination] := Append(
                controller2Switch[destination], 
                [
                    type |-> getIRType(irID),
                    flow |-> getIRFlow(irID),
                    to |-> destination,
                    from |-> self[1]
                ]
            );
            if whichSwitchModel(destination) = SW_COMPLEX_MODEL then 
                switchLock := <<NIC_ASIC_IN, destination>>;
            else
                switchLock := <<SW_SIMPLE_ID, destination>>;
            end if;
        end with; 
    end macro;

    macro modifiedEnqueue(nextIR)
    begin
        IRQueueNIB := Append(IRQueueNIB, [IR |-> nextIR, tag |-> NADIR_NULL]);
    end macro;
    
    macro modifiedRead()
    begin
        await ExistsEntryWithTag(NADIR_NULL) \/ ExistsEntryWithTag(self);
        rowIndex := getFirstIRIndexToRead(self);
        nextIRIDToSend := IRQueueNIB[rowIndex].IR;
        IRQueueNIB[rowIndex].tag := self;
    end macro;
    
    macro modifiedRemove()
    begin
        rowRemove := getFirstIndexWith(nextIRIDToSend, self);
        IRQueueNIB := removeFromSeq(IRQueueNIB, rowRemove);
    end macro;

    macro prepareDeletionIR(forWhat, DID)
    begin
        if (DID \notin DOMAIN RCIRStatus) then
            RCIRStatus    := RCIRStatus    @@ (DID :> IR_NONE);
            NIBIRStatus   := NIBIRStatus   @@ (DID :> IR_NONE);
            FirstInstall  := FirstInstall  @@ (DID :> 0);
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
        await Len(RCNIBEventQueue) > 0;
        controllerWaitForLockFree();
        event := Head(RCNIBEventQueue);
        assert event.type \in {TOPO_MOD, IR_MOD};
        if (event.type = TOPO_MOD) then
            if RCSwSuspensionStatus[event.sw] # event.state then    
                RCSwSuspensionStatus[event.sw] := event.state;
                TEEventQueue := Append(TEEventQueue, event);
            end if;
        elsif (event.type = IR_MOD) then
            if RCIRStatus[event.IR] # event.state then
                RCIRStatus[event.IR] := event.state;
                SetScheduledIRs[ir2sw[event.IR]] := SetScheduledIRs[ir2sw[event.IR]]\{event.IR};
            end if;
        end if;
        RCNIBEventQueue := Tail(RCNIBEventQueue);
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
        await init = 1 \/ Len(TEEventQueue) > 0;
        controllerAcquireLock();
        
        ControllerTEEventProcessing:
            while Len(TEEventQueue) > 0 do 
                controllerWaitForLockFree();
                topoChangeEvent := Head(TEEventQueue);
                assert topoChangeEvent.type \in {TOPO_MOD};
                if topoChangeEvent.state = SW_SUSPEND then
                    currSetDownSw := currSetDownSw \cup {topoChangeEvent.sw};
                else
                    currSetDownSw := currSetDownSw \ {topoChangeEvent.sw};
                end if; 
                TEEventQueue := Tail(TEEventQueue);
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
                        DAGEventQueue := Append(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id]);
                
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
            DAGEventQueue := Append(
                DAGEventQueue, 
                [type |-> DAG_NEW, dag_obj |-> nxtDAG]
            );
    
    end while;
    end process

    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    variables seqEvent = NADIR_NULL, worker = NADIR_NULL;
    begin
    ControllerBossSeqProc:
    while TRUE do
        await Len(DAGEventQueue) > 0;
    
        controllerWaitForLockFree();
        seqEvent := Head(DAGEventQueue);
        DAGEventQueue := Tail(DAGEventQueue);
        assert seqEvent.type \in {DAG_NEW, DAG_STALE};
        if seqEvent.type = DAG_NEW then
            DAGQueue := Append(DAGQueue, seqEvent.dag_obj);
        else
            if seqWorkerIsBusy # FALSE then
                WaitForRCSeqWorkerTerminate:
                    controllerWaitForLockFree();
                    await seqWorkerIsBusy = FALSE;
                    DAGState[seqEvent.id] := DAG_NONE;
            else
                DAGState[seqEvent.id] := DAG_NONE;
            end if;
        end if;
    end while;
    end process

    fair process controllerSequencer \in ({rc0} \X {CONT_WORKER_SEQ})
    variables toBeScheduledIRs = {}, nextIR = NADIR_NULL, currDAG = NADIR_NULL, IRSet = {};
    begin
    ControllerWorkerSeqProc:
    while TRUE do
        await Len(DAGQueue) > 0;
        controllerWaitForLockFree();
        currDAG := Head(DAGQueue);
        seqWorkerIsBusy := TRUE;
        
        ControllerWorkerSeqScheduleDAG:
        while dagObjectShouldBeProcessed(currDAG) do
            controllerWaitForLockFree();
            toBeScheduledIRs := getSetIRsCanBeScheduledNext(currDAG.dag);
            await toBeScheduledIRs # {};

            SchedulerMechanism:
            while TRUE do
                controllerWaitForLockFree();
                nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                
                FailBeforeStartSched:
                    controllerWaitForLockFree();
                    rcInternalState[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
                
                FailBeforeAddingToSched:
                    controllerWaitForLockFree();
                    SetScheduledIRs[ir2sw[nextIR]] := SetScheduledIRs[ir2sw[nextIR]] \cup {nextIR};
                
                AddDeleteIRIRDoneSet:      
                    controllerWaitForLockFree();
                    if getIRType(nextIR) = INSTALL_FLOW then
                        IRDoneSet := IRDoneSet \cup {nextIR};
                    else
                        IRDoneSet := IRDoneSet \ {getDualOfIR(nextIR)}
                    end if;

                ScheduleTheIR: 
                    controllerWaitForLockFree();
                    modifiedEnqueue(nextIR);
                
                FailBeforeRemovingFromSched:
                    controllerWaitForLockFree();
                    toBeScheduledIRs := toBeScheduledIRs \ {nextIR};
                
                FailBeforeClearingInternal:
                    controllerWaitForLockFree();
                    rcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL];
                    if toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then
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
            controllerReleaseLock();
            DAGQueue := Tail(DAGQueue);
    end while;
    
    ControllerSeqStateReconciliation:
        controllerReleaseLock();
        if(rcInternalState[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[ir2sw[rcInternalState[self].next]] := 
                        SetScheduledIRs[ir2sw[rcInternalState[self].next]] \ {rcInternalState[self].next};
        end if;
        goto ControllerWorkerSeqProc;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRIDToSend = NADIR_NULL, rowIndex = NADIR_NULL, rowRemove = NADIR_NULL; 
    begin
    ControllerThread:
    while TRUE do
        controllerWaitForLockFree();

        modifiedRead();
        
        FailBeforeLocking:
            controllerWaitForLockFree();
            ofcInternalState[self] := [type |-> STATUS_LOCKING, next |-> nextIRIDToSend];
        
        ControllerThreadLockIR:
            controllerWaitForLockFree();
            if idThreadWorkingOnIR[nextIRIDToSend] = NADIR_NULL then
                idThreadWorkingOnIR[nextIRIDToSend] := self[2]
            else
                ControllerThreadWaitForIRUnlock: 
                    controllerWaitForLockFree();
                    await idThreadWorkingOnIR[nextIRIDToSend] = NADIR_NULL;
                    goto ControllerThread;    
            end if;
        
        ControllerThreadSendIR:
            controllerWaitForLockFree();
            if ~isSwitchSuspended(ir2sw[nextIRIDToSend]) /\ NIBIRStatus[nextIRIDToSend] = IR_NONE then
                NIBIRStatus[nextIRIDToSend] := IR_SENT;
                RCNIBEventQueue := Append(
                    RCNIBEventQueue, 
                    [type |-> IR_MOD, IR |-> nextIRIDToSend, state |-> IR_SENT]
                );
                
                ControllerThreadForwardIR:
                    controllerWaitForLockFree();
                    controllerSendIR(nextIRIDToSend);
                
                FailBeforeStatusSentDone:
                    controllerWaitForLockFree();
                    ofcInternalState[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRIDToSend];
            end if;
                    
        ControllerThreadUnlockSemaphore:
            controllerWaitForLockFree();
            if idThreadWorkingOnIR[nextIRIDToSend] = self[2] then
                idThreadWorkingOnIR[nextIRIDToSend] := NADIR_NULL;
            end if;

        RemoveFromScheduledIRSet:
            controllerWaitForLockFree();
            ofcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL];
        
        FailBeforeRemoveIR:
            controllerWaitForLockFree();
            modifiedRemove();
    end while;
    
    ControllerThreadStateReconciliation:
        controllerReleaseLock();
        if (ofcInternalState[self].type = STATUS_LOCKING) then
            if (NIBIRStatus[ofcInternalState[self].next] = IR_SENT) then
                NIBIRStatus[ofcInternalState[self].next] := IR_NONE;
            end if;                 
            if (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2]) then
                idThreadWorkingOnIR[ofcInternalState[self].next] := NADIR_NULL;
            end if;        
        elsif (ofcInternalState[self].type = STATUS_SENT_DONE) then       
            if (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2]) then
                idThreadWorkingOnIR[ofcInternalState[self].next] := NADIR_NULL;
            end if;
        end if;
        goto ControllerThread;
    end process

    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = NADIR_NULL, setIRsToReset = {}, resetIR = NADIR_NULL;
    begin
    ControllerEventHandlerProc:
    while TRUE do  
        await Len(swSeqChangedStatus) > 0;
        controllerAcquireLock();

        monitoringEvent := Head(swSeqChangedStatus);
        if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            ControllerEventHandlerSuspendSW: 
                controllerWaitForLockFree();
                SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                RCNIBEventQueue := Append(
                    RCNIBEventQueue,
                    [
                        type |-> TOPO_MOD, 
                        sw |-> monitoringEvent.swID, 
                        state |-> SW_SUSPEND
                    ]
                );
                
        elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            ControllerCheckIfThisIsLastEvent:
                controllerReleaseLock();

                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    getIRsToBeChecked:
                        controllerWaitForLockFree();
                        setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                        if (setIRsToReset = {}) then
                            goto ControllerFreeSuspendedSW;
                        end if;

                    ResetAllIRs:
                        while TRUE do
                            controllerWaitForLockFree();
                            resetIR := CHOOSE x \in setIRsToReset: TRUE;
                            setIRsToReset := setIRsToReset \ {resetIR};
                            NIBIRStatus[resetIR] := IR_NONE;
                            RCNIBEventQueue := Append(
                                RCNIBEventQueue, 
                                [type |-> IR_MOD, IR |-> resetIR, state |-> IR_NONE]
                            );
                            if setIRsToReset = {} then
                                goto ControllerFreeSuspendedSW;
                            end if;
                        end while;
                end if;

            
            ControllerFreeSuspendedSW:
                controllerAcquireLock();
                ofcInternalState[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID];
            
            FailBeforeReturningSwitch:
                controllerAcquireLock();
                SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                RCNIBEventQueue := Append(
                    RCNIBEventQueue, 
                    [
                        type |-> TOPO_MOD, 
                        sw |-> monitoringEvent.swID, 
                        state |-> SW_RUN
                    ]
                );
        end if;

        ControllerEvenHanlderRemoveEventFromQueue:
            controllerReleaseLock();
            ofcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL]; 
        
        FailBeforeRemovingEvent:
            controllerReleaseLock();
            swSeqChangedStatus := Tail(swSeqChangedStatus);
    end while;

    ControllerEventHandlerStateReconciliation:
         controllerReleaseLock();
         if (ofcInternalState[self].type = START_RESET_IR) then
            SwSuspensionStatus[ofcInternalState[self].sw] := SW_SUSPEND;
            RCNIBEventQueue := Append(
                RCNIBEventQueue, 
                [
                    type |-> TOPO_MOD, 
                    sw |-> monitoringEvent.swID, 
                    state |-> SW_SUSPEND
                ]
            );
         end if;
        goto ControllerEventHandlerProc;
    end process

    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = NADIR_NULL, irID = NADIR_NULL, removedIR = NADIR_NULL;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        await Len(switch2Controller) > 0;

        controllerAcquireLock();
        msg := Head(switch2Controller);
        assert msg.flow \in 1..MaxNumIRs;
        irID := getIRIDForFlow(msg.flow, msg.type);
        assert msg.from = ir2sw[irID];
        
        ControllerUpdateIRDone:
            controllerWaitForLockFree(); 

            FirstInstall[irID] := 1;
            if NIBIRStatus[irID] = IR_SENT then
                NIBIRStatus[irID] := IR_DONE; 
                RCNIBEventQueue := Append(
                    RCNIBEventQueue, 
                    [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                );
            end if;
            
            if msg.type = DELETED_SUCCESSFULLY then 
                removedIR := msg.flow;
                ControllerMonUpdateIRNone:
                    controllerWaitForLockFree();
                    NIBIRStatus[removedIR] := IR_NONE; 
                    RCNIBEventQueue := Append(
                        RCNIBEventQueue, 
                        [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]
                    );
            end if;

        MonitoringServerRemoveFromQueue:
            controllerReleaseLock();
            switch2Controller := Tail(switch2Controller);
    end while
    end process
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "e1a963f3")
VARIABLES switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
          switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
          IRQueueNIB, RCNIBEventQueue, FirstInstall, RCProcSet, OFCProcSet, 
          ContProcSet, DAGState, RCIRStatus, RCSwSuspensionStatus, 
          NIBIRStatus, SwSuspensionStatus, rcInternalState, ofcInternalState, 
          SetScheduledIRs, ir2sw, seqWorkerIsBusy, IRDoneSet, 
          idThreadWorkingOnIR, pc

(* define statement *)
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]
getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}
ExistsEntryWithTag(tag) == \E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].tag = tag
FirstUntaggedEntry(num) == ~\E x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = NADIR_NULL
                                                        /\ x < num
getFirstIRIndexToRead(threadID) == CHOOSE x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                                   \/ /\ ~ExistsEntryWithTag(threadID)
                                                                      /\ FirstUntaggedEntry(x)
getFirstIndexWith(RID, threadID) == CHOOSE x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = threadID
                                                                    /\ IRQueueNIB[x].IR = RID

getSetRemovableIRs(swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ RCIRStatus[x] # IR_NONE
                                                              \/ x \in SetScheduledIRs[ir2sw[x]]
                                                           /\ x \notin nxtDAGV
                                                           /\ ir2sw[x] \in swSet}
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
allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: RCIRStatus[y] # IR_DONE
allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getIRType(y) = INSTALL_FLOW
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
getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                             /\ NIBIRStatus[x] \notin {IR_NONE}}
isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE
dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag)
                                            /\ ~isDAGStale(dagObject.id)
                                         \/ ~allIRsInDAGAreStable(dagObject.dag)

VARIABLES event, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, 
          nxtDAG, deleterID, setRemovableIRs, currIR, currIRInDAG, 
          nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, worker, 
          toBeScheduledIRs, nextIR, currDAG, IRSet, nextIRIDToSend, rowIndex, 
          rowRemove, monitoringEvent, setIRsToReset, resetIR, msg, irID, 
          removedIR

vars == << switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
           switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
           IRQueueNIB, RCNIBEventQueue, FirstInstall, RCProcSet, OFCProcSet, 
           ContProcSet, DAGState, RCIRStatus, RCSwSuspensionStatus, 
           NIBIRStatus, SwSuspensionStatus, rcInternalState, ofcInternalState, 
           SetScheduledIRs, ir2sw, seqWorkerIsBusy, IRDoneSet, 
           idThreadWorkingOnIR, pc, event, topoChangeEvent, currSetDownSw, 
           prev_dag_id, init, DAGID, nxtDAG, deleterID, setRemovableIRs, 
           currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, 
           seqEvent, worker, toBeScheduledIRs, nextIR, currDAG, IRSet, 
           nextIRIDToSend, rowIndex, rowRemove, monitoringEvent, 
           setIRsToReset, resetIR, msg, irID, removedIR >>

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
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        /\ RCProcSet = ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, NIB_EVENT_HANDLER, CONT_TE, CONT_MONITOR})
        /\ OFCProcSet = ((({ofc0} \X CONTROLLER_THREAD_POOL)) \cup
                         (({ofc0} \X {CONT_EVENT})) \cup
                         (({ofc0} \X {CONT_MONITOR})))
        /\ ContProcSet = (RCProcSet \cup OFCProcSet)
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
        /\ IRDoneSet = {}
        /\ idThreadWorkingOnIR = [x \in 1..2*MaxNumIRs |-> NADIR_NULL]
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
        (* Process controllerWorkerThreads *)
        /\ nextIRIDToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ rowIndex = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ rowRemove = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
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
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ event' = [event EXCEPT ![self] = Head(RCNIBEventQueue)]
                               /\ Assert(event'[self].type \in {TOPO_MOD, IR_MOD}, 
                                         "Failure of assertion at line 204, column 9.")
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
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, FirstInstall, 
                                               RCProcSet, OFCProcSet, 
                                               ContProcSet, DAGState, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, ir2sw, 
                                               seqWorkerIsBusy, IRDoneSet, 
                                               idThreadWorkingOnIR, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, currDAG, IRSet, 
                                               nextIRIDToSend, rowIndex, 
                                               rowRemove, monitoringEvent, 
                                               setIRsToReset, resetIR, msg, 
                                               irID, removedIR >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ init[self] = 1 \/ Len(TEEventQueue) > 0
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ controllerLock' = self
                          /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, IRQueueNIB, 
                                          RCNIBEventQueue, FirstInstall, 
                                          RCProcSet, OFCProcSet, ContProcSet, 
                                          DAGState, RCIRStatus, 
                                          RCSwSuspensionStatus, NIBIRStatus, 
                                          SwSuspensionStatus, rcInternalState, 
                                          ofcInternalState, SetScheduledIRs, 
                                          ir2sw, seqWorkerIsBusy, IRDoneSet, 
                                          idThreadWorkingOnIR, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, DAGID, nxtDAG, 
                                          deleterID, setRemovableIRs, currIR, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          worker, toBeScheduledIRs, nextIR, 
                                          currDAG, IRSet, nextIRIDToSend, 
                                          rowIndex, rowRemove, monitoringEvent, 
                                          setIRsToReset, resetIR, msg, irID, 
                                          removedIR >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF Len(TEEventQueue) > 0
                                           THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                                /\ Assert(topoChangeEvent'[self].type \in {TOPO_MOD}, 
                                                          "Failure of assertion at line 235, column 17.")
                                                /\ IF topoChangeEvent'[self].state = SW_SUSPEND
                                                      THEN /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \cup {topoChangeEvent'[self].sw}]
                                                      ELSE /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \ {topoChangeEvent'[self].sw}]
                                                /\ TEEventQueue' = Tail(TEEventQueue)
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
                                                     RCNIBEventQueue, 
                                                     FirstInstall, RCProcSet, 
                                                     OFCProcSet, ContProcSet, 
                                                     DAGState, RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     SetScheduledIRs, ir2sw, 
                                                     seqWorkerIsBusy, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     event, prev_dag_id, init, 
                                                     DAGID, nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRSet, 
                                                     nextIRIDToSend, rowIndex, 
                                                     rowRemove, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, irID, removedIR >>

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
                                                           swSeqChangedStatus, 
                                                           controller2Switch, 
                                                           switch2Controller, 
                                                           TEEventQueue, 
                                                           DAGEventQueue, 
                                                           DAGQueue, 
                                                           IRQueueNIB, 
                                                           RCNIBEventQueue, 
                                                           FirstInstall, 
                                                           RCProcSet, 
                                                           OFCProcSet, 
                                                           ContProcSet, 
                                                           RCIRStatus, 
                                                           RCSwSuspensionStatus, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           rcInternalState, 
                                                           ofcInternalState, 
                                                           SetScheduledIRs, 
                                                           ir2sw, 
                                                           seqWorkerIsBusy, 
                                                           IRDoneSet, 
                                                           idThreadWorkingOnIR, 
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
                                                           IRSet, 
                                                           nextIRIDToSend, 
                                                           rowIndex, rowRemove, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, msg, irID, 
                                                           removedIR >>

ControllerTESendDagStaleNotif(self) == /\ pc[self] = "ControllerTESendDagStaleNotif"
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ DAGEventQueue' = Append(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id[self]])
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       TEEventQueue, DAGQueue, 
                                                       IRQueueNIB, 
                                                       RCNIBEventQueue, 
                                                       FirstInstall, RCProcSet, 
                                                       OFCProcSet, ContProcSet, 
                                                       DAGState, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       SetScheduledIRs, ir2sw, 
                                                       seqWorkerIsBusy, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       event, topoChangeEvent, 
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
                                                       nextIRIDToSend, 
                                                       rowIndex, rowRemove, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       msg, irID, removedIR >>

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
                                                                swSeqChangedStatus, 
                                                                controller2Switch, 
                                                                switch2Controller, 
                                                                TEEventQueue, 
                                                                DAGEventQueue, 
                                                                DAGQueue, 
                                                                IRQueueNIB, 
                                                                RCNIBEventQueue, 
                                                                FirstInstall, 
                                                                RCProcSet, 
                                                                OFCProcSet, 
                                                                ContProcSet, 
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
                                                                IRDoneSet, 
                                                                idThreadWorkingOnIR, 
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
                                                                nextIRIDToSend, 
                                                                rowIndex, 
                                                                rowRemove, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, msg, 
                                                                irID, 
                                                                removedIR >>

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
                                                                /\ FirstInstall' = FirstInstall  @@ (deleterID'[self] :> 0)
                                                                /\ ir2sw' = ir2sw         @@ (deleterID'[self] :> ir2sw[currIR'[self]])
                                                           ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                                /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                                /\ UNCHANGED << FirstInstall, 
                                                                                ir2sw >>
                                                     /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {deleterID'[self]}]
                                                     /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(ir2sw'[currIR'[self]], nxtDAGVertices[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                                     /\ UNCHANGED SetScheduledIRs
                                                ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                     /\ SetScheduledIRs' = [x \in SW |-> (SetScheduledIRs[x] \ nxtDAG[self].dag.v)]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                                     /\ UNCHANGED << FirstInstall, 
                                                                     RCIRStatus, 
                                                                     NIBIRStatus, 
                                                                     ir2sw, 
                                                                     nxtDAG, 
                                                                     deleterID, 
                                                                     setRemovableIRs, 
                                                                     currIR, 
                                                                     setIRsInDAG >>
                                          /\ UNCHANGED << switchLock, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          RCProcSet, 
                                                          OFCProcSet, 
                                                          ContProcSet, 
                                                          DAGState, 
                                                          RCSwSuspensionStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          seqWorkerIsBusy, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
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
                                                          IRSet, 
                                                          nextIRIDToSend, 
                                                          rowIndex, rowRemove, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID, 
                                                          removedIR >>

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
                             /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, RCNIBEventQueue, 
                                             FirstInstall, RCProcSet, 
                                             OFCProcSet, ContProcSet, DAGState, 
                                             RCIRStatus, RCSwSuspensionStatus, 
                                             NIBIRStatus, SwSuspensionStatus, 
                                             rcInternalState, ofcInternalState, 
                                             SetScheduledIRs, ir2sw, 
                                             seqWorkerIsBusy, IRDoneSet, 
                                             idThreadWorkingOnIR, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, 
                                             deleterID, setRemovableIRs, 
                                             currIR, nxtDAGVertices, prev_dag, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, currDAG, 
                                             IRSet, nextIRIDToSend, rowIndex, 
                                             rowRemove, monitoringEvent, 
                                             setIRsToReset, resetIR, msg, irID, 
                                             removedIR >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' =                  Append(
                                                          DAGEventQueue,
                                                          [type |-> DAG_NEW, dag_obj |-> nxtDAG[self]]
                                                      )
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  TEEventQueue, DAGQueue, 
                                                  IRQueueNIB, RCNIBEventQueue, 
                                                  FirstInstall, RCProcSet, 
                                                  OFCProcSet, ContProcSet, 
                                                  RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  rcInternalState, 
                                                  ofcInternalState, 
                                                  SetScheduledIRs, ir2sw, 
                                                  seqWorkerIsBusy, IRDoneSet, 
                                                  idThreadWorkingOnIR, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  deleterID, setRemovableIRs, 
                                                  currIR, currIRInDAG, 
                                                  nxtDAGVertices, setIRsInDAG, 
                                                  prev_dag, seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  currDAG, IRSet, 
                                                  nextIRIDToSend, rowIndex, 
                                                  rowRemove, monitoringEvent, 
                                                  setIRsToReset, resetIR, msg, 
                                                  irID, removedIR >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTESendDagStaleNotif(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTEAddEdge(self)
                                         \/ ControllerTESubmitNewDAG(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ Len(DAGEventQueue) > 0
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue)]
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ Assert(seqEvent'[self].type \in {DAG_NEW, DAG_STALE}, 
                                         "Failure of assertion at line 315, column 9.")
                               /\ IF seqEvent'[self].type = DAG_NEW
                                     THEN /\ DAGQueue' = Append(DAGQueue, seqEvent'[self].dag_obj)
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
                                               FirstInstall, RCProcSet, 
                                               OFCProcSet, ContProcSet, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, ir2sw, 
                                               seqWorkerIsBusy, IRDoneSet, 
                                               idThreadWorkingOnIR, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, worker, 
                                               toBeScheduledIRs, nextIR, 
                                               currDAG, IRSet, nextIRIDToSend, 
                                               rowIndex, rowRemove, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, irID, removedIR >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                     FirstInstall, RCProcSet, 
                                                     OFCProcSet, ContProcSet, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     SetScheduledIRs, ir2sw, 
                                                     seqWorkerIsBusy, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     event, topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRSet, 
                                                     nextIRIDToSend, rowIndex, 
                                                     rowRemove, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, irID, removedIR >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ Len(DAGQueue) > 0
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue)]
                                 /\ seqWorkerIsBusy' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 TEEventQueue, DAGEventQueue, 
                                                 DAGQueue, IRQueueNIB, 
                                                 RCNIBEventQueue, FirstInstall, 
                                                 RCProcSet, OFCProcSet, 
                                                 ContProcSet, DAGState, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 rcInternalState, 
                                                 ofcInternalState, 
                                                 SetScheduledIRs, ir2sw, 
                                                 IRDoneSet, 
                                                 idThreadWorkingOnIR, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 deleterID, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 IRSet, nextIRIDToSend, 
                                                 rowIndex, rowRemove, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 irID, removedIR >>

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
                                                        swSeqChangedStatus, 
                                                        controller2Switch, 
                                                        switch2Controller, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, IRQueueNIB, 
                                                        RCNIBEventQueue, 
                                                        FirstInstall, 
                                                        RCProcSet, OFCProcSet, 
                                                        ContProcSet, DAGState, 
                                                        RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        rcInternalState, 
                                                        ofcInternalState, 
                                                        SetScheduledIRs, ir2sw, 
                                                        IRDoneSet, 
                                                        idThreadWorkingOnIR, 
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
                                                        nextIRIDToSend, 
                                                        rowIndex, rowRemove, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        msg, irID, removedIR >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                            /\ pc' = [pc EXCEPT ![self] = "FailBeforeStartSched"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, 
                                            IRQueueNIB, RCNIBEventQueue, 
                                            FirstInstall, RCProcSet, 
                                            OFCProcSet, ContProcSet, DAGState, 
                                            RCIRStatus, RCSwSuspensionStatus, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            rcInternalState, ofcInternalState, 
                                            SetScheduledIRs, ir2sw, 
                                            seqWorkerIsBusy, IRDoneSet, 
                                            idThreadWorkingOnIR, event, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, DAGID, nxtDAG, 
                                            deleterID, setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, currDAG, 
                                            IRSet, nextIRIDToSend, rowIndex, 
                                            rowRemove, monitoringEvent, 
                                            setIRsToReset, resetIR, msg, irID, 
                                            removedIR >>

FailBeforeStartSched(self) == /\ pc[self] = "FailBeforeStartSched"
                              /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                              /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> STATUS_START_SCHEDULING, next |-> nextIR[self]]]
                              /\ pc' = [pc EXCEPT ![self] = "FailBeforeAddingToSched"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, 
                                              IRQueueNIB, RCNIBEventQueue, 
                                              FirstInstall, RCProcSet, 
                                              OFCProcSet, ContProcSet, 
                                              DAGState, RCIRStatus, 
                                              RCSwSuspensionStatus, 
                                              NIBIRStatus, SwSuspensionStatus, 
                                              ofcInternalState, 
                                              SetScheduledIRs, ir2sw, 
                                              seqWorkerIsBusy, IRDoneSet, 
                                              idThreadWorkingOnIR, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, DAGID, nxtDAG, 
                                              deleterID, setRemovableIRs, 
                                              currIR, currIRInDAG, 
                                              nxtDAGVertices, setIRsInDAG, 
                                              prev_dag, seqEvent, worker, 
                                              toBeScheduledIRs, nextIR, 
                                              currDAG, IRSet, nextIRIDToSend, 
                                              rowIndex, rowRemove, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, msg, irID, removedIR >>

FailBeforeAddingToSched(self) == /\ pc[self] = "FailBeforeAddingToSched"
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[nextIR[self]]] = SetScheduledIRs[ir2sw[nextIR[self]]] \cup {nextIR[self]}]
                                 /\ pc' = [pc EXCEPT ![self] = "AddDeleteIRIRDoneSet"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 TEEventQueue, DAGEventQueue, 
                                                 DAGQueue, IRQueueNIB, 
                                                 RCNIBEventQueue, FirstInstall, 
                                                 RCProcSet, OFCProcSet, 
                                                 ContProcSet, DAGState, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 rcInternalState, 
                                                 ofcInternalState, ir2sw, 
                                                 seqWorkerIsBusy, IRDoneSet, 
                                                 idThreadWorkingOnIR, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 deleterID, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 currDAG, IRSet, 
                                                 nextIRIDToSend, rowIndex, 
                                                 rowRemove, monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 irID, removedIR >>

AddDeleteIRIRDoneSet(self) == /\ pc[self] = "AddDeleteIRIRDoneSet"
                              /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                              /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF getIRType(nextIR[self]) = INSTALL_FLOW
                                    THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR[self]})
                                    ELSE /\ IRDoneSet' = IRDoneSet \ {getDualOfIR(nextIR[self])}
                              /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, 
                                              IRQueueNIB, RCNIBEventQueue, 
                                              FirstInstall, RCProcSet, 
                                              OFCProcSet, ContProcSet, 
                                              DAGState, RCIRStatus, 
                                              RCSwSuspensionStatus, 
                                              NIBIRStatus, SwSuspensionStatus, 
                                              rcInternalState, 
                                              ofcInternalState, 
                                              SetScheduledIRs, ir2sw, 
                                              seqWorkerIsBusy, 
                                              idThreadWorkingOnIR, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, DAGID, nxtDAG, 
                                              deleterID, setRemovableIRs, 
                                              currIR, currIRInDAG, 
                                              nxtDAGVertices, setIRsInDAG, 
                                              prev_dag, seqEvent, worker, 
                                              toBeScheduledIRs, nextIR, 
                                              currDAG, IRSet, nextIRIDToSend, 
                                              rowIndex, rowRemove, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, msg, irID, removedIR >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> nextIR[self], tag |-> NADIR_NULL])
                       /\ pc' = [pc EXCEPT ![self] = "FailBeforeRemovingFromSched"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, TEEventQueue, 
                                       DAGEventQueue, DAGQueue, 
                                       RCNIBEventQueue, FirstInstall, 
                                       RCProcSet, OFCProcSet, ContProcSet, 
                                       DAGState, RCIRStatus, 
                                       RCSwSuspensionStatus, NIBIRStatus, 
                                       SwSuspensionStatus, rcInternalState, 
                                       ofcInternalState, SetScheduledIRs, 
                                       ir2sw, seqWorkerIsBusy, IRDoneSet, 
                                       idThreadWorkingOnIR, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, DAGID, nxtDAG, 
                                       deleterID, setRemovableIRs, currIR, 
                                       currIRInDAG, nxtDAGVertices, 
                                       setIRsInDAG, prev_dag, seqEvent, worker, 
                                       toBeScheduledIRs, nextIR, currDAG, 
                                       IRSet, nextIRIDToSend, rowIndex, 
                                       rowRemove, monitoringEvent, 
                                       setIRsToReset, resetIR, msg, irID, 
                                       removedIR >>

FailBeforeRemovingFromSched(self) == /\ pc[self] = "FailBeforeRemovingFromSched"
                                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                     /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self] \ {nextIR[self]}]
                                     /\ pc' = [pc EXCEPT ![self] = "FailBeforeClearingInternal"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     IRQueueNIB, 
                                                     RCNIBEventQueue, 
                                                     FirstInstall, RCProcSet, 
                                                     OFCProcSet, ContProcSet, 
                                                     DAGState, RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     SetScheduledIRs, ir2sw, 
                                                     seqWorkerIsBusy, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     event, topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, DAGID, 
                                                     nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, nextIR, 
                                                     currDAG, IRSet, 
                                                     nextIRIDToSend, rowIndex, 
                                                     rowRemove, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, irID, removedIR >>

FailBeforeClearingInternal(self) == /\ pc[self] = "FailBeforeClearingInternal"
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                                    /\ IF toBeScheduledIRs[self] = {} \/ isDAGStale(currDAG[self].id)
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    IRQueueNIB, 
                                                    RCNIBEventQueue, 
                                                    FirstInstall, RCProcSet, 
                                                    OFCProcSet, ContProcSet, 
                                                    DAGState, RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    ofcInternalState, 
                                                    SetScheduledIRs, ir2sw, 
                                                    seqWorkerIsBusy, IRDoneSet, 
                                                    idThreadWorkingOnIR, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    deleterID, setRemovableIRs, 
                                                    currIR, currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    currDAG, IRSet, 
                                                    nextIRIDToSend, rowIndex, 
                                                    rowRemove, monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    msg, irID, removedIR >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {} /\ allIRsInDAGInstalled(currDAG[self].dag)
                                     THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF getIRType(nextIR'[self]) = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR'[self]})
                                                ELSE /\ IRDoneSet' = IRDoneSet \ {getDualOfIR(nextIR'[self])}
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                          /\ UNCHANGED << controllerLock, 
                                                          DAGQueue >>
                                     ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ DAGQueue' = Tail(DAGQueue)
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << IRDoneSet, nextIR, 
                                                          IRSet >>
                               /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               DAGEventQueue, IRQueueNIB, 
                                               RCNIBEventQueue, FirstInstall, 
                                               RCProcSet, OFCProcSet, 
                                               ContProcSet, DAGState, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, ir2sw, 
                                               seqWorkerIsBusy, 
                                               idThreadWorkingOnIR, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               currDAG, nextIRIDToSend, 
                                               rowIndex, rowRemove, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, irID, removedIR >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (rcInternalState[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[rcInternalState[self].next]] = SetScheduledIRs[ir2sw[rcInternalState[self].next]] \ {rcInternalState[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << switchLock, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, IRQueueNIB, 
                                                          RCNIBEventQueue, 
                                                          FirstInstall, 
                                                          RCProcSet, 
                                                          OFCProcSet, 
                                                          ContProcSet, 
                                                          DAGState, RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          ir2sw, 
                                                          seqWorkerIsBusy, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
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
                                                          IRSet, 
                                                          nextIRIDToSend, 
                                                          rowIndex, rowRemove, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID, 
                                                          removedIR >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ FailBeforeStartSched(self)
                                \/ FailBeforeAddingToSched(self)
                                \/ AddDeleteIRIRDoneSet(self)
                                \/ ScheduleTheIR(self)
                                \/ FailBeforeRemovingFromSched(self)
                                \/ FailBeforeClearingInternal(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ ControllerSeqStateReconciliation(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ ExistsEntryWithTag(NADIR_NULL) \/ ExistsEntryWithTag(self)
                          /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead(self)]
                          /\ nextIRIDToSend' = [nextIRIDToSend EXCEPT ![self] = IRQueueNIB[rowIndex'[self]].IR]
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![rowIndex'[self]].tag = self]
                          /\ pc' = [pc EXCEPT ![self] = "FailBeforeLocking"]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, RCNIBEventQueue, 
                                          FirstInstall, RCProcSet, OFCProcSet, 
                                          ContProcSet, DAGState, RCIRStatus, 
                                          RCSwSuspensionStatus, NIBIRStatus, 
                                          SwSuspensionStatus, rcInternalState, 
                                          ofcInternalState, SetScheduledIRs, 
                                          ir2sw, seqWorkerIsBusy, IRDoneSet, 
                                          idThreadWorkingOnIR, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, DAGID, nxtDAG, 
                                          deleterID, setRemovableIRs, currIR, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          worker, toBeScheduledIRs, nextIR, 
                                          currDAG, IRSet, rowRemove, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, msg, irID, removedIR >>

FailBeforeLocking(self) == /\ pc[self] = "FailBeforeLocking"
                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRIDToSend[self]]]
                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadLockIR"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, IRQueueNIB, 
                                           RCNIBEventQueue, FirstInstall, 
                                           RCProcSet, OFCProcSet, ContProcSet, 
                                           DAGState, RCIRStatus, 
                                           RCSwSuspensionStatus, NIBIRStatus, 
                                           SwSuspensionStatus, rcInternalState, 
                                           SetScheduledIRs, ir2sw, 
                                           seqWorkerIsBusy, IRDoneSet, 
                                           idThreadWorkingOnIR, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, DAGID, nxtDAG, 
                                           deleterID, setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           currDAG, IRSet, nextIRIDToSend, 
                                           rowIndex, rowRemove, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, msg, irID, removedIR >>

ControllerThreadLockIR(self) == /\ pc[self] = "ControllerThreadLockIR"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF idThreadWorkingOnIR[nextIRIDToSend[self]] = NADIR_NULL
                                      THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRIDToSend[self]] = self[2]]
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadWaitForIRUnlock"]
                                           /\ UNCHANGED idThreadWorkingOnIR
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, 
                                                RCNIBEventQueue, FirstInstall, 
                                                RCProcSet, OFCProcSet, 
                                                ContProcSet, DAGState, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                NIBIRStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, ir2sw, 
                                                seqWorkerIsBusy, IRDoneSet, 
                                                event, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, DAGID, nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRSet, nextIRIDToSend, 
                                                rowIndex, rowRemove, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, msg, irID, removedIR >>

ControllerThreadWaitForIRUnlock(self) == /\ pc[self] = "ControllerThreadWaitForIRUnlock"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ idThreadWorkingOnIR[nextIRIDToSend[self]] = NADIR_NULL
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         RCNIBEventQueue, 
                                                         FirstInstall, 
                                                         RCProcSet, OFCProcSet, 
                                                         ContProcSet, DAGState, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         SetScheduledIRs, 
                                                         ir2sw, 
                                                         seqWorkerIsBusy, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
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
                                                         IRSet, nextIRIDToSend, 
                                                         rowIndex, rowRemove, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, irID, 
                                                         removedIR >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF ~isSwitchSuspended(ir2sw[nextIRIDToSend[self]]) /\ NIBIRStatus[nextIRIDToSend[self]] = IR_NONE
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![nextIRIDToSend[self]] = IR_SENT]
                                           /\ RCNIBEventQueue' =                    Append(
                                                                     RCNIBEventQueue,
                                                                     [type |-> IR_MOD, IR |-> nextIRIDToSend[self], state |-> IR_SENT]
                                                                 )
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, 
                                                FirstInstall, RCProcSet, 
                                                OFCProcSet, ContProcSet, 
                                                DAGState, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, ir2sw, 
                                                seqWorkerIsBusy, IRDoneSet, 
                                                idThreadWorkingOnIR, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRSet, nextIRIDToSend, 
                                                rowIndex, rowRemove, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, msg, irID, removedIR >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ Assert(nextIRIDToSend[self] \in 1..2*MaxNumIRs, 
                                             "Failure of assertion at line 136, column 9 of macro called at line 448, column 21.")
                                   /\ LET destination == ir2sw[nextIRIDToSend[self]] IN
                                        /\ controller2Switch' = [controller2Switch EXCEPT ![destination] =                                   Append(
                                                                                                               controller2Switch[destination],
                                                                                                               [
                                                                                                                   type |-> getIRType(nextIRIDToSend[self]),
                                                                                                                   flow |-> getIRFlow(nextIRIDToSend[self]),
                                                                                                                   to |-> destination,
                                                                                                                   from |-> self[1]
                                                                                                               ]
                                                                                                           )]
                                        /\ IF whichSwitchModel(destination) = SW_COMPLEX_MODEL
                                              THEN /\ switchLock' = <<NIC_ASIC_IN, destination>>
                                              ELSE /\ switchLock' = <<SW_SIMPLE_ID, destination>>
                                   /\ pc' = [pc EXCEPT ![self] = "FailBeforeStatusSentDone"]
                                   /\ UNCHANGED << controllerLock, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   RCNIBEventQueue, 
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   rcInternalState, 
                                                   ofcInternalState, 
                                                   SetScheduledIRs, ir2sw, 
                                                   seqWorkerIsBusy, IRDoneSet, 
                                                   idThreadWorkingOnIR, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, 
                                                   nextIRIDToSend, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR >>

FailBeforeStatusSentDone(self) == /\ pc[self] = "FailBeforeStatusSentDone"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_SENT_DONE, next |-> nextIRIDToSend[self]]]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, IRQueueNIB, 
                                                  RCNIBEventQueue, 
                                                  FirstInstall, RCProcSet, 
                                                  OFCProcSet, ContProcSet, 
                                                  DAGState, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  rcInternalState, 
                                                  SetScheduledIRs, ir2sw, 
                                                  seqWorkerIsBusy, IRDoneSet, 
                                                  idThreadWorkingOnIR, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  deleterID, setRemovableIRs, 
                                                  currIR, currIRInDAG, 
                                                  nxtDAGVertices, setIRsInDAG, 
                                                  prev_dag, seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  currDAG, IRSet, 
                                                  nextIRIDToSend, rowIndex, 
                                                  rowRemove, monitoringEvent, 
                                                  setIRsToReset, resetIR, msg, 
                                                  irID, removedIR >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ IF idThreadWorkingOnIR[nextIRIDToSend[self]] = self[2]
                                               THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRIDToSend[self]] = NADIR_NULL]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED idThreadWorkingOnIR
                                         /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         RCNIBEventQueue, 
                                                         FirstInstall, 
                                                         RCProcSet, OFCProcSet, 
                                                         ContProcSet, DAGState, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         SetScheduledIRs, 
                                                         ir2sw, 
                                                         seqWorkerIsBusy, 
                                                         IRDoneSet, event, 
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
                                                         IRSet, nextIRIDToSend, 
                                                         rowIndex, rowRemove, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, irID, 
                                                         removedIR >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                                  /\ pc' = [pc EXCEPT ![self] = "FailBeforeRemoveIR"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, IRQueueNIB, 
                                                  RCNIBEventQueue, 
                                                  FirstInstall, RCProcSet, 
                                                  OFCProcSet, ContProcSet, 
                                                  DAGState, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  rcInternalState, 
                                                  SetScheduledIRs, ir2sw, 
                                                  seqWorkerIsBusy, IRDoneSet, 
                                                  idThreadWorkingOnIR, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  deleterID, setRemovableIRs, 
                                                  currIR, currIRInDAG, 
                                                  nxtDAGVertices, setIRsInDAG, 
                                                  prev_dag, seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  currDAG, IRSet, 
                                                  nextIRIDToSend, rowIndex, 
                                                  rowRemove, monitoringEvent, 
                                                  setIRsToReset, resetIR, msg, 
                                                  irID, removedIR >>

FailBeforeRemoveIR(self) == /\ pc[self] = "FailBeforeRemoveIR"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRIDToSend[self], self)]
                            /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                            /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, 
                                            RCNIBEventQueue, FirstInstall, 
                                            RCProcSet, OFCProcSet, ContProcSet, 
                                            DAGState, RCIRStatus, 
                                            RCSwSuspensionStatus, NIBIRStatus, 
                                            SwSuspensionStatus, 
                                            rcInternalState, ofcInternalState, 
                                            SetScheduledIRs, ir2sw, 
                                            seqWorkerIsBusy, IRDoneSet, 
                                            idThreadWorkingOnIR, event, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, DAGID, nxtDAG, 
                                            deleterID, setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, nextIR, 
                                            currDAG, IRSet, nextIRIDToSend, 
                                            rowIndex, monitoringEvent, 
                                            setIRsToReset, resetIR, msg, irID, 
                                            removedIR >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (ofcInternalState[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (NIBIRStatus[ofcInternalState[self].next] = IR_SENT)
                                                              THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![ofcInternalState[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED NIBIRStatus
                                                        /\ IF (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2])
                                                              THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![ofcInternalState[self].next] = NADIR_NULL]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                   ELSE /\ IF (ofcInternalState[self].type = STATUS_SENT_DONE)
                                                              THEN /\ IF (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2])
                                                                         THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![ofcInternalState[self].next] = NADIR_NULL]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED idThreadWorkingOnIR
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                        /\ UNCHANGED NIBIRStatus
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << switchLock, 
                                                             swSeqChangedStatus, 
                                                             controller2Switch, 
                                                             switch2Controller, 
                                                             TEEventQueue, 
                                                             DAGEventQueue, 
                                                             DAGQueue, 
                                                             IRQueueNIB, 
                                                             RCNIBEventQueue, 
                                                             FirstInstall, 
                                                             RCProcSet, 
                                                             OFCProcSet, 
                                                             ContProcSet, 
                                                             DAGState, 
                                                             RCIRStatus, 
                                                             RCSwSuspensionStatus, 
                                                             SwSuspensionStatus, 
                                                             rcInternalState, 
                                                             ofcInternalState, 
                                                             SetScheduledIRs, 
                                                             ir2sw, 
                                                             seqWorkerIsBusy, 
                                                             IRDoneSet, event, 
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
                                                             IRSet, 
                                                             nextIRIDToSend, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, msg, 
                                                             irID, removedIR >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ FailBeforeLocking(self)
                                    \/ ControllerThreadLockIR(self)
                                    \/ ControllerThreadWaitForIRUnlock(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ FailBeforeStatusSentDone(self)
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ FailBeforeRemoveIR(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ Len(swSeqChangedStatus) > 0
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerLock' = self
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << switchLock, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    IRQueueNIB, 
                                                    RCNIBEventQueue, 
                                                    FirstInstall, RCProcSet, 
                                                    OFCProcSet, ContProcSet, 
                                                    DAGState, RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    rcInternalState, 
                                                    ofcInternalState, 
                                                    SetScheduledIRs, ir2sw, 
                                                    seqWorkerIsBusy, IRDoneSet, 
                                                    idThreadWorkingOnIR, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    deleterID, setRemovableIRs, 
                                                    currIR, currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    currDAG, IRSet, 
                                                    nextIRIDToSend, rowIndex, 
                                                    rowRemove, setIRsToReset, 
                                                    resetIR, msg, irID, 
                                                    removedIR >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                                                   /\ pc' = [pc EXCEPT ![self] = "FailBeforeRemovingEvent"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   IRQueueNIB, 
                                                                   RCNIBEventQueue, 
                                                                   FirstInstall, 
                                                                   RCProcSet, 
                                                                   OFCProcSet, 
                                                                   ContProcSet, 
                                                                   DAGState, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   NIBIRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   rcInternalState, 
                                                                   SetScheduledIRs, 
                                                                   ir2sw, 
                                                                   seqWorkerIsBusy, 
                                                                   IRDoneSet, 
                                                                   idThreadWorkingOnIR, 
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
                                                                   nextIRIDToSend, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   removedIR >>

FailBeforeRemovingEvent(self) == /\ pc[self] = "FailBeforeRemovingEvent"
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                 /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                 /\ UNCHANGED << switchLock, controller2Switch, 
                                                 switch2Controller, 
                                                 TEEventQueue, DAGEventQueue, 
                                                 DAGQueue, IRQueueNIB, 
                                                 RCNIBEventQueue, FirstInstall, 
                                                 RCProcSet, OFCProcSet, 
                                                 ContProcSet, DAGState, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 rcInternalState, 
                                                 ofcInternalState, 
                                                 SetScheduledIRs, ir2sw, 
                                                 seqWorkerIsBusy, IRDoneSet, 
                                                 idThreadWorkingOnIR, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 deleterID, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 currDAG, IRSet, 
                                                 nextIRIDToSend, rowIndex, 
                                                 rowRemove, monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 irID, removedIR >>

ControllerEventHandlerSuspendSW(self) == /\ pc[self] = "ControllerEventHandlerSuspendSW"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                                         /\ RCNIBEventQueue' =                    Append(
                                                                   RCNIBEventQueue,
                                                                   [
                                                                       type |-> TOPO_MOD,
                                                                       sw |-> monitoringEvent[self].swID,
                                                                       state |-> SW_SUSPEND
                                                                   ]
                                                               )
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         FirstInstall, 
                                                         RCProcSet, OFCProcSet, 
                                                         ContProcSet, DAGState, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         NIBIRStatus, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         SetScheduledIRs, 
                                                         ir2sw, 
                                                         seqWorkerIsBusy, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
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
                                                         IRSet, nextIRIDToSend, 
                                                         rowIndex, rowRemove, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, irID, 
                                                         removedIR >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
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
                                                          FirstInstall, 
                                                          RCProcSet, 
                                                          OFCProcSet, 
                                                          ContProcSet, 
                                                          DAGState, RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          SetScheduledIRs, 
                                                          ir2sw, 
                                                          seqWorkerIsBusy, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
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
                                                          IRSet, 
                                                          nextIRIDToSend, 
                                                          rowIndex, rowRemove, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID, 
                                                          removedIR >>

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
                                           RCNIBEventQueue, FirstInstall, 
                                           RCProcSet, OFCProcSet, ContProcSet, 
                                           DAGState, RCIRStatus, 
                                           RCSwSuspensionStatus, NIBIRStatus, 
                                           SwSuspensionStatus, rcInternalState, 
                                           ofcInternalState, SetScheduledIRs, 
                                           ir2sw, seqWorkerIsBusy, IRDoneSet, 
                                           idThreadWorkingOnIR, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, DAGID, nxtDAG, 
                                           deleterID, setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           currDAG, IRSet, nextIRIDToSend, 
                                           rowIndex, rowRemove, 
                                           monitoringEvent, resetIR, msg, irID, 
                                           removedIR >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                     /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                     /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]] = IR_NONE]
                     /\ RCNIBEventQueue' =                    Append(
                                               RCNIBEventQueue,
                                               [type |-> IR_MOD, IR |-> resetIR'[self], state |-> IR_NONE]
                                           )
                     /\ IF setIRsToReset'[self] = {}
                           THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                     /\ UNCHANGED << switchLock, controllerLock, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, IRQueueNIB, 
                                     FirstInstall, RCProcSet, OFCProcSet, 
                                     ContProcSet, DAGState, RCIRStatus, 
                                     RCSwSuspensionStatus, SwSuspensionStatus, 
                                     rcInternalState, ofcInternalState, 
                                     SetScheduledIRs, ir2sw, seqWorkerIsBusy, 
                                     IRDoneSet, idThreadWorkingOnIR, event, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     deleterID, setRemovableIRs, currIR, 
                                     currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                     prev_dag, seqEvent, worker, 
                                     toBeScheduledIRs, nextIR, currDAG, IRSet, 
                                     nextIRIDToSend, rowIndex, rowRemove, 
                                     monitoringEvent, msg, irID, removedIR >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerLock' = self
                                   /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                   /\ pc' = [pc EXCEPT ![self] = "FailBeforeReturningSwitch"]
                                   /\ UNCHANGED << switchLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   RCNIBEventQueue, 
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   rcInternalState, 
                                                   SetScheduledIRs, ir2sw, 
                                                   seqWorkerIsBusy, IRDoneSet, 
                                                   idThreadWorkingOnIR, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, 
                                                   nextIRIDToSend, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR >>

FailBeforeReturningSwitch(self) == /\ pc[self] = "FailBeforeReturningSwitch"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerLock' = self
                                   /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                   /\ RCNIBEventQueue' =                    Append(
                                                             RCNIBEventQueue,
                                                             [
                                                                 type |-> TOPO_MOD,
                                                                 sw |-> monitoringEvent[self].swID,
                                                                 state |-> SW_RUN
                                                             ]
                                                         )
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   /\ UNCHANGED << switchLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   NIBIRStatus, 
                                                   rcInternalState, 
                                                   ofcInternalState, 
                                                   SetScheduledIRs, ir2sw, 
                                                   seqWorkerIsBusy, IRDoneSet, 
                                                   idThreadWorkingOnIR, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, 
                                                   nextIRIDToSend, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (ofcInternalState[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![ofcInternalState[self].sw] = SW_SUSPEND]
                                                              /\ RCNIBEventQueue' =                    Append(
                                                                                        RCNIBEventQueue,
                                                                                        [
                                                                                            type |-> TOPO_MOD,
                                                                                            sw |-> monitoringEvent[self].swID,
                                                                                            state |-> SW_SUSPEND
                                                                                        ]
                                                                                    )
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                                              SwSuspensionStatus >>
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   IRQueueNIB, 
                                                                   FirstInstall, 
                                                                   RCProcSet, 
                                                                   OFCProcSet, 
                                                                   ContProcSet, 
                                                                   DAGState, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   NIBIRStatus, 
                                                                   rcInternalState, 
                                                                   ofcInternalState, 
                                                                   SetScheduledIRs, 
                                                                   ir2sw, 
                                                                   seqWorkerIsBusy, 
                                                                   IRDoneSet, 
                                                                   idThreadWorkingOnIR, 
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
                                                                   nextIRIDToSend, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   removedIR >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ FailBeforeRemovingEvent(self)
                                   \/ ControllerEventHandlerSuspendSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ FailBeforeReturningSwitch(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ Len(switch2Controller) > 0
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = self
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].flow \in 1..MaxNumIRs, 
                                                 "Failure of assertion at line 589, column 9.")
                                       /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg'[self].flow, msg'[self].type)]
                                       /\ Assert(msg'[self].from = ir2sw[irID'[self]], 
                                                 "Failure of assertion at line 591, column 9.")
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone"]
                                       /\ UNCHANGED << switchLock, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       TEEventQueue, 
                                                       DAGEventQueue, DAGQueue, 
                                                       IRQueueNIB, 
                                                       RCNIBEventQueue, 
                                                       FirstInstall, RCProcSet, 
                                                       OFCProcSet, ContProcSet, 
                                                       DAGState, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       SetScheduledIRs, ir2sw, 
                                                       seqWorkerIsBusy, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       event, topoChangeEvent, 
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
                                                       nextIRIDToSend, 
                                                       rowIndex, rowRemove, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       removedIR >>

ControllerUpdateIRDone(self) == /\ pc[self] = "ControllerUpdateIRDone"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ FirstInstall' = [FirstInstall EXCEPT ![irID[self]] = 1]
                                /\ IF NIBIRStatus[irID[self]] = IR_SENT
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID[self]] = IR_DONE]
                                           /\ RCNIBEventQueue' =                    Append(
                                                                     RCNIBEventQueue,
                                                                     [type |-> IR_MOD, IR |-> irID[self], state |-> IR_DONE]
                                                                 )
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
                                                DAGQueue, IRQueueNIB, 
                                                RCProcSet, OFCProcSet, 
                                                ContProcSet, DAGState, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, ir2sw, 
                                                seqWorkerIsBusy, IRDoneSet, 
                                                idThreadWorkingOnIR, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                currDAG, IRSet, nextIRIDToSend, 
                                                rowIndex, rowRemove, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, msg, irID >>

ControllerMonUpdateIRNone(self) == /\ pc[self] = "ControllerMonUpdateIRNone"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![removedIR[self]] = IR_NONE]
                                   /\ RCNIBEventQueue' =                    Append(
                                                             RCNIBEventQueue,
                                                             [type |-> IR_MOD, IR |-> removedIR[self], state |-> IR_NONE]
                                                         )
                                   /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   SwSuspensionStatus, 
                                                   rcInternalState, 
                                                   ofcInternalState, 
                                                   SetScheduledIRs, ir2sw, 
                                                   seqWorkerIsBusy, IRDoneSet, 
                                                   idThreadWorkingOnIR, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   currDAG, IRSet, 
                                                   nextIRIDToSend, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                         /\ switch2Controller' = Tail(switch2Controller)
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                         /\ UNCHANGED << switchLock, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         RCNIBEventQueue, 
                                                         FirstInstall, 
                                                         RCProcSet, OFCProcSet, 
                                                         ContProcSet, DAGState, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         SetScheduledIRs, 
                                                         ir2sw, 
                                                         seqWorkerIsBusy, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
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
                                                         IRSet, nextIRIDToSend, 
                                                         rowIndex, rowRemove, 
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
    IR: NADIR_INT_ID_SET, 
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

\* RCProcSet, OFCProcSet, ContProcSet not in type check

TypeOK ==  /\ NadirQueueOfMessages(MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE, swSeqChangedStatus)
           /\ NadirQueueOfMessages(MSG_SET_OF_ACK, switch2Controller)
           /\ NadirQueueOfMessages(MSG_SET_TE_EVENT, TEEventQueue)
           /\ NadirQueueOfMessages(MSG_SET_DAG_EVENT, DAGEventQueue)
           /\ NadirQueueOfMessages(STRUCT_SET_DAG_OBJECT, DAGQueue)
           /\ NadirQueueOfMessages(MSG_SET_TE_EVENT, RCNIBEventQueue)
           /\ NadirQueueOfMessages(STRUCT_SET_NIB_TAGGED_IR, IRQueueNIB)
           /\ NadirFunctionTypeCheck(Nat, ENUM_SET_DAG_STATE, DAGState)
           /\ NadirFunctionTypeCheck(Nat, SW, ir2sw)
           /\ NadirFunctionTypeCheck(SW, Seq(MSG_SET_OF_CMD), controller2Switch)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, ENUM_SET_IR_STATE, RCIRStatus)
           /\ NadirFunctionTypeCheck(SW, ENUM_SET_SW_STATE, RCSwSuspensionStatus)
           /\ seqWorkerIsBusy \in BOOLEAN 
           /\ IRDoneSet \in SUBSET NADIR_INT_ID_SET
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, NadirNullable(CONTROLLER_THREAD_POOL), idThreadWorkingOnIR)
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
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), nextIRIDToSend)
           /\ NadirLocalVariableTypeCheck(NadirNullable(Nat), rowIndex)
           /\ NadirLocalVariableTypeCheck(NadirNullable(Nat), rowRemove)
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

ASSUME NadirConstantAssumptions

=============================================================================

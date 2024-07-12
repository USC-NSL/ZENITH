------------------- MODULE NoFailover -------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Nadir

CONSTANTS SW
CONSTANTS ofc0, rc0
CONSTANTS CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_TE, CONT_RC_MONITOR
CONSTANTS CONTROLLER_THREAD_POOL, CONT_OFC_MONITOR, CONT_EVENT, NIB_EVENT_HANDLER
CONSTANTS IR_NONE, IR_SENT, IR_DONE
CONSTANTS SW_RUN, SW_SUSPEND
CONSTANTS DAG_STALE, DAG_NEW, DAG_SUBMIT, DAG_NONE
CONSTANTS TOPO_MOD, IR_MOD
CONSTANTS STATUS_START_SCHEDULING, STATUS_LOCKING, STATUS_SENT_DONE, START_RESET_IR
CONSTANTS INSTALL_FLOW, DELETE_FLOW, INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY, KEEP_ALIVE
CONSTANTS NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN, INSTALLER_UP
CONSTANTS MaxNumIRs, TOPO_DAG_MAPPING, IR2SW, IR2FLOW, MaxNumFlows, MaxDAGID
CONSTANTS TOTAL_IR_SET, TOTAL_IR_DEL_SET, TOTAL_DAG_SET, TOTAL_FLOW_SET
                 
(*--fair algorithm stateConsistency
    variables
        \* The set of processes. Nadir will generate identifiers for them as needed
        NadirProcSet = 
            ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_RC_MONITOR, NIB_EVENT_HANDLER, CONT_TE}) \cup 
            ({ofc0} \X {CONT_EVENT, CONT_OFC_MONITOR}) \cup
            ({ofc0} \X CONTROLLER_THREAD_POOL),

        \* We need to think more about these two ...
        irTypeMapping = [x \in TOTAL_IR_SET |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]],
        ir2sw = IR2SW,

        \* The queue of messages between OFC and the switches
        swSeqChangedStatus = <<>>,
        controller2Switch = [x\in SW |-> <<>>],
        switch2Controller = <<>>,
        
        \* Local DB variables for internal states of OFC and RC
        rcInternalState = [x \in NadirProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]],
        ofcInternalState = [x \in NadirProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]],
        
        \* The queue of message from NIB to RC
        RCNIBEventQueue = <<>>,

        \* Internal queue of messages between RC threads
        TEEventQueue = <<>>,
        DAGEventQueue = <<>>,
        DAGQueue = <<>>,

        \* NIB tables
        NIBIRStatus = [x \in TOTAL_IR_SET |-> IR_NONE],
        DAGState = [x \in TOTAL_DAG_SET |-> DAG_NONE],
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        SetScheduledIRs = [y \in SW |-> {}],

        \* Queue of messages from NIB to OFC
        IRQueueNIB = <<>>,

        \* Local RC variables that need persistence
        RCIRStatus = [y \in TOTAL_IR_SET |-> IR_NONE],
        RCSwSuspensionStatus = [y \in SW |-> SW_RUN],
        nxtRCIRID = MaxNumIRs + 1,
        IRDoneSet = {},
        seqWorkerIsBusy = FALSE,

        \* Semaphore for locking IRs to worker pool threads
        idThreadWorkingOnIR = [x \in TOTAL_IR_SET |-> NADIR_NULL] @@                                 \* Installation IRs
                              [x \in TOTAL_IR_DEL_SET |-> NADIR_NULL]                                \* Deletion IRs
    define
        min(set) == CHOOSE x \in set: \A y \in set: x \leq y 
        rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
                                     
        SetSetUnion(Aset, Bset) == {x \cup y: x \in Aset, y \in Bset}
        
        NoEntryTaggedWith(threadID) == ~\E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].tag = threadID 
        FirstUntaggedEntry(threadID, num) == ~\E x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = NADIR_NULL
                                                                          /\ x < num
        getFirstIRIndexToRead(threadID) == CHOOSE x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                                           \/ /\ NoEntryTaggedWith(threadID)
                                                                              /\ FirstUntaggedEntry(threadID, x)
                                                                              /\ IRQueueNIB[x].tag = NADIR_NULL
        getFirstIndexWith(RID, threadID) == CHOOSE x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = threadID
                                                                            /\ IRQueueNIB[x].IR = RID
        getSetRemovableIRs(swSet, nxtDAGV) == {x \in TOTAL_IR_SET: /\ \/ RCIRStatus[x] # IR_NONE
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
        allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: RCIRStatus[y] # IR_DONE
        isDAGStale(id) == DAGState[id] # DAG_SUBMIT
        existIRInSetScheduledIRs(swID, type, flowID) == \E x \in SetScheduledIRs[swID]: /\ irTypeMapping[x].type = type
                                                                                        /\ ir2sw[x] = swID
                                                                                        /\ irTypeMapping[x].flow = flowID
        existIRDeletionInIRSent(swID, flowID) == \E x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = DELETE_FLOW
                                                                                /\ ir2sw[x] = swID
                                                                                /\ irTypeMapping[x].flow = flowID
                                                                                /\ RCIRStatus[x] = IR_SENT
        irMonitorShouldScheduleIR(irID) == \/ /\ irID \in IRDoneSet
                                              /\ RCIRStatus[irID] = IR_NONE
                                              /\ RCSwSuspensionStatus[IR2SW[irID]] = SW_RUN
                                              /\ ~existIRInSetScheduledIRs(ir2sw[irID], INSTALL_FLOW, irTypeMapping[irID].flow)
                                           \/ /\ irID \in (TOTAL_IR_SET) \ IRDoneSet
                                              /\ RCIRStatus[irID] = IR_DONE
                                              /\ RCSwSuspensionStatus[IR2SW[irID]] = SW_RUN
                                              /\ ~ existIRInSetScheduledIRs(ir2sw[irID], DELETE_FLOW, irTypeMapping[irID].flow)
                                              /\ ~ existIRDeletionInIRSent(ir2sw[irID], irTypeMapping[irID].flow)
        
        setIRMonitorShouldSchedule == {x \in TOTAL_IR_SET: irMonitorShouldScheduleIR(x)}                                         
                                                    
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        
        canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                                  \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NADIR_NULL 
                                                     /\ NoEntryTaggedWith(threadID) 
        
        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                        /\ swSeqChangedStatus[x].num > monEvent.num
        
        shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                                     \/ monEvent.type = NIC_ASIC_DOWN
                                     \/ /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.status.installerStatus = INSTALLER_DOWN
        
        canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.status.installerStatus = INSTALLER_UP
        
        getIRSetToReset(SID) == {x \in TOTAL_IR_SET: /\ ir2sw[x] = SID
                                                     /\ NIBIRStatus[x] \notin {IR_NONE}}

        getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                                \/ /\ irType = DELETED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = DELETE_FLOW
                                                                             /\ irTypeMapping[x].flow = flowID
        
        getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID
        
        isFinished == \A x \in TOTAL_IR_SET: NIBIRStatus[x] = IR_DONE                                                     
    end define
    
    macro controllerSendIR(s)
    begin
        assert irTypeMapping[s].type \in {INSTALL_FLOW, DELETE_FLOW};
        assert irTypeMapping[s].flow \in TOTAL_FLOW_SET;
        controller2Switch[ir2sw[s]] := Append(controller2Switch[ir2sw[s]], [type |-> irTypeMapping[s].type,
                                                                            to |-> ir2sw[s],
                                                                            flow |-> irTypeMapping[s].flow]);
    end macro;
    
    macro modifiedEnqueue(nextIR)
    begin
        IRQueueNIB := Append(IRQueueNIB, [IR |-> nextIR, tag |-> NADIR_NULL]);
    end macro;
    
    macro modifiedRead()
    begin
        rowIndex := getFirstIRIndexToRead(self);
        nextIRToSent := IRQueueNIB[rowIndex].IR;
        IRQueueNIB[rowIndex].tag := self;
    end macro;
    
    macro modifiedRemove()
    begin
        rowRemove := getFirstIndexWith(nextIRToSent, self);
        IRQueueNIB := removeFromSeq(IRQueueNIB, rowRemove);
    end macro;

    macro getNextIRID()
    begin
        nxtRCIRID := nxtRCIRID + 1;
    end macro;

    macro getNextDAGID()
    begin
        if DAGID = NADIR_NULL then
            DAGID := 1
        else
            DAGID := (DAGID % MaxDAGID) + 1
        end if;
    end macro;

    macro prepareDeletionIR(forWhat)
    begin
        RCIRStatus    := RCIRStatus    @@ (nxtRCIRID :> IR_NONE);
        NIBIRStatus   := NIBIRStatus   @@ (nxtRCIRID :> IR_NONE);
        irTypeMapping := irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[forWhat]]);
        ir2sw         := ir2sw         @@ (nxtRCIRID :> ir2sw[forWhat]);
    end macro;
    
    fair process rcNibEventHandler \in ({rc0} \X {NIB_EVENT_HANDLER})
    variables event = NADIR_NULL;
    begin
    RCSNIBEventHndlerProc:
    while TRUE do
        await RCNIBEventQueue # <<>>;

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
                if event.state \in {IR_SENT, IR_NONE, IR_DONE} then
                    SetScheduledIRs[ir2sw[event.IR]] := SetScheduledIRs[ir2sw[event.IR]]\{event.IR};    
                end if;
            end if;
        end if;
        RCNIBEventQueue := Tail(RCNIBEventQueue);
    end while;
    end process
    
    fair process controllerTrafficEngineering \in ({rc0} \X {CONT_TE})
    variables topoChangeEvent = NADIR_NULL, currSetDownSw = {}, prev_dag_id = NADIR_NULL, init = 1,
        nxtDAG = NADIR_NULL, setRemovableIRs = {}, currIR = NADIR_NULL, currIRInDAG = NADIR_NULL,
        nxtDAGVertices = {}, setIRsInDAG = {}, prev_dag = NADIR_NULL, DAGID = NADIR_NULL;
    begin
    ControllerTEProc:
    while TRUE do
        await init = 1 \/ TEEventQueue # <<>>;
        
        ControllerTEEventProcessing:
            while TEEventQueue # <<>> do
                topoChangeEvent := Head(TEEventQueue);
                assert topoChangeEvent.type \in {TOPO_MOD};
                if topoChangeEvent.state = SW_SUSPEND then
                    currSetDownSw := currSetDownSw \cup {topoChangeEvent.sw};
                else
                    currSetDownSw := currSetDownSw \ {topoChangeEvent.sw};
                end if; 
                TEEventQueue := Tail(TEEventQueue);
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
                
                    ControllerTESendDagStaleNotif:
                        DAGEventQueue := Append(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id]);
                
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
                
                prepareDeletionIR(currIR);
                nxtDAG.dag.v := nxtDAG.dag.v \cup {nxtRCIRID};
                setIRsInDAG := getSetIRsForSwitchInDAG(ir2sw[currIR], nxtDAGVertices);

                ControllerTEAddEdge:
                    while setIRsInDAG # {} do
                        currIRInDAG := CHOOSE x \in setIRsInDAG: TRUE;
                        setIRsInDAG := setIRsInDAG \ {currIRInDAG};
                        nxtDAG.dag.e := nxtDAG.dag.e \cup {<<nxtRCIRID, currIRInDAG>>};
                    end while;

                    getNextIRID();
            end while;
            SetScheduledIRs := [x \in SW |-> (SetScheduledIRs[x] \ nxtDAG.dag.v)];
            
        ControllerTESubmitNewDAG:
            DAGState[nxtDAG.id] := DAG_SUBMIT;
            DAGEventQueue := Append(DAGEventQueue, [type |-> DAG_NEW, dag_obj |-> nxtDAG]);
    end while;
    end process
    
    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    variables seqEvent = NADIR_NULL, worker = NADIR_NULL;
    begin
    ControllerBossSeqProc:
    while TRUE do
        await DAGEventQueue # <<>>;

        seqEvent := Head(DAGEventQueue);
        DAGEventQueue := Tail(DAGEventQueue);
        assert seqEvent.type \in {DAG_NEW, DAG_STALE};
        if seqEvent.type = DAG_NEW then
            DAGQueue := Append(DAGQueue, seqEvent.dag_obj);
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
    variables toBeScheduledIRs = {}, nextIR = NADIR_NULL, currDAG = NADIR_NULL, IRSet = {};
    begin
    ControllerWorkerSeqProc:
    while TRUE do
        await DAGQueue # <<>>;
        
        currDAG := Head(DAGQueue);
        seqWorkerIsBusy := TRUE;
        
        ControllerWorkerSeqScheduleDAG:
            while ~allIRsInDAGInstalled(currDAG.dag) /\ ~isDAGStale(currDAG.id) do
                toBeScheduledIRs := getSetIRsCanBeScheduledNext(currDAG.dag);
                await toBeScheduledIRs # {};

                SchedulerMechanism:
                while TRUE do 
                    \* CAN FAIL
                    nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                    \* CAN FAIL
                    rcInternalState[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
                    \* CAN FAIL
                    SetScheduledIRs[ir2sw[nextIR]] := SetScheduledIRs[ir2sw[nextIR]] \cup {nextIR};
                    
                    AddDeleteIRIRDoneSet:      
                        if irTypeMapping[nextIR].type = INSTALL_FLOW then
                            IRDoneSet := IRDoneSet \cup {nextIR};
                        else
                            IRDoneSet := IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
                        end if;

                    ScheduleTheIR: 
                        \* CAN FAIL
                        modifiedEnqueue(nextIR);
                        toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                        \* CAN FAIL
                        rcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL];    
                        
                        if toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then
                            goto ControllerWorkerSeqScheduleDAG;
                        end if;
                end while;                                                
            end while;
            seqWorkerIsBusy := FALSE;
            IRSet := currDAG.dag.v;
            
            AddDeleteDAGIRDoneSet:
                while IRSet # {} /\ allIRsInDAGInstalled(currDAG.dag) do
                    nextIR := CHOOSE x \in IRSet: TRUE;
                    if irTypeMapping[nextIR].type = INSTALL_FLOW then
                        IRDoneSet := IRDoneSet \cup {nextIR};
                    else
                        IRDoneSet := IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
                    end if;
                    IRSet := IRSet \ {nextIR};
                end while; 
                DAGQueue := Tail(DAGQueue);
    end while;
    
    ControllerSeqStateReconciliation:
        if (rcInternalState[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[ir2sw[rcInternalState[self].next]] := 
                        SetScheduledIRs[ir2sw[rcInternalState[self].next]] \ {rcInternalState[self].next};
        end if;
        goto ControllerWorkerSeqProc;
    end process
    
    fair process rcIRMonitor \in ({rc0} \X {CONT_RC_MONITOR})
    variable currIRMon = NADIR_NULL;
    begin
    controllerIRMonitor:
    while TRUE do
        await setIRMonitorShouldSchedule # {};

        currIRMon := CHOOSE x \in setIRMonitorShouldSchedule: TRUE;
        if currIRMon \in IRDoneSet then 
            SetScheduledIRs[ir2sw[currIRMon]] := SetScheduledIRs[ir2sw[currIRMon]] \cup {currIRMon};
            modifiedEnqueue(currIRMon);
        else
            prepareDeletionIR(currIRMon);
        
            SetScheduledIRs[ir2sw[nxtRCIRID]] := SetScheduledIRs[ir2sw[nxtRCIRID]] \cup {nxtRCIRID};
            modifiedEnqueue(nxtRCIRID);
            getNextIRID();
        end if;
    end while
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = NADIR_NULL, rowIndex = NADIR_NULL, rowRemove = NADIR_NULL; 
    begin
    ControllerThread:
    while TRUE do
        await IRQueueNIB # <<>>;
        await canWorkerThreadContinue(self[1], self);
        
        modifiedRead();
        \* CAN FAIL
        ofcInternalState[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent];
        \* CAN FAIL
        if idThreadWorkingOnIR[nextIRToSent] = NADIR_NULL then
            idThreadWorkingOnIR[nextIRToSent] := self[2]
        else
            ControllerThreadWaitForIRUnlock: 
                await idThreadWorkingOnIR[nextIRToSent] = NADIR_NULL;
                goto ControllerThread;    
        end if;
        
        ControllerThreadSendIR:
            if ~isSwitchSuspended(ir2sw[nextIRToSent]) /\ NIBIRStatus[nextIRToSent] = IR_NONE then
                NIBIRStatus[nextIRToSent] := IR_SENT;
                RCNIBEventQueue := Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> nextIRToSent, state |-> IR_SENT]); 
                ControllerThreadForwardIR:
                    \* CAN FAIL
                    controllerSendIR(nextIRToSent);
                    \* CAN FAIL
                    ofcInternalState[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRToSent];
            end if;
        
        ControllerThreadUnlockSemaphore:
            \* CAN FAIL
            if idThreadWorkingOnIR[nextIRToSent] = self[2] then
                idThreadWorkingOnIR[nextIRToSent] := NADIR_NULL;
            end if;

        RemoveFromScheduledIRSet:
            \* CAN FAIL
            ofcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL];
            \* CAN FAIL
            modifiedRemove();
    end while;
    
    ControllerThreadStateReconciliation:
        await IRQueueNIB # <<>>;
        await canWorkerThreadContinue(self[1], self);
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
        await swSeqChangedStatus # <<>>;
        
        monitoringEvent := Head(swSeqChangedStatus);
        if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then                 
            ControllerSuspendSW: 
                \* CAN FAIL
                SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                RCNIBEventQueue := Append(RCNIBEventQueue, [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]);        
                
        elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            ControllerCheckIfThisIsLastEvent:
                \* CAN FAIL
                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    getIRsToBeChecked:
                        \* CAN FAIL
                        setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                        if (setIRsToReset = {}) then 
                            goto ControllerFreeSuspendedSW;
                        end if;
                    
                    ResetAllIRs:
                        while TRUE do
                            \* CAN FAIL
                            resetIR := CHOOSE x \in setIRsToReset: TRUE;
                            setIRsToReset := setIRsToReset \ {resetIR};
                            NIBIRStatus[resetIR] := IR_NONE;
                            RCNIBEventQueue := Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> resetIR, state |-> IR_NONE]);
                            
                            if setIRsToReset = {} then
                                goto ControllerFreeSuspendedSW;
                            end if;
                        end while;
                end if;
            
            ControllerFreeSuspendedSW: 
                \* CAN FAIL
                ofcInternalState[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                \* CAN FAIL
                SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                RCNIBEventQueue := Append(RCNIBEventQueue, [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]);  
        end if;
        
        ControllerEvenHanlderRemoveEventFromQueue:
            \* CAN FAIL
            ofcInternalState[self] := [type |-> NADIR_NULL, next |-> NADIR_NULL]; 
            \* CAN FAIL
            swSeqChangedStatus := Tail(swSeqChangedStatus);
    end while;
    
    ControllerEventHandlerStateReconciliation:
        await swSeqChangedStatus # <<>>;
        if (ofcInternalState[self].type = START_RESET_IR) then
           SwSuspensionStatus[ofcInternalState[self].sw] := SW_SUSPEND;
           RCNIBEventQueue := Append(RCNIBEventQueue, [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]);
        end if;
        goto ControllerEventHandlerProc;
    end process
    
    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_OFC_MONITOR})
    variable msg = NADIR_NULL, irID = NADIR_NULL, removedIR = NADIR_NULL;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        await switch2Controller # <<>>;
        
        msg := Head(switch2Controller);

        assert msg.flow \in TOTAL_FLOW_SET;
        assert msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY};
        
        irID := getIRIDForFlow(msg.flow, msg.type);
        
        assert msg.from = ir2sw[irID];
        
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            ControllerUpdateIRDone:
                \* CAN FAIL
                if NIBIRStatus[irID] = IR_SENT then 
                    NIBIRStatus[irID] := IR_DONE; 
                    RCNIBEventQueue := Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]);
                end if;
                
                if msg.type = DELETED_SUCCESSFULLY then 
                    removedIR := getRemovedIRID(msg.flow);
                    ControllerMonUpdateIRNone:
                        NIBIRStatus[removedIR] := IR_NONE; 
                        RCNIBEventQueue := Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]);
                end if;
        end if;
        
        MonitoringServerRemoveFromQueue:
            \* CAN FAIL
            switch2Controller := Tail(switch2Controller);
    end while
    end process

end algorithm *)

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
    tag: NadirNullable(NadirProcSet)]

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
    status: [installerStatus: ENUM_SET_INSTALLER_STATUS]]
        
MSG_SET_OF_CMD == [
    type: ENUM_SET_OF_CMD, 
    to: SW, 
    flow: Nat]

MSG_SET_OF_ACK == [
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

TypeOK ==  /\ NadirFunctionTypeCheck(Nat, [type: {INSTALL_FLOW, DELETE_FLOW}, flow: Nat], irTypeMapping)
           /\ NadirFunctionTypeCheck(Nat, SW, ir2sw)
           /\ NadirQueueOfMessages(MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE, swSeqChangedStatus)
           /\ NadirFunctionTypeCheck(SW, Seq(MSG_SET_OF_CMD), controller2Switch)
           /\ NadirQueueOfMessages(MSG_SET_OF_ACK, switch2Controller)
           /\ NadirQueueOfMessages(MSG_SET_TE_EVENT, TEEventQueue)
           /\ NadirQueueOfMessages(MSG_SET_DAG_EVENT, DAGEventQueue)
           /\ NadirQueueOfMessages(STRUCT_SET_DAG_OBJECT, DAGQueue)
           /\ NadirFunctionTypeCheck(Nat, ENUM_SET_DAG_STATE, DAGState)
           /\ NadirQueueOfMessages(MSG_SET_TE_EVENT, RCNIBEventQueue)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, ENUM_SET_IR_STATE, RCIRStatus)
           /\ NadirFunctionTypeCheck(SW, ENUM_SET_SW_STATE, RCSwSuspensionStatus)
           /\ nxtRCIRID \in NADIR_INT_ID_SET
           /\ seqWorkerIsBusy \in BOOLEAN 
           /\ IRDoneSet \in SUBSET NADIR_INT_ID_SET
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, NadirNullable(CONTROLLER_THREAD_POOL), idThreadWorkingOnIR)
           /\ NadirFunctionTypeCheck(NadirProcSet, STRUCT_SET_RC_INTERNAL_STATE, rcInternalState)
           /\ NadirFunctionTypeCheck(NadirProcSet, STRUCT_SET_OFC_INTERNAL_STATE, ofcInternalState)
           /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, ENUM_SET_IR_STATE, NIBIRStatus)
           /\ NadirFunctionTypeCheck(SW, ENUM_SET_SW_STATE, SwSuspensionStatus)
           /\ NadirQueueOfMessages(STRUCT_SET_NIB_TAGGED_IR, IRQueueNIB)
           /\ NadirFunctionTypeCheck(SW, SUBSET NADIR_INT_ID_SET, SetScheduledIRs)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_TE_EVENT), event)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_TE_EVENT), topoChangeEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET SW, currSetDownSw)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), prev_dag_id)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), DAGID)
           /\ NadirLocalVariableTypeCheck({0, 1}, init)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_DAG_OBJECT), nxtDAG)
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
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), currIRMon)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), nextIRToSent)
           /\ NadirLocalVariableTypeCheck(NadirNullable(Nat), rowIndex)
           /\ NadirLocalVariableTypeCheck(NadirNullable(Nat), rowRemove)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_KEEPALIVE \cup MSG_SET_TIMEOUT), monitoringEvent)
           /\ NadirLocalVariableTypeCheck(SUBSET NADIR_INT_ID_SET, setIRsToReset)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), resetIR)
           /\ NadirLocalVariableTypeCheck(NadirNullable(MSG_SET_OF_ACK), msg)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), irID)
           /\ NadirLocalVariableTypeCheck(NadirNullable(NADIR_INT_ID_SET), removedIR)

NadirConstantAssumptions == /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, SW, IR2SW)
                            /\ MaxDAGID \in Nat
                            /\ MaxNumIRs \in Nat
                            /\ MaxNumFlows \in Nat
                            /\ TOTAL_IR_SET \in SUBSET NADIR_INT_ID_SET
                            /\ TOTAL_IR_DEL_SET \in SUBSET NADIR_INT_ID_SET
                            /\ TOTAL_DAG_SET \in SUBSET NADIR_INT_ID_SET
                            /\ TOTAL_FLOW_SET \in SUBSET NADIR_INT_ID_SET
                            /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, Nat, IR2FLOW)
                            /\ NadirFunctionTypeCheck(SUBSET SW, STRUCT_SET_RC_DAG, TOPO_DAG_MAPPING)

ASSUME NadirConstantAssumptions

=============================================================================

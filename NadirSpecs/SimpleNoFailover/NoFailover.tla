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
CONSTANTS MaxNumIRs, TOPO_DAG_MAPPING, IR2SW, IR2FLOW, MaxNumFlows, MaxDAGID, DeleteIRIDStart
                 
(*--fair algorithm stateConsistency
    variables
        \* The set of processes. Nadir will generate identifiers for them as needed
        NadirProcSet = 
            ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_RC_MONITOR, NIB_EVENT_HANDLER, CONT_TE}) \cup 
            ({ofc0} \X {CONT_EVENT, CONT_OFC_MONITOR}) \cup
            ({ofc0} \X CONTROLLER_THREAD_POOL),

        \* We need to think more about these two ...
        irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]],
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
        NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE],
        DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        SetScheduledIRs = [y \in SW |-> {}],

        \* Queue of messages from NIB to OFC
        IRQueueNIB = <<>>,

        \* Local RC variables that need persistence
        RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE],
        RCSwSuspensionStatus = [y \in SW |-> SW_RUN],
        nxtRCIRID = DeleteIRIDStart,
        IRDoneSet = {},
        seqWorkerIsBusy = FALSE,

        \* Semaphore for locking IRs to worker pool threads
        idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> NADIR_NULL] @@                                 \* Installation IRs
                              [x \in DeleteIRIDStart..(DeleteIRIDStart + MaxNumIRs) |-> NADIR_NULL]  \* Deletion IRs
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
                                           \/ /\ irID \in (1..MaxNumIRs) \ IRDoneSet
                                              /\ RCIRStatus[irID] = IR_DONE
                                              /\ RCSwSuspensionStatus[IR2SW[irID]] = SW_RUN
                                              /\ ~ existIRInSetScheduledIRs(ir2sw[irID], DELETE_FLOW, irTypeMapping[irID].flow)
                                              /\ ~ existIRDeletionInIRSent(ir2sw[irID], irTypeMapping[irID].flow)
        
        setIRMonitorShouldSchedule == {x \in 1..MaxNumIRs: irMonitorShouldScheduleIR(x)}                                         
                                                    
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
        
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                                     /\ NIBIRStatus[x] \notin {IR_NONE}}

        getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                                \/ /\ irType = DELETED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = DELETE_FLOW
                                                                             /\ irTypeMapping[x].flow = flowID
        
        getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID
        
        isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE                                                     
    end define
    
    macro controllerSendIR(s)
    begin
        assert irTypeMapping[s].type \in {INSTALL_FLOW, DELETE_FLOW};
        assert irTypeMapping[s].flow \in 1..MaxNumFlows;
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
    variables toBeScheduledIRs = {}, nextIR = NADIR_NULL, stepOfFailure = 0, currDAG = NADIR_NULL, IRSet = {};
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
    variables nextIRToSent = NADIR_NULL, rowIndex = NADIR_NULL, rowRemove = NADIR_NULL, stepOfFailure = 0; 
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
    variables monitoringEvent = NADIR_NULL, setIRsToReset = {}, resetIR = NADIR_NULL, stepOfFailure = 0;
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

        assert msg.flow \in 1..MaxNumFlows;
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
\* BEGIN TRANSLATION (chksum(pcal) = "e691a8cf" /\ chksum(tla) = "8b25d7df")
\* Process variable stepOfFailure of process controllerSequencer at line 318 col 59 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 406 col 89 changed to stepOfFailure_c
VARIABLES NadirProcSet, irTypeMapping, ir2sw, swSeqChangedStatus, 
          controller2Switch, switch2Controller, rcInternalState, 
          ofcInternalState, RCNIBEventQueue, TEEventQueue, DAGEventQueue, 
          DAGQueue, NIBIRStatus, DAGState, SwSuspensionStatus, 
          SetScheduledIRs, IRQueueNIB, RCIRStatus, RCSwSuspensionStatus, 
          nxtRCIRID, IRDoneSet, seqWorkerIsBusy, idThreadWorkingOnIR, pc

(* define statement *)
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
                                   \/ /\ irID \in (1..MaxNumIRs) \ IRDoneSet
                                      /\ RCIRStatus[irID] = IR_DONE
                                      /\ RCSwSuspensionStatus[IR2SW[irID]] = SW_RUN
                                      /\ ~ existIRInSetScheduledIRs(ir2sw[irID], DELETE_FLOW, irTypeMapping[irID].flow)
                                      /\ ~ existIRDeletionInIRSent(ir2sw[irID], irTypeMapping[irID].flow)

setIRMonitorShouldSchedule == {x \in 1..MaxNumIRs: irMonitorShouldScheduleIR(x)}

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

getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                             /\ NIBIRStatus[x] \notin {IR_NONE}}

getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                        \/ /\ irType = DELETED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = DELETE_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID

getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                             /\ irTypeMapping[x].flow = flowID

isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE

VARIABLES event, topoChangeEvent, currSetDownSw, prev_dag_id, init, nxtDAG, 
          setRemovableIRs, currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, 
          prev_dag, DAGID, seqEvent, worker, toBeScheduledIRs, nextIR, 
          stepOfFailure_, currDAG, IRSet, currIRMon, nextIRToSent, rowIndex, 
          rowRemove, stepOfFailure_c, monitoringEvent, setIRsToReset, resetIR, 
          stepOfFailure, msg, irID, removedIR

vars == << NadirProcSet, irTypeMapping, ir2sw, swSeqChangedStatus, 
           controller2Switch, switch2Controller, rcInternalState, 
           ofcInternalState, RCNIBEventQueue, TEEventQueue, DAGEventQueue, 
           DAGQueue, NIBIRStatus, DAGState, SwSuspensionStatus, 
           SetScheduledIRs, IRQueueNIB, RCIRStatus, RCSwSuspensionStatus, 
           nxtRCIRID, IRDoneSet, seqWorkerIsBusy, idThreadWorkingOnIR, pc, 
           event, topoChangeEvent, currSetDownSw, prev_dag_id, init, nxtDAG, 
           setRemovableIRs, currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, 
           prev_dag, DAGID, seqEvent, worker, toBeScheduledIRs, nextIR, 
           stepOfFailure_, currDAG, IRSet, currIRMon, nextIRToSent, rowIndex, 
           rowRemove, stepOfFailure_c, monitoringEvent, setIRsToReset, 
           resetIR, stepOfFailure, msg, irID, removedIR >>

ProcSet == (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({rc0} \X {CONT_RC_MONITOR})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_OFC_MONITOR}))

Init == (* Global variables *)
        /\ NadirProcSet = (({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_RC_MONITOR, NIB_EVENT_HANDLER, CONT_TE}) \cup
                           ({ofc0} \X {CONT_EVENT, CONT_OFC_MONITOR}) \cup
                           ({ofc0} \X CONTROLLER_THREAD_POOL))
        /\ irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]]
        /\ ir2sw = IR2SW
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x\in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ rcInternalState = [x \in NadirProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]]
        /\ ofcInternalState = [x \in NadirProcSet |-> [type |-> NADIR_NULL, next |-> NADIR_NULL]]
        /\ RCNIBEventQueue = <<>>
        /\ TEEventQueue = <<>>
        /\ DAGEventQueue = <<>>
        /\ DAGQueue = <<>>
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ IRQueueNIB = <<>>
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ nxtRCIRID = DeleteIRIDStart
        /\ IRDoneSet = {}
        /\ seqWorkerIsBusy = FALSE
        /\ idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> NADIR_NULL] @@
                                 [x \in DeleteIRIDStart..(DeleteIRIDStart + MaxNumIRs) |-> NADIR_NULL]
        (* Process rcNibEventHandler *)
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> NADIR_NULL]
        (* Process controllerTrafficEngineering *)
        /\ topoChangeEvent = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ currSetDownSw = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag_id = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ init = [self \in ({rc0} \X {CONT_TE}) |-> 1]
        /\ nxtDAG = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ setRemovableIRs = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ currIR = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ currIRInDAG = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ nxtDAGVertices = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ setIRsInDAG = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ DAGID = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        (* Process controllerBossSequencer *)
        /\ seqEvent = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        /\ worker = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        (* Process rcIRMonitor *)
        /\ currIRMon = [self \in ({rc0} \X {CONT_RC_MONITOR}) |-> NADIR_NULL]
        (* Process controllerWorkerThreads *)
        /\ nextIRToSent = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ rowIndex = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ rowRemove = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ stepOfFailure_c = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ stepOfFailure = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_OFC_MONITOR}) |-> NADIR_NULL]
        /\ irID = [self \in ({ofc0} \X {CONT_OFC_MONITOR}) |-> NADIR_NULL]
        /\ removedIR = [self \in ({ofc0} \X {CONT_OFC_MONITOR}) |-> NADIR_NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({rc0} \X {CONT_RC_MONITOR}) -> "controllerIRMonitor"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_OFC_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ RCNIBEventQueue # <<>>
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
                                          /\ UNCHANGED << SetScheduledIRs, 
                                                          RCIRStatus >>
                                     ELSE /\ IF (event'[self].type = IR_MOD)
                                                THEN /\ IF RCIRStatus[event'[self].IR] # event'[self].state
                                                           THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![event'[self].IR] = event'[self].state]
                                                                /\ IF event'[self].state \in {IR_SENT, IR_NONE, IR_DONE}
                                                                      THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[event'[self].IR]] = SetScheduledIRs[ir2sw[event'[self].IR]]\{event'[self].IR}]
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED SetScheduledIRs
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << SetScheduledIRs, 
                                                                                RCIRStatus >>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << SetScheduledIRs, 
                                                                     RCIRStatus >>
                                          /\ UNCHANGED << TEEventQueue, 
                                                          RCSwSuspensionStatus >>
                               /\ RCNIBEventQueue' = Tail(RCNIBEventQueue)
                               /\ pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]
                               /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                               ir2sw, swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               rcInternalState, 
                                               ofcInternalState, DAGEventQueue, 
                                               DAGQueue, NIBIRStatus, DAGState, 
                                               SwSuspensionStatus, IRQueueNIB, 
                                               nxtRCIRID, IRDoneSet, 
                                               seqWorkerIsBusy, 
                                               idThreadWorkingOnIR, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, DAGID, 
                                               seqEvent, worker, 
                                               toBeScheduledIRs, nextIR, 
                                               stepOfFailure_, currDAG, IRSet, 
                                               currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ init[self] = 1 \/ TEEventQueue # <<>>
                          /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << NadirProcSet, irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          rcInternalState, ofcInternalState, 
                                          RCNIBEventQueue, TEEventQueue, 
                                          DAGEventQueue, DAGQueue, NIBIRStatus, 
                                          DAGState, SwSuspensionStatus, 
                                          SetScheduledIRs, IRQueueNIB, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, IRDoneSet, 
                                          seqWorkerIsBusy, idThreadWorkingOnIR, 
                                          event, topoChangeEvent, 
                                          currSetDownSw, prev_dag_id, init, 
                                          nxtDAG, setRemovableIRs, currIR, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, DAGID, 
                                          seqEvent, worker, toBeScheduledIRs, 
                                          nextIR, stepOfFailure_, currDAG, 
                                          IRSet, currIRMon, nextIRToSent, 
                                          rowIndex, rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF TEEventQueue # <<>>
                                           THEN /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                                /\ Assert(topoChangeEvent'[self].type \in {TOPO_MOD}, 
                                                          "Failure of assertion at line 234, column 17.")
                                                /\ IF topoChangeEvent'[self].state = SW_SUSPEND
                                                      THEN /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \cup {topoChangeEvent'[self].sw}]
                                                      ELSE /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \ {topoChangeEvent'[self].sw}]
                                                /\ TEEventQueue' = Tail(TEEventQueue)
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                /\ UNCHANGED << TEEventQueue, 
                                                                topoChangeEvent, 
                                                                currSetDownSw >>
                                     /\ UNCHANGED << NadirProcSet, 
                                                     irTypeMapping, ir2sw, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     RCNIBEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     NIBIRStatus, DAGState, 
                                                     SwSuspensionStatus, 
                                                     SetScheduledIRs, 
                                                     IRQueueNIB, RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, IRDoneSet, 
                                                     seqWorkerIsBusy, 
                                                     idThreadWorkingOnIR, 
                                                     event, prev_dag_id, init, 
                                                     nxtDAG, setRemovableIRs, 
                                                     currIR, currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     DAGID, seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
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
                                           /\ UNCHANGED << NadirProcSet, 
                                                           irTypeMapping, 
                                                           ir2sw, 
                                                           swSeqChangedStatus, 
                                                           controller2Switch, 
                                                           switch2Controller, 
                                                           rcInternalState, 
                                                           ofcInternalState, 
                                                           RCNIBEventQueue, 
                                                           TEEventQueue, 
                                                           DAGEventQueue, 
                                                           DAGQueue, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           SetScheduledIRs, 
                                                           IRQueueNIB, 
                                                           RCIRStatus, 
                                                           RCSwSuspensionStatus, 
                                                           nxtRCIRID, 
                                                           IRDoneSet, 
                                                           seqWorkerIsBusy, 
                                                           idThreadWorkingOnIR, 
                                                           event, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           setRemovableIRs, 
                                                           currIR, currIRInDAG, 
                                                           setIRsInDAG, 
                                                           prev_dag, seqEvent, 
                                                           worker, 
                                                           toBeScheduledIRs, 
                                                           nextIR, 
                                                           stepOfFailure_, 
                                                           currDAG, IRSet, 
                                                           currIRMon, 
                                                           nextIRToSent, 
                                                           rowIndex, rowRemove, 
                                                           stepOfFailure_c, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, 
                                                           stepOfFailure, msg, 
                                                           irID, removedIR >>

ControllerTESendDagStaleNotif(self) == /\ pc[self] = "ControllerTESendDagStaleNotif"
                                       /\ DAGEventQueue' = Append(DAGEventQueue, [type |-> DAG_STALE, id |-> prev_dag_id[self]])
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                       /\ UNCHANGED << NadirProcSet, 
                                                       irTypeMapping, ir2sw, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       RCNIBEventQueue, 
                                                       TEEventQueue, DAGQueue, 
                                                       NIBIRStatus, DAGState, 
                                                       SwSuspensionStatus, 
                                                       SetScheduledIRs, 
                                                       IRQueueNIB, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       nxtRCIRID, IRDoneSet, 
                                                       seqWorkerIsBusy, 
                                                       idThreadWorkingOnIR, 
                                                       event, topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       nxtDAG, setRemovableIRs, 
                                                       currIR, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       DAGID, seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, msg, 
                                                       irID, removedIR >>

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ DAGState[prev_dag_id[self]] = DAG_NONE
                                                /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID[self]]
                                                /\ prev_dag' = [prev_dag EXCEPT ![self] = nxtDAG[self].dag]
                                                /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = getSetRemovableIRs(SW \ currSetDownSw[self], nxtDAGVertices[self])]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                /\ UNCHANGED << NadirProcSet, 
                                                                irTypeMapping, 
                                                                ir2sw, 
                                                                swSeqChangedStatus, 
                                                                controller2Switch, 
                                                                switch2Controller, 
                                                                rcInternalState, 
                                                                ofcInternalState, 
                                                                RCNIBEventQueue, 
                                                                TEEventQueue, 
                                                                DAGEventQueue, 
                                                                DAGQueue, 
                                                                NIBIRStatus, 
                                                                DAGState, 
                                                                SwSuspensionStatus, 
                                                                SetScheduledIRs, 
                                                                IRQueueNIB, 
                                                                RCIRStatus, 
                                                                RCSwSuspensionStatus, 
                                                                nxtRCIRID, 
                                                                IRDoneSet, 
                                                                seqWorkerIsBusy, 
                                                                idThreadWorkingOnIR, 
                                                                event, 
                                                                topoChangeEvent, 
                                                                currSetDownSw, 
                                                                init, nxtDAG, 
                                                                currIR, 
                                                                currIRInDAG, 
                                                                nxtDAGVertices, 
                                                                setIRsInDAG, 
                                                                DAGID, 
                                                                seqEvent, 
                                                                worker, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                stepOfFailure_, 
                                                                currDAG, IRSet, 
                                                                currIRMon, 
                                                                nextIRToSent, 
                                                                rowIndex, 
                                                                rowRemove, 
                                                                stepOfFailure_c, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, 
                                                                stepOfFailure, 
                                                                msg, irID, 
                                                                removedIR >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF setRemovableIRs[self] # {}
                                                THEN /\ currIR' = [currIR EXCEPT ![self] = CHOOSE x \in setRemovableIRs[self]: TRUE]
                                                     /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = setRemovableIRs[self] \ {currIR'[self]}]
                                                     /\ RCIRStatus' = RCIRStatus    @@ (nxtRCIRID :> IR_NONE)
                                                     /\ NIBIRStatus' = NIBIRStatus   @@ (nxtRCIRID :> IR_NONE)
                                                     /\ irTypeMapping' = irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIR'[self]]])
                                                     /\ ir2sw' = ir2sw         @@ (nxtRCIRID :> ir2sw[currIR'[self]])
                                                     /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {nxtRCIRID}]
                                                     /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(ir2sw'[currIR'[self]], nxtDAGVertices[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                                     /\ UNCHANGED SetScheduledIRs
                                                ELSE /\ SetScheduledIRs' = [x \in SW |-> (SetScheduledIRs[x] \ nxtDAG[self].dag.v)]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                                     /\ UNCHANGED << irTypeMapping, 
                                                                     ir2sw, 
                                                                     NIBIRStatus, 
                                                                     RCIRStatus, 
                                                                     nxtDAG, 
                                                                     setRemovableIRs, 
                                                                     currIR, 
                                                                     setIRsInDAG >>
                                          /\ UNCHANGED << NadirProcSet, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          RCNIBEventQueue, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGState, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, IRDoneSet, 
                                                          seqWorkerIsBusy, 
                                                          idThreadWorkingOnIR, 
                                                          event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          prev_dag, DAGID, 
                                                          seqEvent, worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR >>

ControllerTEAddEdge(self) == /\ pc[self] = "ControllerTEAddEdge"
                             /\ IF setIRsInDAG[self] # {}
                                   THEN /\ currIRInDAG' = [currIRInDAG EXCEPT ![self] = CHOOSE x \in setIRsInDAG[self]: TRUE]
                                        /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = setIRsInDAG[self] \ {currIRInDAG'[self]}]
                                        /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.e = nxtDAG[self].dag.e \cup {<<nxtRCIRID, currIRInDAG'[self]>>}]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                        /\ UNCHANGED nxtRCIRID
                                   ELSE /\ nxtRCIRID' = nxtRCIRID + 1
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                        /\ UNCHANGED << nxtDAG, currIRInDAG, 
                                                        setIRsInDAG >>
                             /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                             ir2sw, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             rcInternalState, ofcInternalState, 
                                             RCNIBEventQueue, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             NIBIRStatus, DAGState, 
                                             SwSuspensionStatus, 
                                             SetScheduledIRs, IRQueueNIB, 
                                             RCIRStatus, RCSwSuspensionStatus, 
                                             IRDoneSet, seqWorkerIsBusy, 
                                             idThreadWorkingOnIR, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, 
                                             setRemovableIRs, currIR, 
                                             nxtDAGVertices, prev_dag, DAGID, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' = Append(DAGEventQueue, [type |-> DAG_NEW, dag_obj |-> nxtDAG[self]])
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                  /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                  ir2sw, swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  rcInternalState, 
                                                  ofcInternalState, 
                                                  RCNIBEventQueue, 
                                                  TEEventQueue, DAGQueue, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  SetScheduledIRs, IRQueueNIB, 
                                                  RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, IRDoneSet, 
                                                  seqWorkerIsBusy, 
                                                  idThreadWorkingOnIR, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, DAGID, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTESendDagStaleNotif(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTEAddEdge(self)
                                         \/ ControllerTESubmitNewDAG(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ DAGEventQueue # <<>>
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue)]
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ Assert(seqEvent'[self].type \in {DAG_NEW, DAG_STALE}, 
                                         "Failure of assertion at line 302, column 9.")
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
                               /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                               ir2sw, swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               RCNIBEventQueue, TEEventQueue, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               SetScheduledIRs, IRQueueNIB, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               IRDoneSet, seqWorkerIsBusy, 
                                               idThreadWorkingOnIR, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, DAGID, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, currDAG, 
                                               IRSet, currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ seqWorkerIsBusy = FALSE
                                     /\ DAGState' = [DAGState EXCEPT ![seqEvent[self].id] = DAG_NONE]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                     /\ UNCHANGED << NadirProcSet, 
                                                     irTypeMapping, ir2sw, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     RCNIBEventQueue, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     SetScheduledIRs, 
                                                     IRQueueNIB, RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, IRDoneSet, 
                                                     seqWorkerIsBusy, 
                                                     idThreadWorkingOnIR, 
                                                     event, topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     DAGID, seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ DAGQueue # <<>>
                                 /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue)]
                                 /\ seqWorkerIsBusy' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                 /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                 ir2sw, swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 rcInternalState, 
                                                 ofcInternalState, 
                                                 RCNIBEventQueue, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 NIBIRStatus, DAGState, 
                                                 SwSuspensionStatus, 
                                                 SetScheduledIRs, IRQueueNIB, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, IRDoneSet, 
                                                 idThreadWorkingOnIR, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, DAGID, seqEvent, 
                                                 worker, toBeScheduledIRs, 
                                                 nextIR, stepOfFailure_, IRSet, 
                                                 currIRMon, nextIRToSent, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF ~allIRsInDAGInstalled(currDAG[self].dag) /\ ~isDAGStale(currDAG[self].id)
                                              THEN /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(currDAG[self].dag)]
                                                   /\ toBeScheduledIRs'[self] # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                   /\ UNCHANGED << seqWorkerIsBusy, 
                                                                   IRSet >>
                                              ELSE /\ seqWorkerIsBusy' = FALSE
                                                   /\ IRSet' = [IRSet EXCEPT ![self] = currDAG[self].dag.v]
                                                   /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                                   /\ UNCHANGED toBeScheduledIRs
                                        /\ UNCHANGED << NadirProcSet, 
                                                        irTypeMapping, ir2sw, 
                                                        swSeqChangedStatus, 
                                                        controller2Switch, 
                                                        switch2Controller, 
                                                        rcInternalState, 
                                                        ofcInternalState, 
                                                        RCNIBEventQueue, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, NIBIRStatus, 
                                                        DAGState, 
                                                        SwSuspensionStatus, 
                                                        SetScheduledIRs, 
                                                        IRQueueNIB, RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        nxtRCIRID, IRDoneSet, 
                                                        idThreadWorkingOnIR, 
                                                        event, topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        nxtDAG, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        DAGID, seqEvent, 
                                                        worker, nextIR, 
                                                        stepOfFailure_, 
                                                        currDAG, currIRMon, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        irID, removedIR >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                            /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> STATUS_START_SCHEDULING, next |-> nextIR'[self]]]
                            /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[nextIR'[self]]] = SetScheduledIRs[ir2sw[nextIR'[self]]] \cup {nextIR'[self]}]
                            /\ pc' = [pc EXCEPT ![self] = "AddDeleteIRIRDoneSet"]
                            /\ UNCHANGED << NadirProcSet, irTypeMapping, ir2sw, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, 
                                            ofcInternalState, RCNIBEventQueue, 
                                            TEEventQueue, DAGEventQueue, 
                                            DAGQueue, NIBIRStatus, DAGState, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            RCIRStatus, RCSwSuspensionStatus, 
                                            nxtRCIRID, IRDoneSet, 
                                            seqWorkerIsBusy, 
                                            idThreadWorkingOnIR, event, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, DAGID, 
                                            seqEvent, worker, toBeScheduledIRs, 
                                            stepOfFailure_, currDAG, IRSet, 
                                            currIRMon, nextIRToSent, rowIndex, 
                                            rowRemove, stepOfFailure_c, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, msg, irID, 
                                            removedIR >>

AddDeleteIRIRDoneSet(self) == /\ pc[self] = "AddDeleteIRIRDoneSet"
                              /\ IF irTypeMapping[nextIR[self]].type = INSTALL_FLOW
                                    THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR[self]})
                                    ELSE /\ IRDoneSet' = IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR[self]].flow, INSTALLED_SUCCESSFULLY)}
                              /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                              /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                              ir2sw, swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, 
                                              rcInternalState, 
                                              ofcInternalState, 
                                              RCNIBEventQueue, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, 
                                              NIBIRStatus, DAGState, 
                                              SwSuspensionStatus, 
                                              SetScheduledIRs, IRQueueNIB, 
                                              RCIRStatus, RCSwSuspensionStatus, 
                                              nxtRCIRID, seqWorkerIsBusy, 
                                              idThreadWorkingOnIR, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, DAGID, 
                                              seqEvent, worker, 
                                              toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> nextIR[self], tag |-> NADIR_NULL])
                       /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
                       /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                       /\ IF toBeScheduledIRs'[self] = {} \/ isDAGStale(currDAG[self].id)
                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                       /\ UNCHANGED << NadirProcSet, irTypeMapping, ir2sw, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, ofcInternalState, 
                                       RCNIBEventQueue, TEEventQueue, 
                                       DAGEventQueue, DAGQueue, NIBIRStatus, 
                                       DAGState, SwSuspensionStatus, 
                                       SetScheduledIRs, RCIRStatus, 
                                       RCSwSuspensionStatus, nxtRCIRID, 
                                       IRDoneSet, seqWorkerIsBusy, 
                                       idThreadWorkingOnIR, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, nxtDAG, 
                                       setRemovableIRs, currIR, currIRInDAG, 
                                       nxtDAGVertices, setIRsInDAG, prev_dag, 
                                       DAGID, seqEvent, worker, nextIR, 
                                       stepOfFailure_, currDAG, IRSet, 
                                       currIRMon, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, irID, removedIR >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {} /\ allIRsInDAGInstalled(currDAG[self].dag)
                                     THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF irTypeMapping[nextIR'[self]].type = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR'[self]})
                                                ELSE /\ IRDoneSet' = IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR'[self]].flow, INSTALLED_SUCCESSFULLY)}
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                          /\ UNCHANGED DAGQueue
                                     ELSE /\ DAGQueue' = Tail(DAGQueue)
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << IRDoneSet, nextIR, 
                                                          IRSet >>
                               /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                               ir2sw, swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               RCNIBEventQueue, TEEventQueue, 
                                               DAGEventQueue, NIBIRStatus, 
                                               DAGState, SwSuspensionStatus, 
                                               SetScheduledIRs, IRQueueNIB, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               seqWorkerIsBusy, 
                                               idThreadWorkingOnIR, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, DAGID, 
                                               seqEvent, worker, 
                                               toBeScheduledIRs, 
                                               stepOfFailure_, currDAG, 
                                               currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ IF (rcInternalState[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[rcInternalState[self].next]] = SetScheduledIRs[ir2sw[rcInternalState[self].next]] \ {rcInternalState[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << NadirProcSet, 
                                                          irTypeMapping, ir2sw, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          RCNIBEventQueue, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, 
                                                          NIBIRStatus, 
                                                          DAGState, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, IRDoneSet, 
                                                          seqWorkerIsBusy, 
                                                          idThreadWorkingOnIR, 
                                                          event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          nxtDAG, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, DAGID, 
                                                          seqEvent, worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteIRIRDoneSet(self)
                                \/ ScheduleTheIR(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ ControllerSeqStateReconciliation(self)

controllerIRMonitor(self) == /\ pc[self] = "controllerIRMonitor"
                             /\ setIRMonitorShouldSchedule # {}
                             /\ currIRMon' = [currIRMon EXCEPT ![self] = CHOOSE x \in setIRMonitorShouldSchedule: TRUE]
                             /\ IF currIRMon'[self] \in IRDoneSet
                                   THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[currIRMon'[self]]] = SetScheduledIRs[ir2sw[currIRMon'[self]]] \cup {currIRMon'[self]}]
                                        /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> currIRMon'[self], tag |-> NADIR_NULL])
                                        /\ UNCHANGED << irTypeMapping, ir2sw, 
                                                        NIBIRStatus, 
                                                        RCIRStatus, nxtRCIRID >>
                                   ELSE /\ RCIRStatus' = RCIRStatus    @@ (nxtRCIRID :> IR_NONE)
                                        /\ NIBIRStatus' = NIBIRStatus   @@ (nxtRCIRID :> IR_NONE)
                                        /\ irTypeMapping' = irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIRMon'[self]]])
                                        /\ ir2sw' = ir2sw         @@ (nxtRCIRID :> ir2sw[currIRMon'[self]])
                                        /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw'[nxtRCIRID]] = SetScheduledIRs[ir2sw'[nxtRCIRID]] \cup {nxtRCIRID}]
                                        /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> nxtRCIRID, tag |-> NADIR_NULL])
                                        /\ nxtRCIRID' = nxtRCIRID + 1
                             /\ pc' = [pc EXCEPT ![self] = "controllerIRMonitor"]
                             /\ UNCHANGED << NadirProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             rcInternalState, ofcInternalState, 
                                             RCNIBEventQueue, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, DAGState, 
                                             SwSuspensionStatus, 
                                             RCSwSuspensionStatus, IRDoneSet, 
                                             seqWorkerIsBusy, 
                                             idThreadWorkingOnIR, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, DAGID, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, 
                                             removedIR >>

rcIRMonitor(self) == controllerIRMonitor(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ IRQueueNIB # <<>>
                          /\ canWorkerThreadContinue(self[1], self)
                          /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead(self)]
                          /\ nextIRToSent' = [nextIRToSent EXCEPT ![self] = IRQueueNIB[rowIndex'[self]].IR]
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![rowIndex'[self]].tag = self]
                          /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent'[self]]]
                          /\ IF idThreadWorkingOnIR[nextIRToSent'[self]] = NADIR_NULL
                                THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent'[self]] = self[2]]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadWaitForIRUnlock"]
                                     /\ UNCHANGED idThreadWorkingOnIR
                          /\ UNCHANGED << NadirProcSet, irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          rcInternalState, RCNIBEventQueue, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, NIBIRStatus, DAGState, 
                                          SwSuspensionStatus, SetScheduledIRs, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, IRDoneSet, 
                                          seqWorkerIsBusy, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, DAGID, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, rowRemove, 
                                          stepOfFailure_c, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure, msg, irID, removedIR >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ IF ~isSwitchSuspended(ir2sw[nextIRToSent[self]]) /\ NIBIRStatus[nextIRToSent[self]] = IR_NONE
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                           /\ RCNIBEventQueue' = Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> nextIRToSent[self], state |-> IR_SENT])
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                ir2sw, swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                rcInternalState, 
                                                ofcInternalState, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, 
                                                DAGState, SwSuspensionStatus, 
                                                SetScheduledIRs, IRQueueNIB, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, IRDoneSet, 
                                                seqWorkerIsBusy, 
                                                idThreadWorkingOnIR, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, nxtDAG, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, DAGID, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ Assert(irTypeMapping[nextIRToSent[self]].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                             "Failure of assertion at line 149, column 9 of macro called at line 431, column 21.")
                                   /\ Assert(irTypeMapping[nextIRToSent[self]].flow \in 1..MaxNumFlows, 
                                             "Failure of assertion at line 150, column 9 of macro called at line 431, column 21.")
                                   /\ controller2Switch' = [controller2Switch EXCEPT ![ir2sw[nextIRToSent[self]]] = Append(controller2Switch[ir2sw[nextIRToSent[self]]], [type |-> irTypeMapping[nextIRToSent[self]].type,
                                                                                                                                                                          to |-> ir2sw[nextIRToSent[self]],
                                                                                                                                                                          flow |-> irTypeMapping[nextIRToSent[self]].flow])]
                                   /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_SENT_DONE, next |-> nextIRToSent[self]]]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                   /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                   ir2sw, swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   rcInternalState, 
                                                   RCNIBEventQueue, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, NIBIRStatus, 
                                                   DAGState, 
                                                   SwSuspensionStatus, 
                                                   SetScheduledIRs, IRQueueNIB, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, IRDoneSet, 
                                                   seqWorkerIsBusy, 
                                                   idThreadWorkingOnIR, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   DAGID, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
                                         /\ IF idThreadWorkingOnIR[nextIRToSent[self]] = self[2]
                                               THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent[self]] = NADIR_NULL]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED idThreadWorkingOnIR
                                         /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                         /\ UNCHANGED << NadirProcSet, 
                                                         irTypeMapping, ir2sw, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         RCNIBEventQueue, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, NIBIRStatus, 
                                                         DAGState, 
                                                         SwSuspensionStatus, 
                                                         SetScheduledIRs, 
                                                         IRQueueNIB, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         nxtRCIRID, IRDoneSet, 
                                                         seqWorkerIsBusy, 
                                                         event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         DAGID, seqEvent, 
                                                         worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                                  /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self)]
                                  /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                  /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                  ir2sw, swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  rcInternalState, 
                                                  RCNIBEventQueue, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, NIBIRStatus, 
                                                  DAGState, SwSuspensionStatus, 
                                                  SetScheduledIRs, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, IRDoneSet, 
                                                  seqWorkerIsBusy, 
                                                  idThreadWorkingOnIR, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, DAGID, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, rowIndex, 
                                                  stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR >>

ControllerThreadWaitForIRUnlock(self) == /\ pc[self] = "ControllerThreadWaitForIRUnlock"
                                         /\ idThreadWorkingOnIR[nextIRToSent[self]] = NADIR_NULL
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                         /\ UNCHANGED << NadirProcSet, 
                                                         irTypeMapping, ir2sw, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         RCNIBEventQueue, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, NIBIRStatus, 
                                                         DAGState, 
                                                         SwSuspensionStatus, 
                                                         SetScheduledIRs, 
                                                         IRQueueNIB, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         nxtRCIRID, IRDoneSet, 
                                                         seqWorkerIsBusy, 
                                                         idThreadWorkingOnIR, 
                                                         event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         DAGID, seqEvent, 
                                                         worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ IRQueueNIB # <<>>
                                             /\ canWorkerThreadContinue(self[1], self)
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
                                             /\ UNCHANGED << NadirProcSet, 
                                                             irTypeMapping, 
                                                             ir2sw, 
                                                             swSeqChangedStatus, 
                                                             controller2Switch, 
                                                             switch2Controller, 
                                                             rcInternalState, 
                                                             ofcInternalState, 
                                                             RCNIBEventQueue, 
                                                             TEEventQueue, 
                                                             DAGEventQueue, 
                                                             DAGQueue, 
                                                             DAGState, 
                                                             SwSuspensionStatus, 
                                                             SetScheduledIRs, 
                                                             IRQueueNIB, 
                                                             RCIRStatus, 
                                                             RCSwSuspensionStatus, 
                                                             nxtRCIRID, 
                                                             IRDoneSet, 
                                                             seqWorkerIsBusy, 
                                                             event, 
                                                             topoChangeEvent, 
                                                             currSetDownSw, 
                                                             prev_dag_id, init, 
                                                             nxtDAG, 
                                                             setRemovableIRs, 
                                                             currIR, 
                                                             currIRInDAG, 
                                                             nxtDAGVertices, 
                                                             setIRsInDAG, 
                                                             prev_dag, DAGID, 
                                                             seqEvent, worker, 
                                                             toBeScheduledIRs, 
                                                             nextIR, 
                                                             stepOfFailure_, 
                                                             currDAG, IRSet, 
                                                             currIRMon, 
                                                             nextIRToSent, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             stepOfFailure_c, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, 
                                                             stepOfFailure, 
                                                             msg, irID, 
                                                             removedIR >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadWaitForIRUnlock(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ swSeqChangedStatus # <<>>
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << NadirProcSet, 
                                                    irTypeMapping, ir2sw, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    rcInternalState, 
                                                    ofcInternalState, 
                                                    RCNIBEventQueue, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    NIBIRStatus, DAGState, 
                                                    SwSuspensionStatus, 
                                                    SetScheduledIRs, 
                                                    IRQueueNIB, RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    nxtRCIRID, IRDoneSet, 
                                                    seqWorkerIsBusy, 
                                                    idThreadWorkingOnIR, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    DAGID, seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    removedIR >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> NADIR_NULL, next |-> NADIR_NULL]]
                                                   /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << NadirProcSet, 
                                                                   irTypeMapping, 
                                                                   ir2sw, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   rcInternalState, 
                                                                   RCNIBEventQueue, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   NIBIRStatus, 
                                                                   DAGState, 
                                                                   SwSuspensionStatus, 
                                                                   SetScheduledIRs, 
                                                                   IRQueueNIB, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   nxtRCIRID, 
                                                                   IRDoneSet, 
                                                                   seqWorkerIsBusy, 
                                                                   idThreadWorkingOnIR, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, 
                                                                   nxtDAG, 
                                                                   setRemovableIRs, 
                                                                   currIR, 
                                                                   currIRInDAG, 
                                                                   nxtDAGVertices, 
                                                                   setIRsInDAG, 
                                                                   prev_dag, 
                                                                   DAGID, 
                                                                   seqEvent, 
                                                                   worker, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   currIRMon, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
                                                                   msg, irID, 
                                                                   removedIR >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                             /\ RCNIBEventQueue' = Append(RCNIBEventQueue, [type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND])
                             /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                             /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                             ir2sw, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             rcInternalState, ofcInternalState, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, NIBIRStatus, DAGState, 
                                             SetScheduledIRs, IRQueueNIB, 
                                             RCIRStatus, RCSwSuspensionStatus, 
                                             nxtRCIRID, IRDoneSet, 
                                             seqWorkerIsBusy, 
                                             idThreadWorkingOnIR, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, DAGID, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                          /\ UNCHANGED << NadirProcSet, 
                                                          irTypeMapping, ir2sw, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          RCNIBEventQueue, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, 
                                                          NIBIRStatus, 
                                                          DAGState, 
                                                          SwSuspensionStatus, 
                                                          SetScheduledIRs, 
                                                          IRQueueNIB, 
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, IRDoneSet, 
                                                          seqWorkerIsBusy, 
                                                          idThreadWorkingOnIR, 
                                                          event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          nxtDAG, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, DAGID, 
                                                          seqEvent, worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = getIRSetToReset(monitoringEvent[self].swID)]
                           /\ IF (setIRsToReset'[self] = {})
                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           /\ UNCHANGED << NadirProcSet, irTypeMapping, ir2sw, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, rcInternalState, 
                                           ofcInternalState, RCNIBEventQueue, 
                                           TEEventQueue, DAGEventQueue, 
                                           DAGQueue, NIBIRStatus, DAGState, 
                                           SwSuspensionStatus, SetScheduledIRs, 
                                           IRQueueNIB, RCIRStatus, 
                                           RCSwSuspensionStatus, nxtRCIRID, 
                                           IRDoneSet, seqWorkerIsBusy, 
                                           idThreadWorkingOnIR, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, DAGID, 
                                           seqEvent, worker, toBeScheduledIRs, 
                                           nextIR, stepOfFailure_, currDAG, 
                                           IRSet, currIRMon, nextIRToSent, 
                                           rowIndex, rowRemove, 
                                           stepOfFailure_c, monitoringEvent, 
                                           resetIR, stepOfFailure, msg, irID, 
                                           removedIR >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                     /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                     /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]] = IR_NONE]
                     /\ RCNIBEventQueue' = Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> resetIR'[self], state |-> IR_NONE])
                     /\ IF setIRsToReset'[self] = {}
                           THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                     /\ UNCHANGED << NadirProcSet, irTypeMapping, ir2sw, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, rcInternalState, 
                                     ofcInternalState, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, DAGState, 
                                     SwSuspensionStatus, SetScheduledIRs, 
                                     IRQueueNIB, RCIRStatus, 
                                     RCSwSuspensionStatus, nxtRCIRID, 
                                     IRDoneSet, seqWorkerIsBusy, 
                                     idThreadWorkingOnIR, event, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, nxtDAG, 
                                     setRemovableIRs, currIR, currIRInDAG, 
                                     nxtDAGVertices, setIRsInDAG, prev_dag, 
                                     DAGID, seqEvent, worker, toBeScheduledIRs, 
                                     nextIR, stepOfFailure_, currDAG, IRSet, 
                                     currIRMon, nextIRToSent, rowIndex, 
                                     rowRemove, stepOfFailure_c, 
                                     monitoringEvent, stepOfFailure, msg, irID, 
                                     removedIR >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                   /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                   /\ RCNIBEventQueue' = Append(RCNIBEventQueue, [type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_RUN])
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                   ir2sw, swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   rcInternalState, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, NIBIRStatus, 
                                                   DAGState, SetScheduledIRs, 
                                                   IRQueueNIB, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, IRDoneSet, 
                                                   seqWorkerIsBusy, 
                                                   idThreadWorkingOnIR, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   DAGID, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ swSeqChangedStatus # <<>>
                                                   /\ IF (ofcInternalState[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![ofcInternalState[self].sw] = SW_SUSPEND]
                                                              /\ RCNIBEventQueue' = Append(RCNIBEventQueue, [type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND])
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                                              SwSuspensionStatus >>
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << NadirProcSet, 
                                                                   irTypeMapping, 
                                                                   ir2sw, 
                                                                   swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   rcInternalState, 
                                                                   ofcInternalState, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   NIBIRStatus, 
                                                                   DAGState, 
                                                                   SetScheduledIRs, 
                                                                   IRQueueNIB, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   nxtRCIRID, 
                                                                   IRDoneSet, 
                                                                   seqWorkerIsBusy, 
                                                                   idThreadWorkingOnIR, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, 
                                                                   nxtDAG, 
                                                                   setRemovableIRs, 
                                                                   currIR, 
                                                                   currIRInDAG, 
                                                                   nxtDAGVertices, 
                                                                   setIRsInDAG, 
                                                                   prev_dag, 
                                                                   DAGID, 
                                                                   seqEvent, 
                                                                   worker, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   currIRMon, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
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
                                       /\ switch2Controller # <<>>
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].flow \in 1..MaxNumFlows, 
                                                 "Failure of assertion at line 539, column 9.")
                                       /\ Assert(msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                 "Failure of assertion at line 540, column 9.")
                                       /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg'[self].flow, msg'[self].type)]
                                       /\ Assert(msg'[self].from = ir2sw[irID'[self]], 
                                                 "Failure of assertion at line 544, column 9.")
                                       /\ IF msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                       /\ UNCHANGED << NadirProcSet, 
                                                       irTypeMapping, ir2sw, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       RCNIBEventQueue, 
                                                       TEEventQueue, 
                                                       DAGEventQueue, DAGQueue, 
                                                       NIBIRStatus, DAGState, 
                                                       SwSuspensionStatus, 
                                                       SetScheduledIRs, 
                                                       IRQueueNIB, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       nxtRCIRID, IRDoneSet, 
                                                       seqWorkerIsBusy, 
                                                       idThreadWorkingOnIR, 
                                                       event, topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       nxtDAG, setRemovableIRs, 
                                                       currIR, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       DAGID, seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, 
                                                       removedIR >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ switch2Controller' = Tail(switch2Controller)
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                         /\ UNCHANGED << NadirProcSet, 
                                                         irTypeMapping, ir2sw, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         RCNIBEventQueue, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, NIBIRStatus, 
                                                         DAGState, 
                                                         SwSuspensionStatus, 
                                                         SetScheduledIRs, 
                                                         IRQueueNIB, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         nxtRCIRID, IRDoneSet, 
                                                         seqWorkerIsBusy, 
                                                         idThreadWorkingOnIR, 
                                                         event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         DAGID, seqEvent, 
                                                         worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR >>

ControllerUpdateIRDone(self) == /\ pc[self] = "ControllerUpdateIRDone"
                                /\ IF NIBIRStatus[irID[self]] = IR_SENT
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID[self]] = IR_DONE]
                                           /\ RCNIBEventQueue' = Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> irID[self], state |-> IR_DONE])
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                /\ IF msg[self].type = DELETED_SUCCESSFULLY
                                      THEN /\ removedIR' = [removedIR EXCEPT ![self] = getRemovedIRID(msg[self].flow)]
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerMonUpdateIRNone"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                           /\ UNCHANGED removedIR
                                /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                ir2sw, swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                rcInternalState, 
                                                ofcInternalState, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, 
                                                DAGState, SwSuspensionStatus, 
                                                SetScheduledIRs, IRQueueNIB, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, IRDoneSet, 
                                                seqWorkerIsBusy, 
                                                idThreadWorkingOnIR, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, nxtDAG, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, DAGID, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID >>

ControllerMonUpdateIRNone(self) == /\ pc[self] = "ControllerMonUpdateIRNone"
                                   /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![removedIR[self]] = IR_NONE]
                                   /\ RCNIBEventQueue' = Append(RCNIBEventQueue, [type |-> IR_MOD, IR |-> removedIR[self], state |-> IR_NONE])
                                   /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   /\ UNCHANGED << NadirProcSet, irTypeMapping, 
                                                   ir2sw, swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   rcInternalState, 
                                                   ofcInternalState, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGState, 
                                                   SwSuspensionStatus, 
                                                   SetScheduledIRs, IRQueueNIB, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, IRDoneSet, 
                                                   seqWorkerIsBusy, 
                                                   idThreadWorkingOnIR, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   DAGID, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerUpdateIRDone(self)
                                       \/ ControllerMonUpdateIRNone(self)

Next == (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_RC_MONITOR}): rcIRMonitor(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0} \X {CONT_OFC_MONITOR}): controllerMonitoringServer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_RC_MONITOR}) : WF_vars(rcIRMonitor(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_OFC_MONITOR}) : WF_vars(controllerMonitoringServer(self))

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
                            /\ DeleteIRIDStart \in Nat
                            /\ MaxNumIRs \in Nat
                            /\ MaxNumFlows \in Nat
                            /\ NadirFunctionTypeCheck(NADIR_INT_ID_SET, Nat, IR2FLOW)
                            /\ NadirFunctionTypeCheck(SUBSET SW, STRUCT_SET_RC_DAG, TOPO_DAG_MAPPING)

ASSUME NadirConstantAssumptions

=============================================================================

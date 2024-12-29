------------------- MODULE zenith_nr_with_monitor -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR, CONT_EVENT, 
          WATCH_DOG, NIB_EVENT_HANDLER, CONT_TE
CONSTANTS TOPO_DAG_MAPPING, IR2SW, IR2FLOW

ASSUME MaxNumIRs >= Cardinality({TOPO_DAG_MAPPING[i]: i \in DOMAIN TOPO_DAG_MAPPING})
ASSUME {"ofc0", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE
ASSUME \A x \in DOMAIN TOPO_DAG_MAPPING: /\ "v" \in DOMAIN TOPO_DAG_MAPPING[x]
                                         /\ "e" \in DOMAIN TOPO_DAG_MAPPING[x]
ASSUME \A x \in 1..MaxNumIRs: x \in DOMAIN IR2SW
ASSUME \A x \in 1..MaxNumIRs: /\ x \in DOMAIN IR2FLOW
                              /\ IR2FLOW[x] \in 1..MaxNumFlows

(*--fair algorithm stateConsistency
    variables 
        switchLock = <<NO_LOCK, NO_LOCK>>,
        controllerLock = <<NO_LOCK, NO_LOCK>>, 
        
        swSeqChangedStatus = <<>>,
        controller2Switch = [x\in SW |-> <<>>],
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

        controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0],
        controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed],

        DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
        RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE],
        RCSwSuspensionStatus = [y \in SW |-> SW_RUN],
        NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE],
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        rcInternalState = [x \in RCProcSet |-> [type |-> NO_STATUS]],
        ofcInternalState = [x \in OFCProcSet |-> [type |-> NO_STATUS]],
        SetScheduledIRs = [y \in SW |-> {}],
        
        irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]],
        ir2sw = IR2SW,
        idWorkerWorkingOnDAG = [x \in 1..MaxDAGID |-> DAG_UNLOCK],
        IRDoneSet = {},
        idThreadWorkingOnIR = [x \in 1..2*MaxNumIRs |-> IR_UNLOCK],
        workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]:
            ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z]
    define
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
        getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}                        
        moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
        getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                                     [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0
        NoEntryTaggedWith(threadID) == ~\E x \in rangeSeq(IRQueueNIB): x.tag = threadID 
        FirstUntaggedEntry(threadID, num) == ~\E x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = NO_TAG
                                                                          /\ x < num
        getFirstIRIndexToRead(threadID) == CHOOSE x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                                           \/ /\ NoEntryTaggedWith(threadID)
                                                                              /\ FirstUntaggedEntry(threadID, x)
                                                                              /\ IRQueueNIB[x].tag = NO_TAG
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
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>)
                                                              /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}        
        canWorkerThreadContinue(threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                             \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NO_TAG 
                                                /\ NoEntryTaggedWith(threadID)
                                                /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(threadID[1])})
        setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
                                                                                                                        /\ y.tag = <<CID, x>>
                                                                                         /\ pc[<<CID, x>>] = "ControllerThread"}
        threadWithLowerIDGetsTheLock(threadID, nIR, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: 
                                                                                                        z \in setThreadsAttemptingForLock(threadID[1], nIR, IRQueue)})
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
        getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                                \/ /\ irType = DELETED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = DELETE_FLOW
                                                                             /\ irTypeMapping[x].flow = flowID
        getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID
        returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                                   /\ controllerSubmoduleFailStat[x] = Failed}
    
        isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE
        getDeletionIRID(ofWhat) == ofWhat + MaxNumIRs

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

    macro controllerSendIR(s)
    begin
        assert irTypeMapping[s].type \in {INSTALL_FLOW, DELETE_FLOW};
        assert irTypeMapping[s].flow \in 1..MaxNumFlows;
        controller2Switch[ir2sw[s]] := Append(
            controller2Switch[ir2sw[s]], 
            [
                type |-> irTypeMapping[s].type,
                to |-> ir2sw[s],
                flow |-> irTypeMapping[s].flow,
                from |-> self[1]
            ]
        );
        if whichSwitchModel(ir2sw[s]) = SW_COMPLEX_MODEL then 
            switchLock := <<NIC_ASIC_IN, ir2sw[s]>>;
        else
            switchLock := <<SW_SIMPLE_ID, ir2sw[s]>>;
        end if;
    end macro;

    macro modifiedEnqueue(nextIR)
    begin
        IRQueueNIB := Append(IRQueueNIB, [IR |-> nextIR, tag |-> NO_TAG]);
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

    macro prepareDeletionIR(forWhat, DID)
    begin
        if (DID \notin DOMAIN RCIRStatus) then
            RCIRStatus    := RCIRStatus    @@ (DID :> IR_NONE);
            NIBIRStatus   := NIBIRStatus   @@ (DID :> IR_NONE);
            FirstInstall  := FirstInstall  @@ (DID :> 0);
            irTypeMapping := irTypeMapping @@ (DID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[forWhat]]);
            ir2sw         := ir2sw         @@ (DID :> ir2sw[forWhat]);
        else
            RCIRStatus[DID] := IR_NONE;
            NIBIRStatus[DID] := IR_NONE;
        end if;
    end macro;

    macro getNextDAGID()
    begin
        if DAGID = 0 then
            DAGID := 1
        else
            DAGID := (DAGID % MaxDAGID) + 1
        end if;
    end macro;

    fair process rcNibEventHandler \in ({rc0} \X {NIB_EVENT_HANDLER})
    variables event = [type |-> 0];
    begin
    RCSNIBEventHndlerProc:
    while TRUE do
        await moduleIsUp(self);
        await RCNIBEventQueue # <<>>;
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
    variables topoChangeEvent = [type |-> 0], currSetDownSw = {}, prev_dag_id = 0, init = 1,
        DAGID = 0, nxtDAG = [type |-> 0], deleterID = 0, setRemovableIRs = {}, 
        currIR = 0, currIRInDAG = 0, nxtDAGVertices = {}, setIRsInDAG = {}, 
        prev_dag = [e |-> {}, v |-> {}];
    begin
    ControllerTEProc:
    while TRUE do
        await moduleIsUp(self);
        await init = 1 \/ TEEventQueue # <<>>;
        controllerAcquireLock();
        
        ControllerTEEventProcessing:
            while TEEventQueue # <<>> do 
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
                deleterID := getDeletionIRID(currIR);
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
    variables seqEvent = [type |-> 0], worker = 0;
    begin
    ControllerBossSeqProc:
    while TRUE do
        await moduleIsUp(self);
        await DAGEventQueue # <<>>;
    
        controllerWaitForLockFree();
        seqEvent := Head(DAGEventQueue);
        DAGEventQueue := Tail(DAGEventQueue);
        assert seqEvent.type \in {DAG_NEW, DAG_STALE};
        if seqEvent.type = DAG_NEW then
            DAGQueue := Append(DAGQueue, seqEvent.dag_obj);
        else
            worker := idWorkerWorkingOnDAG[seqEvent.id];
            if worker # DAG_UNLOCK then
                WaitForRCSeqWorkerTerminate:
                    controllerWaitForLockFree();
                    await idWorkerWorkingOnDAG[seqEvent.id] = DAG_UNLOCK;
                    DAGState[seqEvent.id] := DAG_NONE;
            else
                DAGState[seqEvent.id] := DAG_NONE;
            end if;
        end if;
    end while;
    end process

    fair process controllerSequencer \in ({rc0} \X {CONT_WORKER_SEQ})
    variables toBeScheduledIRs = {}, nextIR = 0, stepOfFailure = 0, currDAG = [dag |-> 0], IRSet = {};
    begin
    ControllerWorkerSeqProc:
    while TRUE do
        await moduleIsUp(self);
        await DAGQueue # <<>>;
        controllerWaitForLockFree();
        currDAG := Head(DAGQueue);
        idWorkerWorkingOnDAG[currDAG.id] := self[2];
        
        ControllerWorkerSeqScheduleDAG:
            while ~allIRsInDAGInstalled(currDAG.dag) /\ ~isDAGStale(currDAG.id) do
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
                        controllerWaitForLockFree();
                        if irTypeMapping[nextIR].type = INSTALL_FLOW then
                            IRDoneSet := IRDoneSet \cup {nextIR};
                        else
                            IRDoneSet := IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
                        end if;

                    ScheduleTheIR: 
                        controllerWaitForLockFree();
                        whichStepToFail(2);
                        if (stepOfFailure # 1) then
                            modifiedEnqueue(nextIR);
                            toBeScheduledIRs := toBeScheduledIRs\{nextIR};
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
            idWorkerWorkingOnDAG[currDAG.id] := DAG_UNLOCK;
            IRSet := currDAG.dag.v;
            
            AddDeleteDAGIRDoneSet:
                while IRSet # {} /\ allIRsInDAGInstalled(currDAG.dag) do
                    controllerWaitForLockFree();
                    nextIR := CHOOSE x \in IRSet: TRUE;
                    if irTypeMapping[nextIR].type = INSTALL_FLOW then
                        IRDoneSet := IRDoneSet \cup {nextIR};
                    else
                        IRDoneSet := IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
                    end if;
                    IRSet := IRSet \ {nextIR};
                end while; 
                controllerReleaseLock();
                DAGQueue := Tail(DAGQueue);
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

    fair process rcIRMonitor \in ({rc0} \X {CONT_MONITOR})
    variable currIRMon = 0, deleterIDMon = 0;
    begin
    controllerIRMonitor:
    while TRUE do
        await moduleIsUp(self);
        await setIRMonitorShouldSchedule # {};
        controllerWaitForLockFree();
        currIRMon := CHOOSE x \in setIRMonitorShouldSchedule: TRUE;
        if currIRMon \in IRDoneSet then 
            SetScheduledIRs[ir2sw[currIRMon]] := SetScheduledIRs[ir2sw[currIRMon]] \cup {currIRMon};
            modifiedEnqueue(currIRMon);
        else
            deleterIDMon := getDeletionIRID(currIRMon);
            prepareDeletionIR(currIRMon, deleterIDMon);
            SetScheduledIRs[ir2sw[deleterIDMon]] := SetScheduledIRs[ir2sw[deleterIDMon]] \cup {deleterIDMon};
            modifiedEnqueue(deleterIDMon);
        end if;
    end while
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = 0, rowIndex = -1, rowRemove = -1, stepOfFailure = 0; 
    begin
    ControllerThread:
    while TRUE do
        await moduleIsUp(self);
        await IRQueueNIB # <<>>;
        await canWorkerThreadContinue(self);
        controllerWaitForLockFree();

        modifiedRead();
        
        whichStepToFail(2);
        if (stepOfFailure = 1) then
            controllerModuleFails();
            goto ControllerThreadStateReconciliation;
        else
            ofcInternalState[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent];
            if (stepOfFailure = 2) then
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            else    
                if idThreadWorkingOnIR[nextIRToSent] = IR_UNLOCK then
                    await threadWithLowerIDGetsTheLock(self, nextIRToSent, IRQueueNIB); \* For Reducing Space
                    idThreadWorkingOnIR[nextIRToSent] := self[2]
                else
                    ControllerThreadWaitForIRUnlock: 
                        controllerWaitForLockFree();
                        await idThreadWorkingOnIR[nextIRToSent] = IR_UNLOCK;
                        goto ControllerThread;    
                end if;
            end if;
        end if;
        
        ControllerThreadSendIR:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                if ~isSwitchSuspended(ir2sw[nextIRToSent]) /\ NIBIRStatus[nextIRToSent] = IR_NONE then
                    NIBIRStatus[nextIRToSent] := IR_SENT;
                    RCNIBEventQueue := Append(
                        RCNIBEventQueue, 
                        [type |-> IR_MOD, IR |-> nextIRToSent, state |-> IR_SENT]
                    );
                    ControllerThreadForwardIR:
                        controllerWaitForLockFree();
                        whichStepToFail(2);
                        if (stepOfFailure # 1) then
                            controllerSendIR(nextIRToSent);
                            if (stepOfFailure # 2) then
                               ofcInternalState[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRToSent];
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
                    
        ControllerThreadUnlockSemaphore:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                if idThreadWorkingOnIR[nextIRToSent] = self[2] then
                    idThreadWorkingOnIR[nextIRToSent] := IR_UNLOCK;
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
                    modifiedRemove();
                end if;
            end if;
            
            if (stepOfFailure # 0) then
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            end if;
    end while;
    
    ControllerThreadStateReconciliation:
        await moduleIsUp(self);
        await IRQueueNIB # <<>>;
        await canWorkerThreadContinue(self);
        controllerReleaseLock();
        if (ofcInternalState[self].type = STATUS_LOCKING) then
            if (NIBIRStatus[ofcInternalState[self].next] = IR_SENT) then
                    NIBIRStatus[ofcInternalState[self].next] := IR_NONE;
            end if;                 
            if (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2]) then
                idThreadWorkingOnIR[ofcInternalState[self].next] := IR_UNLOCK;
            end if;        
        elsif (ofcInternalState[self].type = STATUS_SENT_DONE) then       
            if (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2]) then
                idThreadWorkingOnIR[ofcInternalState[self].next] := IR_UNLOCK;
            end if;
        end if;
        goto ControllerThread;
    end process

    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, resetIR = 0, stepOfFailure = 0;
    begin
    ControllerEventHandlerProc:
    while TRUE do 
        await moduleIsUp(self);   
        await swSeqChangedStatus # <<>>;
        controllerAcquireLock();

        monitoringEvent := Head(swSeqChangedStatus);
        if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            ControllerSuspendSW: 
                controllerWaitForLockFree();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                    RCNIBEventQueue := Append(
                        RCNIBEventQueue,
                        [
                            type |-> TOPO_MOD, 
                            sw |-> monitoringEvent.swID, 
                            state |-> SW_SUSPEND
                        ]
                    );
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
                
        elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            ControllerCheckIfThisIsLastEvent:
                controllerReleaseLock();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
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
                                    RCNIBEventQueue := Append(
                                        RCNIBEventQueue, 
                                        [
                                            type |-> IR_MOD, 
                                            IR |-> resetIR, 
                                            state |-> IR_NONE
                                        ]
                                    );
                                    if setIRsToReset = {} then
                                        goto ControllerFreeSuspendedSW;
                                    end if;
                                else
                                    goto ControllerEventHandlerStateReconciliation;
                                end if;
                            end while;
                    end if;
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;

            ControllerFreeSuspendedSW: 
                controllerAcquireLock();
                whichStepToFail(2);
                if (stepOfFailure # 1) then
                    ofcInternalState[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                    if (stepOfFailure # 2) then
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
                    swSeqChangedStatus := Tail(swSeqChangedStatus);
                end if;
            end if;
            
            if (stepOfFailure # 0) then
                controllerModuleFails();
                goto ControllerEventHandlerStateReconciliation;
            end if;
    end while;

    ControllerEventHandlerStateReconciliation:
 
         await moduleIsUp(self);   
         await swSeqChangedStatus # <<>>; 
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
    variable msg = [type |-> 0], irID = 0, removedIR = 0;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        await moduleIsUp(self);
        await switch2Controller # <<>>;

        controllerAcquireLock();
        msg := Head(switch2Controller);
        assert msg.flow \in 1..MaxNumFlows;
        assert msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY};
        irID := getIRIDForFlow(msg.flow, msg.type);
        assert msg.from = ir2sw[irID];
        
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            ControllerUpdateIRDone:
                controllerWaitForLockFree(); 
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    FirstInstall[irID] := 1;
                    if NIBIRStatus[irID] = IR_SENT then
                        NIBIRStatus[irID] := IR_DONE; 
                        RCNIBEventQueue := Append(
                            RCNIBEventQueue, 
                            [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                        );
                    end if;
                    
                    if msg.type = DELETED_SUCCESSFULLY then 
                        removedIR := getRemovedIRID(msg.flow);
                        ControllerMonUpdateIRNone:
                            controllerWaitForLockFree(); 
                            controllerModuleFailOrNot();
                            NIBIRStatus[removedIR] := IR_NONE; 
                            RCNIBEventQueue := Append(
                                RCNIBEventQueue, 
                                [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]
                            );
                    end if;
                else
                    goto ControllerMonitorCheckIfMastr;
                end if;
        end if;

        MonitoringServerRemoveFromQueue:
            controllerReleaseLock();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                switch2Controller := Tail(switch2Controller);
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1f8f2c4c79611c3d669c9d57bdd1d35e
\* Process variable stepOfFailure of process controllerSequencer at line 399 col 50 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 514 col 64 changed to stepOfFailure_c
VARIABLES switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
          switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
          IRQueueNIB, RCNIBEventQueue, FirstInstall, RCProcSet, OFCProcSet, 
          ContProcSet, controllerSubmoduleFailNum, 
          controllerSubmoduleFailStat, DAGState, RCIRStatus, 
          RCSwSuspensionStatus, NIBIRStatus, SwSuspensionStatus, 
          rcInternalState, ofcInternalState, SetScheduledIRs, irTypeMapping, 
          ir2sw, idWorkerWorkingOnDAG, IRDoneSet, idThreadWorkingOnIR, 
          workerThreadRanking, pc

(* define statement *)
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]
getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}
moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                             [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0
NoEntryTaggedWith(threadID) == ~\E x \in rangeSeq(IRQueueNIB): x.tag = threadID
FirstUntaggedEntry(threadID, num) == ~\E x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = NO_TAG
                                                                  /\ x < num
getFirstIRIndexToRead(threadID) == CHOOSE x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                                   \/ /\ NoEntryTaggedWith(threadID)
                                                                      /\ FirstUntaggedEntry(threadID, x)
                                                                      /\ IRQueueNIB[x].tag = NO_TAG
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
isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>)
                                                      /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}
canWorkerThreadContinue(threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                     \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NO_TAG
                                        /\ NoEntryTaggedWith(threadID)
                                        /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(threadID[1])})
setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
                                                                                                                /\ y.tag = <<CID, x>>
                                                                                 /\ pc[<<CID, x>>] = "ControllerThread"}
threadWithLowerIDGetsTheLock(threadID, nIR, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]:
                                                                                                z \in setThreadsAttemptingForLock(threadID[1], nIR, IRQueue)})
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
getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                        \/ /\ irType = DELETED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = DELETE_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID
getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                             /\ irTypeMapping[x].flow = flowID
returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                           /\ controllerSubmoduleFailStat[x] = Failed}

isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE
getDeletionIRID(ofWhat) == ofWhat + MaxNumIRs

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

VARIABLES event, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, 
          nxtDAG, deleterID, setRemovableIRs, currIR, currIRInDAG, 
          nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, worker, 
          toBeScheduledIRs, nextIR, stepOfFailure_, currDAG, IRSet, currIRMon, 
          deleterIDMon, nextIRToSent, rowIndex, rowRemove, stepOfFailure_c, 
          monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, irID, 
          removedIR, controllerFailedModules

vars == << switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
           switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
           IRQueueNIB, RCNIBEventQueue, FirstInstall, RCProcSet, OFCProcSet, 
           ContProcSet, controllerSubmoduleFailNum, 
           controllerSubmoduleFailStat, DAGState, RCIRStatus, 
           RCSwSuspensionStatus, NIBIRStatus, SwSuspensionStatus, 
           rcInternalState, ofcInternalState, SetScheduledIRs, irTypeMapping, 
           ir2sw, idWorkerWorkingOnDAG, IRDoneSet, idThreadWorkingOnIR, 
           workerThreadRanking, pc, event, topoChangeEvent, currSetDownSw, 
           prev_dag_id, init, DAGID, nxtDAG, deleterID, setRemovableIRs, 
           currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, 
           seqEvent, worker, toBeScheduledIRs, nextIR, stepOfFailure_, 
           currDAG, IRSet, currIRMon, deleterIDMon, nextIRToSent, rowIndex, 
           rowRemove, stepOfFailure_c, monitoringEvent, setIRsToReset, 
           resetIR, stepOfFailure, msg, irID, removedIR, 
           controllerFailedModules >>

ProcSet == (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({rc0} \X {CONT_MONITOR})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})) \cup (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x\in SW |-> <<>>]
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
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> IR_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ rcInternalState = [x \in RCProcSet |-> [type |-> NO_STATUS]]
        /\ ofcInternalState = [x \in OFCProcSet |-> [type |-> NO_STATUS]]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]]
        /\ ir2sw = IR2SW
        /\ idWorkerWorkingOnDAG = [x \in 1..MaxDAGID |-> DAG_UNLOCK]
        /\ IRDoneSet = {}
        /\ idThreadWorkingOnIR = [x \in 1..2*MaxNumIRs |-> IR_UNLOCK]
        /\ workerThreadRanking = (                  CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]:
                                  ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        (* Process rcNibEventHandler *)
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> [type |-> 0]]
        (* Process controllerTrafficEngineering *)
        /\ topoChangeEvent = [self \in ({rc0} \X {CONT_TE}) |-> [type |-> 0]]
        /\ currSetDownSw = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag_id = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ init = [self \in ({rc0} \X {CONT_TE}) |-> 1]
        /\ DAGID = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ nxtDAG = [self \in ({rc0} \X {CONT_TE}) |-> [type |-> 0]]
        /\ deleterID = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ setRemovableIRs = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ currIR = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ currIRInDAG = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ nxtDAGVertices = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ setIRsInDAG = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag = [self \in ({rc0} \X {CONT_TE}) |-> [e |-> {}, v |-> {}]]
        (* Process controllerBossSequencer *)
        /\ seqEvent = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> [type |-> 0]]
        /\ worker = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> 0]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> [dag |-> 0]]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        (* Process rcIRMonitor *)
        /\ currIRMon = [self \in ({rc0} \X {CONT_MONITOR}) |-> 0]
        /\ deleterIDMon = [self \in ({rc0} \X {CONT_MONITOR}) |-> 0]
        (* Process controllerWorkerThreads *)
        /\ nextIRToSent = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ rowIndex = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ rowRemove = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ stepOfFailure_c = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ stepOfFailure = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [type |-> 0]]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
        /\ removedIR = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
        (* Process watchDog *)
        /\ controllerFailedModules = [self \in ({ofc0, rc0} \X {WATCH_DOG}) |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({rc0} \X {CONT_MONITOR}) -> "controllerIRMonitor"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({ofc0, rc0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ moduleIsUp(self)
                               /\ RCNIBEventQueue # <<>>
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ event' = [event EXCEPT ![self] = Head(RCNIBEventQueue)]
                               /\ Assert(event'[self].type \in {TOPO_MOD, IR_MOD}, 
                                         "Failure of assertion at line 268, column 9.")
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
                                               ContProcSet, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               DAGState, NIBIRStatus, 
                                               SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, irTypeMapping, 
                                               ir2sw, idWorkerWorkingOnDAG, 
                                               IRDoneSet, idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, currDAG, 
                                               IRSet, currIRMon, deleterIDMon, 
                                               nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ moduleIsUp(self)
                          /\ init[self] = 1 \/ TEEventQueue # <<>>
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
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          DAGState, RCIRStatus, 
                                          RCSwSuspensionStatus, NIBIRStatus, 
                                          SwSuspensionStatus, rcInternalState, 
                                          ofcInternalState, SetScheduledIRs, 
                                          irTypeMapping, ir2sw, 
                                          idWorkerWorkingOnDAG, IRDoneSet, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, DAGID, nxtDAG, 
                                          deleterID, setRemovableIRs, currIR, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          worker, toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, deleterIDMon, 
                                          nextIRToSent, rowIndex, rowRemove, 
                                          stepOfFailure_c, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure, msg, irID, removedIR, 
                                          controllerFailedModules >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF TEEventQueue # <<>>
                                           THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                                /\ Assert(topoChangeEvent'[self].type \in {TOPO_MOD}, 
                                                          "Failure of assertion at line 300, column 17.")
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
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     DAGState, RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     SetScheduledIRs, 
                                                     irTypeMapping, ir2sw, 
                                                     idWorkerWorkingOnDAG, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     event, prev_dag_id, init, 
                                                     DAGID, nxtDAG, deleterID, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     deleterIDMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ IF DAGID[self] = 0
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
                                                           controllerSubmoduleFailNum, 
                                                           controllerSubmoduleFailStat, 
                                                           RCIRStatus, 
                                                           RCSwSuspensionStatus, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           rcInternalState, 
                                                           ofcInternalState, 
                                                           SetScheduledIRs, 
                                                           irTypeMapping, 
                                                           ir2sw, 
                                                           idWorkerWorkingOnDAG, 
                                                           IRDoneSet, 
                                                           idThreadWorkingOnIR, 
                                                           workerThreadRanking, 
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
                                                           nextIR, 
                                                           stepOfFailure_, 
                                                           currDAG, IRSet, 
                                                           currIRMon, 
                                                           deleterIDMon, 
                                                           nextIRToSent, 
                                                           rowIndex, rowRemove, 
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
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       DAGState, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       SetScheduledIRs, 
                                                       irTypeMapping, ir2sw, 
                                                       idWorkerWorkingOnDAG, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
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
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, deleterIDMon, 
                                                       nextIRToSent, rowIndex, 
                                                       rowRemove, 
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
                                                                controllerSubmoduleFailNum, 
                                                                controllerSubmoduleFailStat, 
                                                                DAGState, 
                                                                RCIRStatus, 
                                                                RCSwSuspensionStatus, 
                                                                NIBIRStatus, 
                                                                SwSuspensionStatus, 
                                                                rcInternalState, 
                                                                ofcInternalState, 
                                                                SetScheduledIRs, 
                                                                irTypeMapping, 
                                                                ir2sw, 
                                                                idWorkerWorkingOnDAG, 
                                                                IRDoneSet, 
                                                                idThreadWorkingOnIR, 
                                                                workerThreadRanking, 
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
                                                                stepOfFailure_, 
                                                                currDAG, IRSet, 
                                                                currIRMon, 
                                                                deleterIDMon, 
                                                                nextIRToSent, 
                                                                rowIndex, 
                                                                rowRemove, 
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
                                                     /\ deleterID' = [deleterID EXCEPT ![self] = getDeletionIRID(currIR'[self])]
                                                     /\ IF (deleterID'[self] \notin DOMAIN RCIRStatus)
                                                           THEN /\ RCIRStatus' = RCIRStatus    @@ (deleterID'[self] :> IR_NONE)
                                                                /\ NIBIRStatus' = NIBIRStatus   @@ (deleterID'[self] :> IR_NONE)
                                                                /\ FirstInstall' = FirstInstall  @@ (deleterID'[self] :> 0)
                                                                /\ irTypeMapping' = irTypeMapping @@ (deleterID'[self] :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIR'[self]]])
                                                                /\ ir2sw' = ir2sw         @@ (deleterID'[self] :> ir2sw[currIR'[self]])
                                                           ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                                /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![deleterID'[self]] = IR_NONE]
                                                                /\ UNCHANGED << FirstInstall, 
                                                                                irTypeMapping, 
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
                                                                     irTypeMapping, 
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
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          DAGState, 
                                                          RCSwSuspensionStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          idWorkerWorkingOnDAG, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          DAGID, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          prev_dag, seqEvent, 
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          deleterIDMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
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
                             /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, RCNIBEventQueue, 
                                             FirstInstall, RCProcSet, 
                                             OFCProcSet, ContProcSet, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             DAGState, RCIRStatus, 
                                             RCSwSuspensionStatus, NIBIRStatus, 
                                             SwSuspensionStatus, 
                                             rcInternalState, ofcInternalState, 
                                             SetScheduledIRs, irTypeMapping, 
                                             ir2sw, idWorkerWorkingOnDAG, 
                                             IRDoneSet, idThreadWorkingOnIR, 
                                             workerThreadRanking, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, 
                                             deleterID, setRemovableIRs, 
                                             currIR, nxtDAGVertices, prev_dag, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, deleterIDMon, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

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
                                                  controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat, 
                                                  RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  rcInternalState, 
                                                  ofcInternalState, 
                                                  SetScheduledIRs, 
                                                  irTypeMapping, ir2sw, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  deleterID, setRemovableIRs, 
                                                  currIR, currIRInDAG, 
                                                  nxtDAGVertices, setIRsInDAG, 
                                                  prev_dag, seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  deleterIDMon, nextIRToSent, 
                                                  rowIndex, rowRemove, 
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
                               /\ DAGEventQueue # <<>>
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue)]
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ Assert(seqEvent'[self].type \in {DAG_NEW, DAG_STALE}, 
                                         "Failure of assertion at line 381, column 9.")
                               /\ IF seqEvent'[self].type = DAG_NEW
                                     THEN /\ DAGQueue' = Append(DAGQueue, seqEvent'[self].dag_obj)
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                          /\ UNCHANGED << DAGState, worker >>
                                     ELSE /\ worker' = [worker EXCEPT ![self] = idWorkerWorkingOnDAG[seqEvent'[self].id]]
                                          /\ IF worker'[self] # DAG_UNLOCK
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
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, irTypeMapping, 
                                               ir2sw, idWorkerWorkingOnDAG, 
                                               IRDoneSet, idThreadWorkingOnIR, 
                                               workerThreadRanking, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, 
                                               toBeScheduledIRs, nextIR, 
                                               stepOfFailure_, currDAG, IRSet, 
                                               currIRMon, deleterIDMon, 
                                               nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                     /\ idWorkerWorkingOnDAG[seqEvent[self].id] = DAG_UNLOCK
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
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     rcInternalState, 
                                                     ofcInternalState, 
                                                     SetScheduledIRs, 
                                                     irTypeMapping, ir2sw, 
                                                     idWorkerWorkingOnDAG, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
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
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     deleterIDMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
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
                                 /\ DAGQueue # <<>>
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue)]
                                 /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG'[self].id] = self[2]]
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 TEEventQueue, DAGEventQueue, 
                                                 DAGQueue, IRQueueNIB, 
                                                 RCNIBEventQueue, FirstInstall, 
                                                 RCProcSet, OFCProcSet, 
                                                 ContProcSet, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 DAGState, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 rcInternalState, 
                                                 ofcInternalState, 
                                                 SetScheduledIRs, 
                                                 irTypeMapping, ir2sw, 
                                                 IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 deleterID, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, IRSet, 
                                                 currIRMon, deleterIDMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF ~allIRsInDAGInstalled(currDAG[self].dag) /\ ~isDAGStale(currDAG[self].id)
                                              THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(currDAG[self].dag)]
                                                   /\ toBeScheduledIRs'[self] # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                   /\ UNCHANGED << controllerLock, 
                                                                   idWorkerWorkingOnDAG, 
                                                                   IRSet >>
                                              ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = self
                                                   /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG[self].id] = DAG_UNLOCK]
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
                                                        ContProcSet, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        DAGState, RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        rcInternalState, 
                                                        ofcInternalState, 
                                                        SetScheduledIRs, 
                                                        irTypeMapping, ir2sw, 
                                                        IRDoneSet, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
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
                                                        nextIR, stepOfFailure_, 
                                                        currDAG, currIRMon, 
                                                        deleterIDMon, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
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
                                            FirstInstall, RCProcSet, 
                                            OFCProcSet, ContProcSet, DAGState, 
                                            RCIRStatus, RCSwSuspensionStatus, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            ofcInternalState, irTypeMapping, 
                                            ir2sw, idWorkerWorkingOnDAG, 
                                            IRDoneSet, idThreadWorkingOnIR, 
                                            workerThreadRanking, event, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, DAGID, nxtDAG, 
                                            deleterID, setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, currDAG, 
                                            IRSet, currIRMon, deleterIDMon, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, irID, 
                                            removedIR, controllerFailedModules >>

AddDeleteIRIRDoneSet(self) == /\ pc[self] = "AddDeleteIRIRDoneSet"
                              /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                              /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF irTypeMapping[nextIR[self]].type = INSTALL_FLOW
                                    THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR[self]})
                                    ELSE /\ IRDoneSet' = IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR[self]].flow, INSTALLED_SUCCESSFULLY)}
                              /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, 
                                              IRQueueNIB, RCNIBEventQueue, 
                                              FirstInstall, RCProcSet, 
                                              OFCProcSet, ContProcSet, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              DAGState, RCIRStatus, 
                                              RCSwSuspensionStatus, 
                                              NIBIRStatus, SwSuspensionStatus, 
                                              rcInternalState, 
                                              ofcInternalState, 
                                              SetScheduledIRs, irTypeMapping, 
                                              ir2sw, idWorkerWorkingOnDAG, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, DAGID, nxtDAG, 
                                              deleterID, setRemovableIRs, 
                                              currIR, currIRInDAG, 
                                              nxtDAGVertices, setIRsInDAG, 
                                              prev_dag, seqEvent, worker, 
                                              toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, deleterIDMon, 
                                              nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure_c, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, stepOfFailure, msg, 
                                              irID, removedIR, 
                                              controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                             THEN /\ \E num \in 0..2:
                                       stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                             ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                       /\ IF (stepOfFailure_'[self] # 1)
                             THEN /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> nextIR[self], tag |-> NO_TAG])
                                  /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
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
                                       RCNIBEventQueue, FirstInstall, 
                                       RCProcSet, OFCProcSet, ContProcSet, 
                                       DAGState, RCIRStatus, 
                                       RCSwSuspensionStatus, NIBIRStatus, 
                                       SwSuspensionStatus, ofcInternalState, 
                                       SetScheduledIRs, irTypeMapping, ir2sw, 
                                       idWorkerWorkingOnDAG, IRDoneSet, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, DAGID, nxtDAG, 
                                       deleterID, setRemovableIRs, currIR, 
                                       currIRInDAG, nxtDAGVertices, 
                                       setIRsInDAG, prev_dag, seqEvent, worker, 
                                       nextIR, currDAG, IRSet, currIRMon, 
                                       deleterIDMon, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, irID, removedIR, 
                                       controllerFailedModules >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {} /\ allIRsInDAGInstalled(currDAG[self].dag)
                                     THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF irTypeMapping[nextIR'[self]].type = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR'[self]})
                                                ELSE /\ IRDoneSet' = IRDoneSet \ {getIRIDForFlow(irTypeMapping[nextIR'[self]].flow, INSTALLED_SUCCESSFULLY)}
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
                                               ContProcSet, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               DAGState, RCIRStatus, 
                                               RCSwSuspensionStatus, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               rcInternalState, 
                                               ofcInternalState, 
                                               SetScheduledIRs, irTypeMapping, 
                                               ir2sw, idWorkerWorkingOnDAG, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               stepOfFailure_, currDAG, 
                                               currIRMon, deleterIDMon, 
                                               nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure_c, 
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
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          DAGState, RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          irTypeMapping, ir2sw, 
                                                          idWorkerWorkingOnDAG, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
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
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          deleterIDMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
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

controllerIRMonitor(self) == /\ pc[self] = "controllerIRMonitor"
                             /\ moduleIsUp(self)
                             /\ setIRMonitorShouldSchedule # {}
                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ currIRMon' = [currIRMon EXCEPT ![self] = CHOOSE x \in setIRMonitorShouldSchedule: TRUE]
                             /\ IF currIRMon'[self] \in IRDoneSet
                                   THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[currIRMon'[self]]] = SetScheduledIRs[ir2sw[currIRMon'[self]]] \cup {currIRMon'[self]}]
                                        /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> currIRMon'[self], tag |-> NO_TAG])
                                        /\ UNCHANGED << FirstInstall, 
                                                        RCIRStatus, 
                                                        NIBIRStatus, 
                                                        irTypeMapping, ir2sw, 
                                                        deleterIDMon >>
                                   ELSE /\ deleterIDMon' = [deleterIDMon EXCEPT ![self] = getDeletionIRID(currIRMon'[self])]
                                        /\ IF (deleterIDMon'[self] \notin DOMAIN RCIRStatus)
                                              THEN /\ RCIRStatus' = RCIRStatus    @@ (deleterIDMon'[self] :> IR_NONE)
                                                   /\ NIBIRStatus' = NIBIRStatus   @@ (deleterIDMon'[self] :> IR_NONE)
                                                   /\ FirstInstall' = FirstInstall  @@ (deleterIDMon'[self] :> 0)
                                                   /\ irTypeMapping' = irTypeMapping @@ (deleterIDMon'[self] :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIRMon'[self]]])
                                                   /\ ir2sw' = ir2sw         @@ (deleterIDMon'[self] :> ir2sw[currIRMon'[self]])
                                              ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![deleterIDMon'[self]] = IR_NONE]
                                                   /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![deleterIDMon'[self]] = IR_NONE]
                                                   /\ UNCHANGED << FirstInstall, 
                                                                   irTypeMapping, 
                                                                   ir2sw >>
                                        /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw'[deleterIDMon'[self]]] = SetScheduledIRs[ir2sw'[deleterIDMon'[self]]] \cup {deleterIDMon'[self]}]
                                        /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> deleterIDMon'[self], tag |-> NO_TAG])
                             /\ pc' = [pc EXCEPT ![self] = "controllerIRMonitor"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             RCNIBEventQueue, RCProcSet, 
                                             OFCProcSet, ContProcSet, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             DAGState, RCSwSuspensionStatus, 
                                             SwSuspensionStatus, 
                                             rcInternalState, ofcInternalState, 
                                             idWorkerWorkingOnDAG, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, nxtDAG, 
                                             deleterID, setRemovableIRs, 
                                             currIR, currIRInDAG, 
                                             nxtDAGVertices, setIRsInDAG, 
                                             prev_dag, seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

rcIRMonitor(self) == controllerIRMonitor(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ moduleIsUp(self)
                          /\ IRQueueNIB # <<>>
                          /\ canWorkerThreadContinue(self)
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead(self)]
                          /\ nextIRToSent' = [nextIRToSent EXCEPT ![self] = IRQueueNIB[rowIndex'[self]].IR]
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![rowIndex'[self]].tag = self]
                          /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                THEN /\ \E num \in 0..2:
                                          stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                          /\ IF (stepOfFailure_c'[self] = 1)
                                THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                     /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                     /\ UNCHANGED << ofcInternalState, 
                                                     idThreadWorkingOnIR >>
                                ELSE /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent'[self]]]
                                     /\ IF (stepOfFailure_c'[self] = 2)
                                           THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                /\ UNCHANGED idThreadWorkingOnIR
                                           ELSE /\ IF idThreadWorkingOnIR[nextIRToSent'[self]] = IR_UNLOCK
                                                      THEN /\ threadWithLowerIDGetsTheLock(self, nextIRToSent'[self], IRQueueNIB')
                                                           /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent'[self]] = self[2]]
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadWaitForIRUnlock"]
                                                           /\ UNCHANGED idThreadWorkingOnIR
                                                /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                controllerSubmoduleFailStat >>
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, RCNIBEventQueue, 
                                          FirstInstall, RCProcSet, OFCProcSet, 
                                          ContProcSet, DAGState, RCIRStatus, 
                                          RCSwSuspensionStatus, NIBIRStatus, 
                                          SwSuspensionStatus, rcInternalState, 
                                          SetScheduledIRs, irTypeMapping, 
                                          ir2sw, idWorkerWorkingOnDAG, 
                                          IRDoneSet, workerThreadRanking, 
                                          event, topoChangeEvent, 
                                          currSetDownSw, prev_dag_id, init, 
                                          DAGID, nxtDAG, deleterID, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, deleterIDMon, rowRemove, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR, controllerFailedModules >>

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
                                      THEN /\ IF ~isSwitchSuspended(ir2sw[nextIRToSent[self]]) /\ NIBIRStatus[nextIRToSent[self]] = IR_NONE
                                                 THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                                      /\ RCNIBEventQueue' =                    Append(
                                                                                RCNIBEventQueue,
                                                                                [type |-> IR_MOD, IR |-> nextIRToSent[self], state |-> IR_SENT]
                                                                            )
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
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
                                                DAGQueue, IRQueueNIB, 
                                                FirstInstall, RCProcSet, 
                                                OFCProcSet, ContProcSet, 
                                                DAGState, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, irTypeMapping, 
                                                ir2sw, idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
                                                workerThreadRanking, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, deleterIDMon, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
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
                                         THEN /\ Assert(irTypeMapping[nextIRToSent[self]].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                                        "Failure of assertion at line 200, column 9 of macro called at line 561, column 29.")
                                              /\ Assert(irTypeMapping[nextIRToSent[self]].flow \in 1..MaxNumFlows, 
                                                        "Failure of assertion at line 201, column 9 of macro called at line 561, column 29.")
                                              /\ controller2Switch' = [controller2Switch EXCEPT ![ir2sw[nextIRToSent[self]]] =                                Append(
                                                                                                                                   controller2Switch[ir2sw[nextIRToSent[self]]],
                                                                                                                                   [
                                                                                                                                       type |-> irTypeMapping[nextIRToSent[self]].type,
                                                                                                                                       to |-> ir2sw[nextIRToSent[self]],
                                                                                                                                       flow |-> irTypeMapping[nextIRToSent[self]].flow,
                                                                                                                                       from |-> self[1]
                                                                                                                                   ]
                                                                                                                               )]
                                              /\ IF whichSwitchModel(ir2sw[nextIRToSent[self]]) = SW_COMPLEX_MODEL
                                                    THEN /\ switchLock' = <<NIC_ASIC_IN, ir2sw[nextIRToSent[self]]>>
                                                    ELSE /\ switchLock' = <<SW_SIMPLE_ID, ir2sw[nextIRToSent[self]]>>
                                              /\ IF (stepOfFailure_c'[self] # 2)
                                                    THEN /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> STATUS_SENT_DONE, next |-> nextIRToSent[self]]]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED ofcInternalState
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << switchLock, 
                                                              controller2Switch, 
                                                              ofcInternalState >>
                                   /\ IF (stepOfFailure_c'[self] # 0)
                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
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
                                                   SetScheduledIRs, 
                                                   irTypeMapping, ir2sw, 
                                                   idWorkerWorkingOnDAG, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   deleterIDMon, nextIRToSent, 
                                                   rowIndex, rowRemove, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
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
                                               THEN /\ IF idThreadWorkingOnIR[nextIRToSent[self]] = self[2]
                                                          THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent[self]] = IR_UNLOCK]
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED idThreadWorkingOnIR
                                                    /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                    /\ UNCHANGED idThreadWorkingOnIR
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
                                                         irTypeMapping, ir2sw, 
                                                         idWorkerWorkingOnDAG, 
                                                         IRDoneSet, 
                                                         workerThreadRanking, 
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
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         deleterIDMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
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
                                                   THEN /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self)]
                                                        /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << IRQueueNIB, 
                                                                        rowRemove >>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << IRQueueNIB, 
                                                             ofcInternalState, 
                                                             rowRemove >>
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
                                                  FirstInstall, RCProcSet, 
                                                  OFCProcSet, ContProcSet, 
                                                  DAGState, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  rcInternalState, 
                                                  SetScheduledIRs, 
                                                  irTypeMapping, ir2sw, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, DAGID, nxtDAG, 
                                                  deleterID, setRemovableIRs, 
                                                  currIR, currIRInDAG, 
                                                  nxtDAGVertices, setIRsInDAG, 
                                                  prev_dag, seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  deleterIDMon, nextIRToSent, 
                                                  rowIndex, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR, 
                                                  controllerFailedModules >>

ControllerThreadWaitForIRUnlock(self) == /\ pc[self] = "ControllerThreadWaitForIRUnlock"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ idThreadWorkingOnIR[nextIRToSent[self]] = IR_UNLOCK
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
                                                         ContProcSet, 
                                                         controllerSubmoduleFailNum, 
                                                         controllerSubmoduleFailStat, 
                                                         DAGState, RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         SetScheduledIRs, 
                                                         irTypeMapping, ir2sw, 
                                                         idWorkerWorkingOnDAG, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
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
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         deleterIDMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
                                                         controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ moduleIsUp(self)
                                             /\ IRQueueNIB # <<>>
                                             /\ canWorkerThreadContinue(self)
                                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (ofcInternalState[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (NIBIRStatus[ofcInternalState[self].next] = IR_SENT)
                                                              THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![ofcInternalState[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED NIBIRStatus
                                                        /\ IF (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2])
                                                              THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![ofcInternalState[self].next] = IR_UNLOCK]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                   ELSE /\ IF (ofcInternalState[self].type = STATUS_SENT_DONE)
                                                              THEN /\ IF (idThreadWorkingOnIR[ofcInternalState[self].next] = self[2])
                                                                         THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![ofcInternalState[self].next] = IR_UNLOCK]
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
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             DAGState, 
                                                             RCIRStatus, 
                                                             RCSwSuspensionStatus, 
                                                             SwSuspensionStatus, 
                                                             rcInternalState, 
                                                             ofcInternalState, 
                                                             SetScheduledIRs, 
                                                             irTypeMapping, 
                                                             ir2sw, 
                                                             idWorkerWorkingOnDAG, 
                                                             IRDoneSet, 
                                                             workerThreadRanking, 
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
                                                             nextIR, 
                                                             stepOfFailure_, 
                                                             currDAG, IRSet, 
                                                             currIRMon, 
                                                             deleterIDMon, 
                                                             nextIRToSent, 
                                                             rowIndex, 
                                                             rowRemove, 
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
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadWaitForIRUnlock(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ moduleIsUp(self)
                                    /\ swSeqChangedStatus # <<>>
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerLock' = self
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
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
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    DAGState, RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    rcInternalState, 
                                                    ofcInternalState, 
                                                    SetScheduledIRs, 
                                                    irTypeMapping, ir2sw, 
                                                    idWorkerWorkingOnDAG, 
                                                    IRDoneSet, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, DAGID, nxtDAG, 
                                                    deleterID, setRemovableIRs, 
                                                    currIR, currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    deleterIDMon, nextIRToSent, 
                                                    rowIndex, rowRemove, 
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
                                                                   irTypeMapping, 
                                                                   ir2sw, 
                                                                   idWorkerWorkingOnDAG, 
                                                                   IRDoneSet, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
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
                                                                   stepOfFailure_, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   currIRMon, 
                                                                   deleterIDMon, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   removedIR, 
                                                                   controllerFailedModules >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
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
                                        /\ RCNIBEventQueue' =                    Append(
                                                                  RCNIBEventQueue,
                                                                  [
                                                                      type |-> TOPO_MOD,
                                                                      sw |-> monitoringEvent[self].swID,
                                                                      state |-> SW_SUSPEND
                                                                  ]
                                                              )
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED << RCNIBEventQueue, 
                                                        SwSuspensionStatus >>
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, 
                                             IRQueueNIB, FirstInstall, 
                                             RCProcSet, OFCProcSet, 
                                             ContProcSet, DAGState, RCIRStatus, 
                                             RCSwSuspensionStatus, NIBIRStatus, 
                                             rcInternalState, ofcInternalState, 
                                             SetScheduledIRs, irTypeMapping, 
                                             ir2sw, idWorkerWorkingOnDAG, 
                                             IRDoneSet, idThreadWorkingOnIR, 
                                             workerThreadRanking, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, DAGID, nxtDAG, 
                                             deleterID, setRemovableIRs, 
                                             currIR, currIRInDAG, 
                                             nxtDAGVertices, setIRsInDAG, 
                                             prev_dag, seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, deleterIDMon, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, 
                                             removedIR, 
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
                                          /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                                THEN /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                           THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
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
                                                          irTypeMapping, ir2sw, 
                                                          idWorkerWorkingOnDAG, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
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
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          deleterIDMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
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
                                           RCNIBEventQueue, FirstInstall, 
                                           RCProcSet, OFCProcSet, ContProcSet, 
                                           DAGState, RCIRStatus, 
                                           RCSwSuspensionStatus, NIBIRStatus, 
                                           SwSuspensionStatus, rcInternalState, 
                                           ofcInternalState, SetScheduledIRs, 
                                           irTypeMapping, ir2sw, 
                                           idWorkerWorkingOnDAG, IRDoneSet, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, DAGID, nxtDAG, 
                                           deleterID, setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, currDAG, IRSet, 
                                           currIRMon, deleterIDMon, 
                                           nextIRToSent, rowIndex, rowRemove, 
                                           stepOfFailure_c, monitoringEvent, 
                                           resetIR, stepOfFailure, msg, irID, 
                                           removedIR, controllerFailedModules >>

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
                                /\ RCNIBEventQueue' =                    Append(
                                                          RCNIBEventQueue,
                                                          [
                                                              type |-> IR_MOD,
                                                              IR |-> resetIR'[self],
                                                              state |-> IR_NONE
                                                          ]
                                                      )
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
                                     FirstInstall, RCProcSet, OFCProcSet, 
                                     ContProcSet, DAGState, RCIRStatus, 
                                     RCSwSuspensionStatus, SwSuspensionStatus, 
                                     rcInternalState, ofcInternalState, 
                                     SetScheduledIRs, irTypeMapping, ir2sw, 
                                     idWorkerWorkingOnDAG, IRDoneSet, 
                                     idThreadWorkingOnIR, workerThreadRanking, 
                                     event, topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     deleterID, setRemovableIRs, currIR, 
                                     currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                     prev_dag, seqEvent, worker, 
                                     toBeScheduledIRs, nextIR, stepOfFailure_, 
                                     currDAG, IRSet, currIRMon, deleterIDMon, 
                                     nextIRToSent, rowIndex, rowRemove, 
                                     stepOfFailure_c, monitoringEvent, 
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
                                                         /\ RCNIBEventQueue' =                    Append(
                                                                                   RCNIBEventQueue,
                                                                                   [
                                                                                       type |-> TOPO_MOD,
                                                                                       sw |-> monitoringEvent[self].swID,
                                                                                       state |-> SW_RUN
                                                                                   ]
                                                                               )
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
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   NIBIRStatus, 
                                                   rcInternalState, 
                                                   SetScheduledIRs, 
                                                   irTypeMapping, ir2sw, 
                                                   idWorkerWorkingOnDAG, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   deleterIDMon, nextIRToSent, 
                                                   rowIndex, rowRemove, 
                                                   stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID, removedIR, 
                                                   controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus # <<>>
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
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   DAGState, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   NIBIRStatus, 
                                                                   rcInternalState, 
                                                                   ofcInternalState, 
                                                                   SetScheduledIRs, 
                                                                   irTypeMapping, 
                                                                   ir2sw, 
                                                                   idWorkerWorkingOnDAG, 
                                                                   IRDoneSet, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
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
                                                                   stepOfFailure_, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   currIRMon, 
                                                                   deleterIDMon, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
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
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ moduleIsUp(self)
                                       /\ switch2Controller # <<>>
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = self
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].flow \in 1..MaxNumFlows, 
                                                 "Failure of assertion at line 765, column 9.")
                                       /\ Assert(msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                 "Failure of assertion at line 766, column 9.")
                                       /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg'[self].flow, msg'[self].type)]
                                       /\ Assert(msg'[self].from = ir2sw[irID'[self]], 
                                                 "Failure of assertion at line 768, column 9.")
                                       /\ IF msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
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
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       DAGState, RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       SetScheduledIRs, 
                                                       irTypeMapping, ir2sw, 
                                                       idWorkerWorkingOnDAG, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
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
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, deleterIDMon, 
                                                       nextIRToSent, rowIndex, 
                                                       rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, 
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
                                                         irTypeMapping, ir2sw, 
                                                         idWorkerWorkingOnDAG, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
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
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         deleterIDMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
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
                                /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                      THEN /\ FirstInstall' = [FirstInstall EXCEPT ![irID[self]] = 1]
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
                                                 THEN /\ removedIR' = [removedIR EXCEPT ![self] = getRemovedIRID(msg[self].flow)]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerMonUpdateIRNone"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                                      /\ UNCHANGED removedIR
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           FirstInstall, 
                                                           NIBIRStatus, 
                                                           removedIR >>
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
                                                SetScheduledIRs, irTypeMapping, 
                                                ir2sw, idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
                                                workerThreadRanking, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, deleterIDMon, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
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
                                                   SetScheduledIRs, 
                                                   irTypeMapping, ir2sw, 
                                                   idWorkerWorkingOnDAG, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, DAGID, nxtDAG, 
                                                   deleterID, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   deleterIDMon, nextIRToSent, 
                                                   rowIndex, rowRemove, 
                                                   stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerUpdateIRDone(self)
                                       \/ ControllerMonUpdateIRNone(self)

ControllerWatchDogProc(self) == /\ pc[self] = "ControllerWatchDogProc"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerFailedModules' = [controllerFailedModules EXCEPT ![self] = returnControllerFailedModules(self[1])]
                                /\ Cardinality(controllerFailedModules'[self]) > 0
                                /\ \E module \in controllerFailedModules'[self]:
                                     /\ Assert(controllerSubmoduleFailStat[module] = Failed, 
                                               "Failure of assertion at line 820, column 13.")
                                     /\ controllerLock' = module
                                     /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![module] = NotFailed]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerWatchDogProc"]
                                /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, IRQueueNIB, 
                                                RCNIBEventQueue, FirstInstall, 
                                                RCProcSet, OFCProcSet, 
                                                ContProcSet, 
                                                controllerSubmoduleFailNum, 
                                                DAGState, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                NIBIRStatus, 
                                                SwSuspensionStatus, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SetScheduledIRs, irTypeMapping, 
                                                ir2sw, idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
                                                workerThreadRanking, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, DAGID, 
                                                nxtDAG, deleterID, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, deleterIDMon, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR >>

watchDog(self) == ControllerWatchDogProc(self)

Next == (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_MONITOR}): rcIRMonitor(self))
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
        /\ \A self \in ({rc0} \X {CONT_MONITOR}) : WF_vars(rcIRMonitor(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in ({ofc0, rc0} \X {WATCH_DOG}) : WF_vars(watchDog(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-df10ba78ef79126e5c7b036fa2f8f5ed

=============================================================================

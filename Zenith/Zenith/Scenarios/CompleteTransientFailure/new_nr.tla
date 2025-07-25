------------------- MODULE new_nr -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag, NadirTypes, NadirAckQueue

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
        controller2Switch = [x\in SW |-> <<>>],
        switch2Controller = <<>>,
        TEEventQueue = <<>>,
        DAGEventQueue = <<>>,
        DAGQueue = <<>>,
        IRQueueNIB = <<>>,
        RCNIBEventQueue = <<>>,

        FirstInstall = [x \in 1..2*MaxNumIRs |-> 0],

        RCProcSet = ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, NIB_EVENT_HANDLER, CONT_TE, CONT_MONITOR}),
        OFCProcSet = (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup 
                     (({ofc0} \X {CONT_EVENT})) \cup 
                     (({ofc0} \X {CONT_MONITOR})),
        ContProcSet = RCProcSet \cup OFCProcSet,

        DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
        RCSwSuspensionStatus = [y \in SW |-> SW_RUN],
        RCIRStatus = [y \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]],
        NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]],
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        SetScheduledIRs = [y \in SW |-> {}],
        seqWorkerIsBusy = FALSE
    define
        getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN ir + MaxNumIRs
                                                ELSE ir - MaxNumIRs
        getPrimaryOfIR(ir) == IF ir \leq MaxNumIRs THEN ir ELSE ir - MaxNumIRs
        getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
        getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW
                                                  ELSE DELETE_FLOW
        getIRFlow(irID) == IF irID \leq MaxNumIRs THEN irID
                                                  ELSE irID - MaxNumIRs
        getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                             ELSE flowID + MaxNumIRs
        
        getNIBIRState(irID) == IF irID \leq MaxNumIRs THEN NIBIRStatus[irID].primary
                                                      ELSE NIBIRStatus[irID - MaxNumIRs].dual
        getRCIRState(irID) == IF irID \leq MaxNumIRs THEN RCIRStatus[irID].primary
                                                     ELSE RCIRStatus[irID - MaxNumIRs].dual
        
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
        shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                                     \/ monEvent.type = NIC_ASIC_DOWN
                                     \/ /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.installerStatus = INSTALLER_DOWN
        canClearSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                         /\ monEvent.installerStatus = INSTALLER_UP
        canfreeSuspendedSw(monEvent) == /\ monEvent.type = CLEARED_TCAM_SUCCESSFULLY
                                        /\ monEvent.installerStatus = INSTALLER_UP
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ getSwitchForIR(x) = SID
                                                     /\ getNIBIRState(x) # IR_NONE}
    
        isFinished == \A x \in 1..MaxNumIRs: getNIBIRState(x) = IR_DONE
        allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getRCIRState(y) = IR_DONE
                                                      /\ \/ getRCIRState(getDualOfIR(y)) # IR_NONE
                                                         \/ getDualOfIR(y) \in SetScheduledIRs[getSwitchForIR(y)]
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

    \* This operation is illegal in practice ...
    macro NadirFIFOExtend(queue, list)
    begin
        queue := queue \o list
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
        if irObject.IR = 0 then
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
                    flow |-> getIRFlow(irObject.IR), 
                    to |-> irObject.sw, 
                    from |-> self[1]
                ]
            );
        end if;
        if whichSwitchModel(irObject.sw) = SW_COMPLEX_MODEL then 
            switchLock := <<NIC_ASIC_IN, irObject.sw>>;
        else
            switchLock := <<SW_SIMPLE_ID, irObject.sw>>;
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

    macro unscheduleDagIRs(dagIRSet)
    begin
        \* Unschedule ONLY IRs that are not IR_NONE.
        \* Other IRs WILL eventually be sent, and there is nothing that
        \* we can do to prevent that. Thus, unscheduling them will cause
        \* us to forget them.
        SetScheduledIRs := [x \in SW |-> (SetScheduledIRs[x] \ getSetUnschedulableIRs(dagIRSet))];
    end macro;

    macro setNIBIRState(irID, state) begin
        if (irID \leq MaxNumIRs) then
            if state = IR_DONE /\ NIBIRStatus[irID].dual = IR_DONE then
                NIBIRStatus[irID] := [primary |-> IR_DONE, dual |-> IR_NONE]
            else
                NIBIRStatus[irID].primary := state
            end if;
        else
            if state = IR_DONE /\ NIBIRStatus[irID - MaxNumIRs].primary = IR_DONE then
                NIBIRStatus[irID - MaxNumIRs] := [primary |-> IR_NONE, dual |-> IR_DONE]
            else
                NIBIRStatus[irID - MaxNumIRs].dual := state
            end if;
        end if;
    end macro;

    macro setRCIRState(irID, state) begin
        if (irID \leq MaxNumIRs) then
            if state = IR_DONE /\ RCIRStatus[irID].dual = IR_DONE then
                RCIRStatus[irID] := [primary |-> IR_DONE, dual |-> IR_NONE]
            else
                RCIRStatus[irID].primary := state
            end if;
        else
            if state = IR_DONE /\ RCIRStatus[irID - MaxNumIRs].primary = IR_DONE then
                RCIRStatus[irID - MaxNumIRs] := [primary |-> IR_NONE, dual |-> IR_DONE]
            else
                RCIRStatus[irID - MaxNumIRs].dual := state
            end if;
        end if;
    end macro;

    \* setNIBIRState(irID, state) == IF irID \leq MaxNumIRs
    \*                                 THEN IF state = IR_DONE 
    \*                                     THEN NIBIRStatus[irID] = [primary |-> IR_DONE, dual |-> IR_NONE]
    \*                                     ELSE NIBIRStatus[irID].primary = state
    \*                                 ELSE
    \*                                     THEN NIBIRStatus[irID - MaxNumIRs] = [primary |-> IR_NONE, dual |-> IR_DONE]
    \*                                     ELSE NIBIRStatus[irID - MaxNumIRs].dual = state
    \* setRCIRState(irID, state) == IF irID \leq MaxNumIRs
    \*                                 THEN IF state = IR_DONE 
    \*                                     THEN RCIRStatus[irID] = [primary |-> IR_DONE, dual |-> IR_NONE]
    \*                                     ELSE RCIRStatus[irID].primary = state
    \*                                 ELSE IF state = IR_DONE 
    \*                                     THEN RCIRStatus[irID - MaxNumIRs] = [primary |-> IR_NONE, dual |-> IR_DONE]
    \*                                     ELSE RCIRStatus[irID - MaxNumIRs].dual = state

    fair process rcNibEventHandler \in ({rc0} \X {NIB_EVENT_HANDLER})
    variables event = [type |-> 0];
    begin
    RCSNIBEventHndlerProc:
    while TRUE do
        controllerWaitForLockFree();
        NadirFIFOPeek(RCNIBEventQueue, event);
        assert event.type \in {TOPO_MOD, IR_MOD, IR_FAILED};
        if (event.type = TOPO_MOD) then
            if RCSwSuspensionStatus[event.sw] # event.state then    
                RCSwSuspensionStatus[event.sw] := event.state;
                TEEventQueue := Append(TEEventQueue, event);
            end if;
        elsif (event.type = IR_MOD) then
            if getRCIRState(event.IR) # event.state then
                setRCIRState(event.IR, event.state);
                with destination = getSwitchForIR(event.IR) do
                    SetScheduledIRs[destination] := SetScheduledIRs[destination] \ {event.IR};    
                end with;
            end if;
        elsif (event.type = IR_FAILED) then
            \* assert getRCIRState(event.IR) = IR_NONE;
            with destination = getSwitchForIR(event.IR) do
                SetScheduledIRs[destination] := SetScheduledIRs[destination] \ {event.IR};    
            end with;
        end if;
        NadirFIFOPop(RCNIBEventQueue);
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
        controllerAcquireLock();
        if init = 1 then
            goto ControllerTEComputeDagBasedOnTopo;
        else
            NadirFIFOPeek(TEEventQueue, topoChangeEvent);
        end if;
        
        ControllerTEEventProcessing:
            while TEEventQueue # <<>> do 
                controllerWaitForLockFree();
                assert topoChangeEvent.type \in {TOPO_MOD};
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
            \* if prev_dag = nxtDAG.dag then
            \*     goto ControllerTEProc;
            \* else
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
            \* end if;
            
        ControllerTERemoveUnnecessaryIRs:
            while setRemovableIRs # {} do
                controllerAcquireLock();
                currIR := CHOOSE x \in setRemovableIRs: TRUE;
                setRemovableIRs := setRemovableIRs \ {currIR};
                deleterID := getDualOfIR(currIR);
                nxtDAG.dag.v := nxtDAG.dag.v \cup {deleterID};
                setIRsInDAG := getSetIRsForSwitchInDAG(getSwitchForIR(currIR), nxtDAGVertices); 
                
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
            unscheduleDagIRs(nxtDAG.dag.v);
            
        ControllerTESubmitNewDAG:
            controllerWaitForLockFree();
            DAGState[nxtDAG.id] := DAG_SUBMIT;
            NadirFIFOPut(DAGEventQueue, [type |-> DAG_NEW, dag_obj |-> nxtDAG]);
    end while;
    end process

    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    variables seqEvent = [type |-> 0], worker = 0;
    begin
    ControllerBossSeqProc:
    while TRUE do
        await DAGEventQueue # <<>>;
    
        controllerWaitForLockFree();
        NadirFIFOGet(DAGEventQueue, seqEvent);
        assert seqEvent.type \in {DAG_NEW, DAG_STALE};
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
    variables toBeScheduledIRs = {}, nextIR = 0, currDAG = [dag |-> 0], IRSet = {}, IRDoneSet = {};
    begin
    ControllerWorkerSeqProc:
    while TRUE do
        controllerWaitForLockFree();
        NadirFIFOPeek(DAGQueue, currDAG);
        seqWorkerIsBusy := TRUE;
        
        ControllerWorkerSeqScheduleDAG:
            while (~allIRsInDAGInstalled(currDAG.dag) /\ ~isDAGStale(currDAG.id)) \/ (~allIRsInDAGAreStable(currDAG.dag)) do
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

                    \* NOTE: Big atomic step for scalability
                    
                    \* AddDeleteIRIRDoneSet:      
                    \*     controllerWaitForLockFree();
                    \*     if getIRType(nextIR) = INSTALL_FLOW then
                    \*         IRDoneSet := IRDoneSet \cup {nextIR};
                    \*     else
                    \*         IRDoneSet := IRDoneSet \ {getDualOfIR(nextIR)}
                    \*     end if;

                    \* ScheduleTheIR: 
                    \*     controllerWaitForLockFree();
                    \*     NadirAckQueuePut(IRQueueNIB, nextIR);
                    \*     toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                
                    \*     if toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then
                    \*         goto ControllerWorkerSeqScheduleDAG;
                    \*     end if;
                end while;                                                
            end while;

            controllerAcquireLock();
            seqWorkerIsBusy := FALSE;
            IRSet := currDAG.dag.v;
            
            if allIRsInDAGInstalled(currDAG.dag) then
                AddDeleteDAGIRDoneSet:
                while IRSet # {} do
                    controllerWaitForLockFree();
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
                controllerReleaseLock();
                NadirFIFOPop(DAGQueue);
    end while;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRObjectToSend = 0, index = -1;
    begin
    ControllerThread:
    while TRUE do
        controllerWaitForLockFree();
        NadirAckQueueGet(IRQueueNIB, self, index, nextIRObjectToSend);
        
        ControllerThreadSendIR:
            controllerWaitForLockFree();
            if nextIRObjectToSend.IR = 0 then
                if isSwitchSuspended(nextIRObjectToSend.sw) then
                    controllerSendIR(nextIRObjectToSend);
                end if;
                NadirAckQueueAck(IRQueueNIB, self, index);                
            elsif ~isSwitchSuspended(nextIRObjectToSend.sw) /\ getNIBIRState(nextIRObjectToSend.IR) = IR_NONE then
                setNIBIRState(nextIRObjectToSend.IR, IR_SENT);
                RCNIBEventQueue := Append(
                    RCNIBEventQueue, 
                    [type |-> IR_MOD, IR |-> nextIRObjectToSend.IR, state |-> IR_SENT]
                );
                
                \* ControllerThreadForwardIR:
                \*     controllerWaitForLockFree();
                \*     controllerSendIR(nextIRIDToSend);
                
                ControllerThreadForwardAndPopIR:
                    controllerWaitForLockFree();
                    controllerSendIR(nextIRObjectToSend);
                    NadirAckQueueAck(IRQueueNIB, self, index);
            else
                \* Failed to send the IR. MUST let applications know
                RCNIBEventQueue := Append(
                    RCNIBEventQueue, 
                    [type |-> IR_FAILED, IR |-> nextIRObjectToSend.IR, state |-> IR_NONE]
                );
                NadirAckQueueAck(IRQueueNIB, self, index);
            end if;
        
        \* NOTE: Combined send and remove into one step for scalability

        \* RemoveFromScheduledIRSet:
        \*     controllerWaitForLockFree();
        \*     NadirAckQueueAck(IRQueueNIB, self, index);
    end while;
    end process

    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, resetIR = 0;
    begin
    ControllerEventHandlerProc:
    while TRUE do 
        controllerWaitForLockFree();
        NadirFIFOPeek(swSeqChangedStatus, monitoringEvent);

        if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            \* ControllerSuspendSW: 
            \*     controllerWaitForLockFree();
            \*     SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
            \*     NadirFIFOPut(
            \*         RCNIBEventQueue,
            \*         [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]
            \*     );
            ControllerSuspendSWAndPop:
                controllerWaitForLockFree();
                SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]
                );
                NadirFIFOPop(swSeqChangedStatus);
        
        elsif canClearSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            ControllerRequestTCAMClear:
                controllerReleaseLock();
                \* Put a CLEAR request on queue!
                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    NadirAckQueuePut(IRQueueNIB, [IR |-> 0, sw |-> monitoringEvent.swID]);
                end if;
                NadirFIFOPop(swSeqChangedStatus);

        elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            ControllerCheckIfThisIsLastEvent:
                controllerReleaseLock();
                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    getIRsToBeChecked:
                        controllerWaitForLockFree();
                        setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                        if (setIRsToReset = {}) then
                            goto ControllerFreeSuspendedSWAndPop;
                        end if;

                    ResetAllIRs:
                        while TRUE do
                            controllerWaitForLockFree();
                            resetIR := CHOOSE x \in setIRsToReset: TRUE;
                            setIRsToReset := setIRsToReset \ {resetIR};
                            setNIBIRState(resetIR, IR_NONE);
                            NadirFIFOPut(
                                RCNIBEventQueue,
                                [type |-> IR_MOD, IR |-> resetIR, state |-> IR_NONE]
                            );
                            if setIRsToReset = {} then
                                goto ControllerFreeSuspendedSWAndPop;
                            end if;
                        end while;
                end if;

            \* ControllerFreeSuspendedSW: 
            \*     controllerAcquireLock();
            \*     SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
            \*     NadirFIFOPut(
            \*         RCNIBEventQueue,
            \*         [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]
            \*     );
            ControllerFreeSuspendedSWAndPop: 
                controllerWaitForLockFree();
                SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]
                );
                NadirFIFOPop(swSeqChangedStatus);
        else
            \* This happens if a switch came back but immediatelly failed afterwards!
            \* In that case, there is no sense processing the event again.
            NadirFIFOPop(swSeqChangedStatus);
        end if;

        \* NOTE: Combine queue pop with previous steps for scalability
        \* ControllerEvenHanlderRemoveEventFromQueue:
        \*     controllerReleaseLock();
        \*     NadirFIFOPop(swSeqChangedStatus);
    end while;
    end process

    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = [type |-> 0], irID = 0;
    \* variable msg = [type |-> 0], irID = 0, removedIR = 0;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        controllerReleaseLock();
        NadirFIFOPeek(switch2Controller, msg);
        \* assert msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY};
        assert msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, 
                             CLEARED_TCAM_SUCCESSFULLY, NIC_ASIC_DOWN, KEEP_ALIVE};

        \* NOTE: IR deletion combined for scalability ....
        
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            ControllerProcessIRModAndPop:
                controllerWaitForLockFree();
                
                irID := getIRIDForFlow(msg.flow, msg.type);
                assert msg.from = getSwitchForIR(irID);
            
                FirstInstall[irID] := 1;
                setNIBIRState(irID, IR_DONE);
                NadirFIFOPut(
                    RCNIBEventQueue,
                    [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                );
                NadirFIFOPop(switch2Controller);
                \* removedIR := getDualOfIR(irID);

                \* if NIBIRStatus[irID] = IR_SENT /\ (removedIR \in DOMAIN NIBIRStatus /\ NIBIRStatus[removedIR] = IR_DONE) then
                \*     NIBIRStatus[irID] := IR_DONE || NIBIRStatus[removedIR] := IR_NONE;
                \*     NadirFIFOExtend(
                \*         RCNIBEventQueue,
                \*         <<[type |-> IR_MOD, IR |-> irID, state |-> IR_DONE], [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]>>
                \*     );
                \*     NadirFIFOPop(switch2Controller);
                \* elsif NIBIRStatus[irID] # IR_SENT /\ (removedIR \in DOMAIN NIBIRStatus /\ NIBIRStatus[removedIR] = IR_DONE) then
                \*     NIBIRStatus[removedIR] := IR_NONE;
                \*     NadirFIFOPut(
                \*         RCNIBEventQueue,
                \*         [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]
                \*     );
                \*     NadirFIFOPop(switch2Controller);
                \* elsif NIBIRStatus[irID] = IR_SENT /\ (removedIR \notin DOMAIN NIBIRStatus \/ NIBIRStatus[removedIR] # IR_DONE) then
                \*     NIBIRStatus[irID] := IR_DONE;
                \*     NadirFIFOPut(
                \*         RCNIBEventQueue,
                \*         [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                \*     );
                \*     NadirFIFOPop(switch2Controller);
                \* else 
                \*     NadirFIFOPop(switch2Controller);
                \* end if;
            \* ControllerUpdateIRDone:
            \*     controllerWaitForLockFree(); 
            
            \*     FirstInstall[irID] := 1;
            \*     if NIBIRStatus[irID] = IR_SENT then
            \*         NIBIRStatus[irID] := IR_DONE; 
            \*         NadirFIFOPut(
            \*             RCNIBEventQueue,
            \*             [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
            \*         );
            \*     end if;

            \*     removedIR := getDualOfIR(irID);
            \*     if removedIR \in DOMAIN NIBIRStatus then 
            \*         ControllerMonUpdateIRNone:
            \*             controllerWaitForLockFree(); 
            \*             controllerModuleFailOrNot();
            \*             if NIBIRStatus[removedIR] = IR_DONE then
            \*                 NIBIRStatus[removedIR] := IR_NONE; 
            \*                 NadirFIFOPut(
            \*                     RCNIBEventQueue,
            \*                     [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]
            \*                 );
            \*             end if;
            \*     end if;
        elsif msg.type \in {CLEARED_TCAM_SUCCESSFULLY, NIC_ASIC_DOWN, KEEP_ALIVE} then
            ForwardToEH:
                controllerWaitForLockFree();
                NadirFIFOPut(swSeqChangedStatus, msg);
                NadirFIFOPop(switch2Controller);                
        end if;

        \* Note: Queue pop combined with previous steps ....
        \* MonitoringServerRemoveFromQueue:
        \*     controllerReleaseLock();
        \*     NadirFIFOPop(switch2Controller);
    end while
    end process   
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "3b5faccd" /\ chksum(tla) = "c08adc")
VARIABLES switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
          switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
          IRQueueNIB, RCNIBEventQueue, FirstInstall, RCProcSet, OFCProcSet, 
          ContProcSet, DAGState, RCSwSuspensionStatus, RCIRStatus, 
          NIBIRStatus, SwSuspensionStatus, SetScheduledIRs, seqWorkerIsBusy, 
          pc

(* define statement *)
getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN ir + MaxNumIRs
                                        ELSE ir - MaxNumIRs
getPrimaryOfIR(ir) == IF ir \leq MaxNumIRs THEN ir ELSE ir - MaxNumIRs
getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW
                                          ELSE DELETE_FLOW
getIRFlow(irID) == IF irID \leq MaxNumIRs THEN irID
                                          ELSE irID - MaxNumIRs
getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                     ELSE flowID + MaxNumIRs

getNIBIRState(irID) == IF irID \leq MaxNumIRs THEN NIBIRStatus[irID].primary
                                              ELSE NIBIRStatus[irID - MaxNumIRs].dual
getRCIRState(irID) == IF irID \leq MaxNumIRs THEN RCIRStatus[irID].primary
                                             ELSE RCIRStatus[irID - MaxNumIRs].dual

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
shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                             \/ monEvent.type = NIC_ASIC_DOWN
                             \/ /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.installerStatus = INSTALLER_DOWN
canClearSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                 /\ monEvent.installerStatus = INSTALLER_UP
canfreeSuspendedSw(monEvent) == /\ monEvent.type = CLEARED_TCAM_SUCCESSFULLY
                                /\ monEvent.installerStatus = INSTALLER_UP
getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ getSwitchForIR(x) = SID
                                             /\ getNIBIRState(x) # IR_NONE}

isFinished == \A x \in 1..MaxNumIRs: getNIBIRState(x) = IR_DONE
allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getRCIRState(y) = IR_DONE
                                              /\ \/ getRCIRState(getDualOfIR(y)) # IR_NONE
                                                 \/ getDualOfIR(y) \in SetScheduledIRs[getSwitchForIR(y)]

VARIABLES event, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, 
          nxtDAG, deleterID, setRemovableIRs, currIR, currIRInDAG, 
          nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, worker, 
          toBeScheduledIRs, nextIR, currDAG, IRSet, IRDoneSet, 
          nextIRObjectToSend, index, monitoringEvent, setIRsToReset, resetIR, 
          msg, irID

vars == << switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
           switch2Controller, TEEventQueue, DAGEventQueue, DAGQueue, 
           IRQueueNIB, RCNIBEventQueue, FirstInstall, RCProcSet, OFCProcSet, 
           ContProcSet, DAGState, RCSwSuspensionStatus, RCIRStatus, 
           NIBIRStatus, SwSuspensionStatus, SetScheduledIRs, seqWorkerIsBusy, 
           pc, event, topoChangeEvent, currSetDownSw, prev_dag_id, init, 
           DAGID, nxtDAG, deleterID, setRemovableIRs, currIR, currIRInDAG, 
           nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, worker, 
           toBeScheduledIRs, nextIR, currDAG, IRSet, IRDoneSet, 
           nextIRObjectToSend, index, monitoringEvent, setIRsToReset, resetIR, 
           msg, irID >>

ProcSet == (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))

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
        /\ FirstInstall = [x \in 1..2*MaxNumIRs |-> 0]
        /\ RCProcSet = ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, NIB_EVENT_HANDLER, CONT_TE, CONT_MONITOR})
        /\ OFCProcSet = ((({ofc0} \X CONTROLLER_THREAD_POOL)) \cup
                         (({ofc0} \X {CONT_EVENT})) \cup
                         (({ofc0} \X {CONT_MONITOR})))
        /\ ContProcSet = (RCProcSet \cup OFCProcSet)
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ seqWorkerIsBusy = FALSE
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
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> [dag |-> 0]]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ IRDoneSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        (* Process controllerWorkerThreads *)
        /\ nextIRObjectToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [type |-> 0]]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
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
                               /\ Assert(event'[self].type \in {TOPO_MOD, IR_MOD, IR_FAILED}, 
                                         "Failure of assertion at line 280, column 9.")
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
                                                           THEN /\ IF ((event'[self].IR) \leq MaxNumIRs)
                                                                      THEN /\ IF (event'[self].state) = IR_DONE /\ RCIRStatus[(event'[self].IR)].dual = IR_DONE
                                                                                 THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![(event'[self].IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                 ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![(event'[self].IR)].primary = event'[self].state]
                                                                      ELSE /\ IF (event'[self].state) = IR_DONE /\ RCIRStatus[(event'[self].IR) - MaxNumIRs].primary = IR_DONE
                                                                                 THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![(event'[self].IR) - MaxNumIRs] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                 ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![(event'[self].IR) - MaxNumIRs].dual = event'[self].state]
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
                                               IRQueueNIB, FirstInstall, 
                                               RCProcSet, OFCProcSet, 
                                               ContProcSet, DAGState, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               seqWorkerIsBusy, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, currDAG, IRSet, 
                                               IRDoneSet, nextIRObjectToSend, 
                                               index, monitoringEvent, 
                                               setIRsToReset, resetIR, msg, 
                                               irID >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ controllerLock' = self
                          /\ IF init[self] = 1
                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                     /\ UNCHANGED topoChangeEvent
                                ELSE /\ Len(TEEventQueue) > 0
                                     /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue)]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, IRQueueNIB, 
                                          RCNIBEventQueue, FirstInstall, 
                                          RCProcSet, OFCProcSet, ContProcSet, 
                                          DAGState, RCSwSuspensionStatus, 
                                          RCIRStatus, NIBIRStatus, 
                                          SwSuspensionStatus, SetScheduledIRs, 
                                          seqWorkerIsBusy, event, 
                                          currSetDownSw, prev_dag_id, init, 
                                          DAGID, nxtDAG, deleterID, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRSet, IRDoneSet, nextIRObjectToSend, 
                                          index, monitoringEvent, 
                                          setIRsToReset, resetIR, msg, irID >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF TEEventQueue # <<>>
                                           THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ Assert(topoChangeEvent[self].type \in {TOPO_MOD}, 
                                                          "Failure of assertion at line 321, column 17.")
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
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     DAGEventQueue, DAGQueue, 
                                                     IRQueueNIB, 
                                                     RCNIBEventQueue, 
                                                     FirstInstall, RCProcSet, 
                                                     OFCProcSet, ContProcSet, 
                                                     DAGState, 
                                                     RCSwSuspensionStatus, 
                                                     RCIRStatus, NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     SetScheduledIRs, 
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
                                                     nextIRObjectToSend, index, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, irID >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ IF DAGID[self] = 0
                                                 THEN /\ DAGID' = [DAGID EXCEPT ![self] = 1]
                                                 ELSE /\ DAGID' = [DAGID EXCEPT ![self] = (DAGID[self] % MaxDAGID) + 1]
                                           /\ nxtDAG' = [nxtDAG EXCEPT ![self] = [id |-> DAGID'[self], dag |-> TOPO_DAG_MAPPING[currSetDownSw[self]]]]
                                           /\ nxtDAGVertices' = [nxtDAGVertices EXCEPT ![self] = nxtDAG'[self].dag.v]
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
                                                           RCSwSuspensionStatus, 
                                                           RCIRStatus, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
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
                                                           worker, 
                                                           toBeScheduledIRs, 
                                                           nextIR, currDAG, 
                                                           IRSet, IRDoneSet, 
                                                           nextIRObjectToSend, 
                                                           index, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, msg, irID >>

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
                                                       FirstInstall, RCProcSet, 
                                                       OFCProcSet, ContProcSet, 
                                                       DAGState, 
                                                       RCSwSuspensionStatus, 
                                                       RCIRStatus, NIBIRStatus, 
                                                       SwSuspensionStatus, 
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
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, IRSet, 
                                                       IRDoneSet, 
                                                       nextIRObjectToSend, 
                                                       index, monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       msg, irID >>

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
                                                                RCSwSuspensionStatus, 
                                                                RCIRStatus, 
                                                                NIBIRStatus, 
                                                                SwSuspensionStatus, 
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
                                                                worker, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                currDAG, IRSet, 
                                                                IRDoneSet, 
                                                                nextIRObjectToSend, 
                                                                index, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, msg, 
                                                                irID >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF setRemovableIRs[self] # {}
                                                THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = self
                                                     /\ currIR' = [currIR EXCEPT ![self] = CHOOSE x \in setRemovableIRs[self]: TRUE]
                                                     /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = setRemovableIRs[self] \ {currIR'[self]}]
                                                     /\ deleterID' = [deleterID EXCEPT ![self] = getDualOfIR(currIR'[self])]
                                                     /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {deleterID'[self]}]
                                                     /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(getSwitchForIR(currIR'[self]), nxtDAGVertices[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                                     /\ UNCHANGED SetScheduledIRs
                                                ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                     /\ SetScheduledIRs' = [x \in SW |-> (SetScheduledIRs[x] \ getSetUnschedulableIRs((nxtDAG[self].dag.v)))]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                                     /\ UNCHANGED << nxtDAG, 
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
                                                          FirstInstall, 
                                                          RCProcSet, 
                                                          OFCProcSet, 
                                                          ContProcSet, 
                                                          DAGState, 
                                                          RCSwSuspensionStatus, 
                                                          RCIRStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
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
                                                          nextIRObjectToSend, 
                                                          index, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID >>

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
                                             RCSwSuspensionStatus, RCIRStatus, 
                                             NIBIRStatus, SwSuspensionStatus, 
                                             SetScheduledIRs, seqWorkerIsBusy, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             DAGID, deleterID, setRemovableIRs, 
                                             currIR, nxtDAGVertices, prev_dag, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, currDAG, 
                                             IRSet, IRDoneSet, 
                                             nextIRObjectToSend, index, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, irID >>

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
                                                  FirstInstall, RCProcSet, 
                                                  OFCProcSet, ContProcSet, 
                                                  RCSwSuspensionStatus, 
                                                  RCIRStatus, NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  SetScheduledIRs, 
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
                                                  nextIRObjectToSend, index, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, msg, 
                                                  irID >>

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
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ Len(DAGEventQueue) > 0
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue)]
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ Assert(seqEvent'[self].type \in {DAG_NEW, DAG_STALE}, 
                                         "Failure of assertion at line 396, column 9.")
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
                                               FirstInstall, RCProcSet, 
                                               OFCProcSet, ContProcSet, 
                                               RCSwSuspensionStatus, 
                                               RCIRStatus, NIBIRStatus, 
                                               SwSuspensionStatus, 
                                               SetScheduledIRs, 
                                               seqWorkerIsBusy, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, worker, 
                                               toBeScheduledIRs, nextIR, 
                                               currDAG, IRSet, IRDoneSet, 
                                               nextIRObjectToSend, index, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, msg, irID >>

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
                                                     FirstInstall, RCProcSet, 
                                                     OFCProcSet, ContProcSet, 
                                                     RCSwSuspensionStatus, 
                                                     RCIRStatus, NIBIRStatus, 
                                                     SwSuspensionStatus, 
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
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     currDAG, IRSet, IRDoneSet, 
                                                     nextIRObjectToSend, index, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     msg, irID >>

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
                                                 RCNIBEventQueue, FirstInstall, 
                                                 RCProcSet, OFCProcSet, 
                                                 ContProcSet, DAGState, 
                                                 RCSwSuspensionStatus, 
                                                 RCIRStatus, NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 SetScheduledIRs, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, DAGID, nxtDAG, 
                                                 deleterID, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 IRSet, IRDoneSet, 
                                                 nextIRObjectToSend, index, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 irID >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF (~allIRsInDAGInstalled(currDAG[self].dag) /\ ~isDAGStale(currDAG[self].id)) \/ (~allIRsInDAGAreStable(currDAG[self].dag))
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
                                                   /\ IF allIRsInDAGInstalled(currDAG[self].dag)
                                                         THEN /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]
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
                                                        RCSwSuspensionStatus, 
                                                        RCIRStatus, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
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
                                                        seqEvent, worker, 
                                                        nextIR, currDAG, 
                                                        IRDoneSet, 
                                                        nextIRObjectToSend, 
                                                        index, monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        msg, irID >>

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
                                            RCNIBEventQueue, FirstInstall, 
                                            RCProcSet, OFCProcSet, ContProcSet, 
                                            DAGState, RCSwSuspensionStatus, 
                                            RCIRStatus, NIBIRStatus, 
                                            SwSuspensionStatus, 
                                            seqWorkerIsBusy, event, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, DAGID, nxtDAG, 
                                            deleterID, setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, currDAG, IRSet, 
                                            nextIRObjectToSend, index, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, msg, irID >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {}
                                     THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF getIRType(nextIR'[self]) = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \cup {nextIR'[self]}]
                                                ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self] = IRDoneSet[self] \ {getDualOfIR(nextIR'[self])}]
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]
                                          /\ UNCHANGED << nextIR, IRSet, 
                                                          IRDoneSet >>
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, 
                                               IRQueueNIB, RCNIBEventQueue, 
                                               FirstInstall, RCProcSet, 
                                               OFCProcSet, ContProcSet, 
                                               DAGState, RCSwSuspensionStatus, 
                                               RCIRStatus, NIBIRStatus, 
                                               SwSuspensionStatus, 
                                               SetScheduledIRs, 
                                               seqWorkerIsBusy, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, DAGID, 
                                               nxtDAG, deleterID, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               currDAG, nextIRObjectToSend, 
                                               index, monitoringEvent, 
                                               setIRsToReset, resetIR, msg, 
                                               irID >>

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
                                            RCNIBEventQueue, FirstInstall, 
                                            RCProcSet, OFCProcSet, ContProcSet, 
                                            DAGState, RCSwSuspensionStatus, 
                                            RCIRStatus, NIBIRStatus, 
                                            SwSuspensionStatus, 
                                            SetScheduledIRs, seqWorkerIsBusy, 
                                            event, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            DAGID, nxtDAG, deleterID, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, nextIR, 
                                            currDAG, IRSet, IRDoneSet, 
                                            nextIRObjectToSend, index, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, msg, irID >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteDAGIRDoneSet(self)
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
                                          DAGQueue, RCNIBEventQueue, 
                                          FirstInstall, RCProcSet, OFCProcSet, 
                                          ContProcSet, DAGState, 
                                          RCSwSuspensionStatus, RCIRStatus, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          SetScheduledIRs, seqWorkerIsBusy, 
                                          event, topoChangeEvent, 
                                          currSetDownSw, prev_dag_id, init, 
                                          DAGID, nxtDAG, deleterID, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, currDAG, 
                                          IRSet, IRDoneSet, monitoringEvent, 
                                          setIRsToReset, resetIR, msg, irID >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF nextIRObjectToSend[self].IR = 0
                                      THEN /\ IF isSwitchSuspended(nextIRObjectToSend[self].sw)
                                                 THEN /\ IF nextIRObjectToSend[self].IR = 0
                                                            THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                                    type |-> CLEAR_TCAM,
                                                                                                                                                                                                                    flow |-> 0,
                                                                                                                                                                                                                    to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                                    from |-> self[1]
                                                                                                                                                                                                                ]))]
                                                            ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                                    type |-> getIRType(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                                    flow |-> getIRFlow(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                                    to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                                    from |-> self[1]
                                                                                                                                                                                                                ]))]
                                                      /\ IF whichSwitchModel(nextIRObjectToSend[self].sw) = SW_COMPLEX_MODEL
                                                            THEN /\ switchLock' = <<NIC_ASIC_IN, nextIRObjectToSend[self].sw>>
                                                            ELSE /\ switchLock' = <<SW_SIMPLE_ID, nextIRObjectToSend[self].sw>>
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << switchLock, 
                                                                      controller2Switch >>
                                           /\ index' = [index EXCEPT ![self] = GetFirstItemIndexWithTag(IRQueueNIB, self)]
                                           /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index'[self])
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           NIBIRStatus >>
                                      ELSE /\ IF ~isSwitchSuspended(nextIRObjectToSend[self].sw) /\ getNIBIRState(nextIRObjectToSend[self].IR) = IR_NONE
                                                 THEN /\ IF ((nextIRObjectToSend[self].IR) \leq MaxNumIRs)
                                                            THEN /\ IF IR_SENT = IR_DONE /\ NIBIRStatus[(nextIRObjectToSend[self].IR)].dual = IR_DONE
                                                                       THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend[self].IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                       ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend[self].IR)].primary = IR_SENT]
                                                            ELSE /\ IF IR_SENT = IR_DONE /\ NIBIRStatus[(nextIRObjectToSend[self].IR) - MaxNumIRs].primary = IR_DONE
                                                                       THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend[self].IR) - MaxNumIRs] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                       ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend[self].IR) - MaxNumIRs].dual = IR_SENT]
                                                      /\ RCNIBEventQueue' =                    Append(
                                                                                RCNIBEventQueue,
                                                                                [type |-> IR_MOD, IR |-> nextIRObjectToSend[self].IR, state |-> IR_SENT]
                                                                            )
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardAndPopIR"]
                                                      /\ UNCHANGED << IRQueueNIB, 
                                                                      index >>
                                                 ELSE /\ RCNIBEventQueue' =                    Append(
                                                                                RCNIBEventQueue,
                                                                                [type |-> IR_FAILED, IR |-> nextIRObjectToSend[self].IR, state |-> IR_NONE]
                                                                            )
                                                      /\ index' = [index EXCEPT ![self] = GetFirstItemIndexWithTag(IRQueueNIB, self)]
                                                      /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index'[self])
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                      /\ UNCHANGED NIBIRStatus
                                           /\ UNCHANGED << switchLock, 
                                                           controller2Switch >>
                                /\ UNCHANGED << controllerLock, 
                                                swSeqChangedStatus, 
                                                switch2Controller, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, FirstInstall, 
                                                RCProcSet, OFCProcSet, 
                                                ContProcSet, DAGState, 
                                                RCSwSuspensionStatus, 
                                                RCIRStatus, SwSuspensionStatus, 
                                                SetScheduledIRs, 
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
                                                nextIRObjectToSend, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, msg, irID >>

ControllerThreadForwardAndPopIR(self) == /\ pc[self] = "ControllerThreadForwardAndPopIR"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ IF nextIRObjectToSend[self].IR = 0
                                               THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                       type |-> CLEAR_TCAM,
                                                                                                                                                                                                       flow |-> 0,
                                                                                                                                                                                                       to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                       from |-> self[1]
                                                                                                                                                                                                   ]))]
                                               ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend[self].sw)] = Append(controller2Switch[(nextIRObjectToSend[self].sw)], ([
                                                                                                                                                                                                       type |-> getIRType(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                       flow |-> getIRFlow(nextIRObjectToSend[self].IR),
                                                                                                                                                                                                       to |-> nextIRObjectToSend[self].sw,
                                                                                                                                                                                                       from |-> self[1]
                                                                                                                                                                                                   ]))]
                                         /\ IF whichSwitchModel(nextIRObjectToSend[self].sw) = SW_COMPLEX_MODEL
                                               THEN /\ switchLock' = <<NIC_ASIC_IN, nextIRObjectToSend[self].sw>>
                                               ELSE /\ switchLock' = <<SW_SIMPLE_ID, nextIRObjectToSend[self].sw>>
                                         /\ index' = [index EXCEPT ![self] = GetFirstItemIndexWithTag(IRQueueNIB, self)]
                                         /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index'[self])
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                         /\ UNCHANGED << controllerLock, 
                                                         swSeqChangedStatus, 
                                                         switch2Controller, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, 
                                                         RCNIBEventQueue, 
                                                         FirstInstall, 
                                                         RCProcSet, OFCProcSet, 
                                                         ContProcSet, DAGState, 
                                                         RCSwSuspensionStatus, 
                                                         RCIRStatus, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
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
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, currDAG, 
                                                         IRSet, IRDoneSet, 
                                                         nextIRObjectToSend, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, irID >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardAndPopIR(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ Len(swSeqChangedStatus) > 0
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSWAndPop"]
                                               /\ UNCHANGED swSeqChangedStatus
                                          ELSE /\ IF canClearSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerRequestTCAMClear"]
                                                          /\ UNCHANGED swSeqChangedStatus
                                                     ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                                     /\ UNCHANGED swSeqChangedStatus
                                                                ELSE /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    IRQueueNIB, 
                                                    RCNIBEventQueue, 
                                                    FirstInstall, RCProcSet, 
                                                    OFCProcSet, ContProcSet, 
                                                    DAGState, 
                                                    RCSwSuspensionStatus, 
                                                    RCIRStatus, NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    SetScheduledIRs, 
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
                                                    nextIRObjectToSend, index, 
                                                    setIRsToReset, resetIR, 
                                                    msg, irID >>

ControllerSuspendSWAndPop(self) == /\ pc[self] = "ControllerSuspendSWAndPop"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                                   /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND]))
                                   /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, IRQueueNIB, 
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   DAGState, 
                                                   RCSwSuspensionStatus, 
                                                   RCIRStatus, NIBIRStatus, 
                                                   SetScheduledIRs, 
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
                                                   nextIRObjectToSend, index, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   irID >>

ControllerRequestTCAMClear(self) == /\ pc[self] = "ControllerRequestTCAMClear"
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                    /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                          THEN /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> 0, sw |-> monitoringEvent[self].swID]), tag |-> NADIR_NULL])
                                          ELSE /\ TRUE
                                               /\ UNCHANGED IRQueueNIB
                                    /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                    /\ UNCHANGED << switchLock, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    RCNIBEventQueue, 
                                                    FirstInstall, RCProcSet, 
                                                    OFCProcSet, ContProcSet, 
                                                    DAGState, 
                                                    RCSwSuspensionStatus, 
                                                    RCIRStatus, NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    SetScheduledIRs, 
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
                                                    nextIRObjectToSend, index, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    msg, irID >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSWAndPop"]
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
                                                          DAGState, 
                                                          RCSwSuspensionStatus, 
                                                          RCIRStatus, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
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
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, currDAG, 
                                                          IRSet, IRDoneSet, 
                                                          nextIRObjectToSend, 
                                                          index, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, irID >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = getIRSetToReset(monitoringEvent[self].swID)]
                           /\ IF (setIRsToReset'[self] = {})
                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSWAndPop"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, IRQueueNIB, 
                                           RCNIBEventQueue, FirstInstall, 
                                           RCProcSet, OFCProcSet, ContProcSet, 
                                           DAGState, RCSwSuspensionStatus, 
                                           RCIRStatus, NIBIRStatus, 
                                           SwSuspensionStatus, SetScheduledIRs, 
                                           seqWorkerIsBusy, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, DAGID, nxtDAG, 
                                           deleterID, setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           currDAG, IRSet, IRDoneSet, 
                                           nextIRObjectToSend, index, 
                                           monitoringEvent, resetIR, msg, irID >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                     /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                     /\ IF (resetIR'[self] \leq MaxNumIRs)
                           THEN /\ IF IR_NONE = IR_DONE /\ NIBIRStatus[resetIR'[self]].dual = IR_DONE
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                      ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self]].primary = IR_NONE]
                           ELSE /\ IF IR_NONE = IR_DONE /\ NIBIRStatus[resetIR'[self] - MaxNumIRs].primary = IR_DONE
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self] - MaxNumIRs] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                      ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'[self] - MaxNumIRs].dual = IR_NONE]
                     /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> resetIR'[self], state |-> IR_NONE]))
                     /\ IF setIRsToReset'[self] = {}
                           THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSWAndPop"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                     /\ UNCHANGED << switchLock, controllerLock, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, IRQueueNIB, 
                                     FirstInstall, RCProcSet, OFCProcSet, 
                                     ContProcSet, DAGState, 
                                     RCSwSuspensionStatus, RCIRStatus, 
                                     SwSuspensionStatus, SetScheduledIRs, 
                                     seqWorkerIsBusy, event, topoChangeEvent, 
                                     currSetDownSw, prev_dag_id, init, DAGID, 
                                     nxtDAG, deleterID, setRemovableIRs, 
                                     currIR, currIRInDAG, nxtDAGVertices, 
                                     setIRsInDAG, prev_dag, seqEvent, worker, 
                                     toBeScheduledIRs, nextIR, currDAG, IRSet, 
                                     IRDoneSet, nextIRObjectToSend, index, 
                                     monitoringEvent, msg, irID >>

ControllerFreeSuspendedSWAndPop(self) == /\ pc[self] = "ControllerFreeSuspendedSWAndPop"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                         /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent[self].swID, state |-> SW_RUN]))
                                         /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, IRQueueNIB, 
                                                         FirstInstall, 
                                                         RCProcSet, OFCProcSet, 
                                                         ContProcSet, DAGState, 
                                                         RCSwSuspensionStatus, 
                                                         RCIRStatus, 
                                                         NIBIRStatus, 
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
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, currDAG, 
                                                         IRSet, IRDoneSet, 
                                                         nextIRObjectToSend, 
                                                         index, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, irID >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerSuspendSWAndPop(self)
                                   \/ ControllerRequestTCAMClear(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSWAndPop(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                       /\ Len(switch2Controller) > 0
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY,
                                                                      CLEARED_TCAM_SUCCESSFULLY, NIC_ASIC_DOWN, KEEP_ALIVE}, 
                                                 "Failure of assertion at line 636, column 9.")
                                       /\ IF msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerProcessIRModAndPop"]
                                             ELSE /\ IF msg'[self].type \in {CLEARED_TCAM_SUCCESSFULLY, NIC_ASIC_DOWN, KEEP_ALIVE}
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "ForwardToEH"]
                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
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
                                                       DAGState, 
                                                       RCSwSuspensionStatus, 
                                                       RCIRStatus, NIBIRStatus, 
                                                       SwSuspensionStatus, 
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
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, currDAG, IRSet, 
                                                       IRDoneSet, 
                                                       nextIRObjectToSend, 
                                                       index, monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       irID >>

ControllerProcessIRModAndPop(self) == /\ pc[self] = "ControllerProcessIRModAndPop"
                                      /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg[self].flow, msg[self].type)]
                                      /\ Assert(msg[self].from = getSwitchForIR(irID'[self]), 
                                                "Failure of assertion at line 646, column 17.")
                                      /\ FirstInstall' = [FirstInstall EXCEPT ![irID'[self]] = 1]
                                      /\ IF (irID'[self] \leq MaxNumIRs)
                                            THEN /\ IF IR_DONE = IR_DONE /\ NIBIRStatus[irID'[self]].dual = IR_DONE
                                                       THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID'[self]] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                       ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID'[self]].primary = IR_DONE]
                                            ELSE /\ IF IR_DONE = IR_DONE /\ NIBIRStatus[irID'[self] - MaxNumIRs].primary = IR_DONE
                                                       THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID'[self] - MaxNumIRs] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                       ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID'[self] - MaxNumIRs].dual = IR_DONE]
                                      /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> irID'[self], state |-> IR_DONE]))
                                      /\ switch2Controller' = Tail(switch2Controller)
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      IRQueueNIB, RCProcSet, 
                                                      OFCProcSet, ContProcSet, 
                                                      DAGState, 
                                                      RCSwSuspensionStatus, 
                                                      RCIRStatus, 
                                                      SwSuspensionStatus, 
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
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      currDAG, IRSet, 
                                                      IRDoneSet, 
                                                      nextIRObjectToSend, 
                                                      index, monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      msg >>

ForwardToEH(self) == /\ pc[self] = "ForwardToEH"
                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ swSeqChangedStatus' = Append(swSeqChangedStatus, msg[self])
                     /\ switch2Controller' = Tail(switch2Controller)
                     /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                     /\ UNCHANGED << switchLock, controllerLock, 
                                     controller2Switch, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, IRQueueNIB, 
                                     RCNIBEventQueue, FirstInstall, RCProcSet, 
                                     OFCProcSet, ContProcSet, DAGState, 
                                     RCSwSuspensionStatus, RCIRStatus, 
                                     NIBIRStatus, SwSuspensionStatus, 
                                     SetScheduledIRs, seqWorkerIsBusy, event, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, DAGID, nxtDAG, 
                                     deleterID, setRemovableIRs, currIR, 
                                     currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                     prev_dag, seqEvent, worker, 
                                     toBeScheduledIRs, nextIR, currDAG, IRSet, 
                                     IRDoneSet, nextIRObjectToSend, index, 
                                     monitoringEvent, setIRsToReset, resetIR, 
                                     msg, irID >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ ControllerProcessIRModAndPop(self)
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

=============================================================================

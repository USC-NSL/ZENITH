---------------------------- MODULE no_semaphore ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag, NadirTypes, NadirAckQueue

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_SEQ, CONT_MONITOR, CONT_EVENT, WATCH_DOG
CONSTANTS IR_TO_SWITCH_ASSIGNMENT

ASSUME {"ofc0", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE
ASSUME DOMAIN IR_TO_SWITCH_ASSIGNMENT = 1..MaxNumIRs

(*--fair algorithm stateConsistency
    variables
        rcMessageCounter = 0,
        switchLock = <<NO_LOCK, NO_LOCK>>,
        controllerLock = <<NO_LOCK, NO_LOCK>>,
        swSeqChangedStatus = <<>>,
        controller2Switch = [x \in SW |-> <<>>],
        switch2Controller = <<>>, 

        FirstInstall = [x \in 1..MaxNumIRs |-> 0],
        
        RCProcSet = ({rc0} \X {CONT_SEQ}),
        OFCProcSet = (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup 
                     (({ofc0} \X {CONT_EVENT})) \cup 
                     (({ofc0} \X {CONT_MONITOR})),
        ContProcSet = RCProcSet \cup OFCProcSet,
        
        controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0],
        controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed],
        
        dependencyGraph \in generateConnectedDAG(1..MaxNumIRs),              
        IR2SW = IR_TO_SWITCH_ASSIGNMENT,
        rcInternalState = [x \in RCProcSet |-> [type |-> NO_STATUS]],
        ofcInternalState = [x \in OFCProcSet |-> [type |-> NO_STATUS]],
        IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        IRQueueNIB = <<>>,
        SetScheduledIRs = [y \in SW |-> {}],
        workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: 
            ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
    define
        moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
        getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                                     [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0 

        isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                             /\ IRStatus[y] # IR_DONE
        getSetIRsCanBeScheduledNext == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                            /\ isDependencySatisfied(x)
                                                            /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                            /\ x \notin SetScheduledIRs[IR2SW[x]]}
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                        /\ swSeqChangedStatus[x].num > monEvent.num
        shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                                     \/ monEvent.type = NIC_ASIC_DOWN
                                     \/ /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.status.installerStatus = INSTALLER_DOWN
        canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                           /\ monEvent.status.installerStatus = INSTALLER_UP
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ IR2SW[x] = SID
                                                     /\ IRStatus[x] \notin {IR_DONE, IR_NONE}}
        returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                                   /\ controllerSubmoduleFailStat[x] = Failed}
        isFinished == \A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE                                                                                                        
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

    macro NadirAckQueuePut(queue, object, counter)
    begin
        queue := Append(queue, [data |-> object, tag |-> NADIR_NULL, counter |-> counter]);
    end macro;

    macro NadirAckQueueGet(queue, tag, index, message, counter)
    begin
        await ExistsItemWithTag(queue, NADIR_NULL) \/ ExistsItemWithTag(queue, tag);
        index := GetItemIndexWithTag(queue, tag);
        message := queue[index].data;
        counter := queue[index].counter;
        queue[index].tag := tag;
    end macro;

    macro NadirAckQueueAck(queue, tag, index)
    begin
        index := GetFirstItemIndexWithTag(queue, tag);
        queue := RemoveFromSequenceByIndex(queue, index);
    end macro;

    macro controllerWaitForLockFree()
    begin
        await controllerLock = <<NO_LOCK, NO_LOCK>>;
        await switchLock = <<NO_LOCK, NO_LOCK>>;
    end macro

    macro controllerReleaseLock(prevLockHolder)
    begin
        await \/ controllerLock = prevLockHolder
              \/ controllerLock = <<NO_LOCK, NO_LOCK>>;
        await switchLock = <<NO_LOCK, NO_LOCK>>;
        controllerLock := <<NO_LOCK, NO_LOCK>>;
    end macro

    macro controllerModuleFails()
    begin
        controllerSubmoduleFailStat[self] := Failed;
        controllerSubmoduleFailNum[self[1]] := controllerSubmoduleFailNum[self[1]] + 1;
    end macro;

    macro controllerModuleFailOrNot()
    begin
        if (
            /\ controllerSubmoduleFailStat[self] = NotFailed 
            /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
        ) then
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
        with destination = IR2SW[irID] do
            NadirFanoutFIFOPut(
                controller2Switch,
                destination,
                [type |-> INSTALL_FLOW, flow |-> irID, to |-> destination, from |-> self[1]]
            );
            if whichSwitchModel(destination) = SW_COMPLEX_MODEL then 
                switchLock := <<NIC_ASIC_IN, destination>>;
            else
                switchLock := <<SW_SIMPLE_ID, destination>>;
            end if;
        end with;
    end macro;

    fair process controllerSequencer \in ({rc0} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}, nextIR = 0, stepOfFailure = 0;
    begin
    ControllerSeqProc:
    while TRUE do
        await moduleIsUp(self);
        controllerWaitForLockFree();
        toBeScheduledIRs := getSetIRsCanBeScheduledNext;
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
                        SetScheduledIRs[IR2SW[nextIR]] := SetScheduledIRs[IR2SW[nextIR]] \cup {nextIR};
                    end if;
                end if;
            end if;
            
            if (stepOfFailure # 0) then    
                controllerModuleFails();
                goto ControllerSeqStateReconciliation; 
            end if;        

            ScheduleTheIR: 
                controllerWaitForLockFree();
                whichStepToFail(2);
                if (stepOfFailure # 1) then
                    NadirAckQueuePut(IRQueueNIB, nextIR, rcMessageCounter);
                    rcMessageCounter := rcMessageCounter + 1;
                    toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                    if (stepOfFailure # 2) then
                        rcInternalState[self] := [type |-> NO_STATUS];    
                    end if;
                end if;
                
                if (stepOfFailure # 0) then    
                    controllerModuleFails();
                    goto ControllerSeqStateReconciliation; 
                elsif toBeScheduledIRs = {} then
                    goto ControllerSeqProc;
                end if;  
        end while;                                                
    end while;
    
    ControllerSeqStateReconciliation:   
        await moduleIsUp(self);
        controllerReleaseLock(self);
        if(rcInternalState[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[IR2SW[rcInternalState[self].next]] := 
                SetScheduledIRs[IR2SW[rcInternalState[self].next]] \ {rcInternalState[self].next};
        end if;
        goto ControllerSeqProc;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRIDToSend = 0, index = -1, stepOfFailure = 0, irCounter = -1;
    begin
    ControllerThread:
    while TRUE do
        await moduleIsUp(self);
        controllerWaitForLockFree();

        NadirAckQueueGet(IRQueueNIB, self, index, nextIRIDToSend, irCounter);
        
        whichStepToFail(2);
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
                if ~isSwitchSuspended(IR2SW[nextIRIDToSend]) /\ IRStatus[nextIRIDToSend] = IR_NONE then
                    IRStatus[nextIRIDToSend] := IR_SENT;
                    \* RCNIBEventQueue := Append(
                    \*     RCNIBEventQueue, 
                    \*     [type |-> IR_MOD, IR |-> nextIRIDToSend, state |-> IR_SENT]
                    \* );
                    ControllerThreadForwardIR:
                        controllerWaitForLockFree();
                        whichStepToFail(1);
                        if (stepOfFailure # 1) then
                            controllerSendIR(nextIRIDToSend);
                        else
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
        controllerReleaseLock(self);
        if (ofcInternalState[self].type = STATUS_LOCKING) then
            if (IRStatus[ofcInternalState[self].next] = IR_SENT) then
                IRStatus[ofcInternalState[self].next] := IR_NONE;
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
        controllerWaitForLockFree();
        
        monitoringEvent := Head(swSeqChangedStatus);
        if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
           ControllerSuspendSW: 
               controllerWaitForLockFree();
               controllerModuleFailOrNot();
               if (controllerSubmoduleFailStat[self] = NotFailed) then
                   SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;        
               else
                   goto ControllerEventHandlerStateReconciliation;
               end if;
        elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            ControllerFreeSuspendedSW: 
                controllerWaitForLockFree();
                whichStepToFail(2);
                if (stepOfFailure # 1) then 
                    ofcInternalState[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                    if (stepOfFailure # 2) then
                        SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;  
                    end if;
                end if;

                if (stepOfFailure # 0) then
                    controllerModuleFails();
                    goto ControllerEventHandlerStateReconciliation;
                end if;
           
            ControllerCheckIfThisIsLastEvent:
                controllerWaitForLockFree();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    if ~existsMonitoringEventHigherNum(monitoringEvent) then
                        getIRsToBeChecked:
                            controllerWaitForLockFree();
                            controllerModuleFailOrNot();
                            if (controllerSubmoduleFailStat[self] = NotFailed) then
                                setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                                if (setIRsToReset = {}) then 
                                    goto ControllerEvenHanlderRemoveEventFromQueue;
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

                                    if IRStatus[resetIR] # IR_DONE then
                                        IRStatus[resetIR] := IR_NONE;
                                    end if;

                                    if setIRsToReset = {} then
                                        goto ControllerEvenHanlderRemoveEventFromQueue;
                                    end if;
                                else
                                    goto ControllerEventHandlerStateReconciliation;
                                end if;
                            end while;
                    end if;
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
        end if;

        ControllerEvenHanlderRemoveEventFromQueue:
            controllerWaitForLockFree();
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
        controllerReleaseLock(self);
        if (ofcInternalState[self].type = START_RESET_IR) then
           SwSuspensionStatus[ofcInternalState[self].sw] := SW_SUSPEND;
        end if;
        goto ControllerEventHandlerProc;
    end process

    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = [type |-> 0]
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        await moduleIsUp(self);
        await switch2Controller # <<>>;
        controllerReleaseLock(self);
        msg := Head(switch2Controller);
        assert msg.from = IR2SW[msg.flow];
        assert msg.type \in {INSTALLED_SUCCESSFULLY};
            if msg.type = INSTALLED_SUCCESSFULLY then
                ControllerUpdateIR2:
                    controllerWaitForLockFree(); 
                    controllerModuleFailOrNot();
                    if (controllerSubmoduleFailStat[self] = NotFailed) then
                        FirstInstall[msg.flow] := 1;
                        IRStatus[msg.flow] := IR_DONE;
                    else
                        goto ControllerMonitorCheckIfMastr;
                    end if;
            else assert FALSE;
            end if;
        
        MonitoringServerRemoveFromQueue:
            controllerWaitForLockFree();
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
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "792a31e3")
\* Process variable stepOfFailure of process controllerSequencer at line 187 col 50 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 247 col 47 changed to stepOfFailure_c
VARIABLES rcMessageCounter, switchLock, controllerLock, swSeqChangedStatus, 
          controller2Switch, switch2Controller, FirstInstall, RCProcSet, 
          OFCProcSet, ContProcSet, controllerSubmoduleFailNum, 
          controllerSubmoduleFailStat, dependencyGraph, IR2SW, 
          rcInternalState, ofcInternalState, IRStatus, SwSuspensionStatus, 
          IRQueueNIB, SetScheduledIRs, workerThreadRanking, pc

(* define statement *)
moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                             [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0

isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                     /\ IRStatus[y] # IR_DONE
getSetIRsCanBeScheduledNext == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                    /\ isDependencySatisfied(x)
                                                    /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                    /\ x \notin SetScheduledIRs[IR2SW[x]]}
isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                /\ swSeqChangedStatus[x].num > monEvent.num
shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                             \/ monEvent.type = NIC_ASIC_DOWN
                             \/ /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.status.installerStatus = INSTALLER_DOWN
canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                   /\ monEvent.status.installerStatus = INSTALLER_UP
getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ IR2SW[x] = SID
                                             /\ IRStatus[x] \notin {IR_DONE, IR_NONE}}
returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                           /\ controllerSubmoduleFailStat[x] = Failed}
isFinished == \A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE

VARIABLES toBeScheduledIRs, nextIR, stepOfFailure_, nextIRIDToSend, index, 
          stepOfFailure_c, irCounter, monitoringEvent, setIRsToReset, resetIR, 
          stepOfFailure, msg, controllerFailedModules

vars == << rcMessageCounter, switchLock, controllerLock, swSeqChangedStatus, 
           controller2Switch, switch2Controller, FirstInstall, RCProcSet, 
           OFCProcSet, ContProcSet, controllerSubmoduleFailNum, 
           controllerSubmoduleFailStat, dependencyGraph, IR2SW, 
           rcInternalState, ofcInternalState, IRStatus, SwSuspensionStatus, 
           IRQueueNIB, SetScheduledIRs, workerThreadRanking, pc, 
           toBeScheduledIRs, nextIR, stepOfFailure_, nextIRIDToSend, index, 
           stepOfFailure_c, irCounter, monitoringEvent, setIRsToReset, 
           resetIR, stepOfFailure, msg, controllerFailedModules >>

ProcSet == (({rc0} \X {CONT_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})) \cup (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Global variables *)
        /\ rcMessageCounter = 0
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        /\ RCProcSet = ({rc0} \X {CONT_SEQ})
        /\ OFCProcSet = ((({ofc0} \X CONTROLLER_THREAD_POOL)) \cup
                         (({ofc0} \X {CONT_EVENT})) \cup
                         (({ofc0} \X {CONT_MONITOR})))
        /\ ContProcSet = (RCProcSet \cup OFCProcSet)
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ IR2SW = IR_TO_SWITCH_ASSIGNMENT
        /\ rcInternalState = [x \in RCProcSet |-> [type |-> NO_STATUS]]
        /\ ofcInternalState = [x \in OFCProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ workerThreadRanking = (                  CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]:
                                  ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        (* Process controllerWorkerThreads *)
        /\ nextIRIDToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ stepOfFailure_c = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ irCounter = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ stepOfFailure = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [type |-> 0]]
        (* Process watchDog *)
        /\ controllerFailedModules = [self \in ({ofc0, rc0} \X {WATCH_DOG}) |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in ({rc0} \X {CONT_SEQ}) -> "ControllerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({ofc0, rc0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

ControllerSeqProc(self) == /\ pc[self] = "ControllerSeqProc"
                           /\ moduleIsUp(self)
                           /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext]
                           /\ toBeScheduledIRs'[self] # {}
                           /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                           /\ UNCHANGED << rcMessageCounter, switchLock, 
                                           controllerLock, swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, FirstInstall, 
                                           RCProcSet, OFCProcSet, ContProcSet, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           dependencyGraph, IR2SW, 
                                           rcInternalState, ofcInternalState, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, SetScheduledIRs, 
                                           workerThreadRanking, nextIR, 
                                           stepOfFailure_, nextIRIDToSend, 
                                           index, stepOfFailure_c, irCounter, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure, msg, 
                                           controllerFailedModules >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                                        THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![IR2SW[nextIR'[self]]] = SetScheduledIRs[IR2SW[nextIR'[self]]] \cup {nextIR'[self]}]
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
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                                       /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat >>
                            /\ UNCHANGED << rcMessageCounter, switchLock, 
                                            controllerLock, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, FirstInstall, 
                                            RCProcSet, OFCProcSet, ContProcSet, 
                                            dependencyGraph, IR2SW, 
                                            ofcInternalState, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            workerThreadRanking, 
                                            toBeScheduledIRs, nextIRIDToSend, 
                                            index, stepOfFailure_c, irCounter, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, msg, 
                                            controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                             THEN /\ \E num \in 0..2:
                                       stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                             ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                       /\ IF (stepOfFailure_'[self] # 1)
                             THEN /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> nextIR[self], tag |-> NADIR_NULL, counter |-> rcMessageCounter])
                                  /\ rcMessageCounter' = rcMessageCounter + 1
                                  /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
                                  /\ IF (stepOfFailure_'[self] # 2)
                                        THEN /\ rcInternalState' = [rcInternalState EXCEPT ![self] = [type |-> NO_STATUS]]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED rcInternalState
                             ELSE /\ TRUE
                                  /\ UNCHANGED << rcMessageCounter, 
                                                  rcInternalState, IRQueueNIB, 
                                                  toBeScheduledIRs >>
                       /\ IF (stepOfFailure_'[self] # 0)
                             THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                  /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                             ELSE /\ IF toBeScheduledIRs'[self] = {}
                                        THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                  /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat >>
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, FirstInstall, 
                                       RCProcSet, OFCProcSet, ContProcSet, 
                                       dependencyGraph, IR2SW, 
                                       ofcInternalState, IRStatus, 
                                       SwSuspensionStatus, SetScheduledIRs, 
                                       workerThreadRanking, nextIR, 
                                       nextIRIDToSend, index, stepOfFailure_c, 
                                       irCounter, monitoringEvent, 
                                       setIRsToReset, resetIR, stepOfFailure, 
                                       msg, controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ moduleIsUp(self)
                                          /\ \/ controllerLock = self
                                             \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (rcInternalState[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![IR2SW[rcInternalState[self].next]] = SetScheduledIRs[IR2SW[rcInternalState[self].next]] \ {rcInternalState[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
                                          /\ UNCHANGED << rcMessageCounter, 
                                                          switchLock, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          FirstInstall, 
                                                          RCProcSet, 
                                                          OFCProcSet, 
                                                          ContProcSet, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          dependencyGraph, 
                                                          IR2SW, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          workerThreadRanking, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          stepOfFailure_c, 
                                                          irCounter, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          controllerFailedModules >>

controllerSequencer(self) == ControllerSeqProc(self)
                                \/ SchedulerMechanism(self)
                                \/ ScheduleTheIR(self)
                                \/ ControllerSeqStateReconciliation(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ moduleIsUp(self)
                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ ExistsItemWithTag(IRQueueNIB, NADIR_NULL) \/ ExistsItemWithTag(IRQueueNIB, self)
                          /\ index' = [index EXCEPT ![self] = GetItemIndexWithTag(IRQueueNIB, self)]
                          /\ nextIRIDToSend' = [nextIRIDToSend EXCEPT ![self] = IRQueueNIB[index'[self]].data]
                          /\ irCounter' = [irCounter EXCEPT ![self] = IRQueueNIB[index'[self]].counter]
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![index'[self]].tag = self]
                          /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                THEN /\ \E num \in 0..2:
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
                          /\ UNCHANGED << rcMessageCounter, switchLock, 
                                          controllerLock, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          FirstInstall, RCProcSet, OFCProcSet, 
                                          ContProcSet, dependencyGraph, IR2SW, 
                                          rcInternalState, IRStatus, 
                                          SwSuspensionStatus, SetScheduledIRs, 
                                          workerThreadRanking, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure, msg, 
                                          controllerFailedModules >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF    (
                                          /\ controllerSubmoduleFailStat[self] = NotFailed
                                          /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
                                      )
                                      THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                 /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              \/ /\ TRUE
                                                 /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                           controllerSubmoduleFailStat >>
                                /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                      THEN /\ IF ~isSwitchSuspended(IR2SW[nextIRIDToSend[self]]) /\ IRStatus[nextIRIDToSend[self]] = IR_NONE
                                                 THEN /\ IRStatus' = [IRStatus EXCEPT ![nextIRIDToSend[self]] = IR_SENT]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                                      /\ UNCHANGED IRStatus
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                           /\ UNCHANGED IRStatus
                                /\ UNCHANGED << rcMessageCounter, switchLock, 
                                                controllerLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                FirstInstall, RCProcSet, 
                                                OFCProcSet, ContProcSet, 
                                                dependencyGraph, IR2SW, 
                                                rcInternalState, 
                                                ofcInternalState, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, 
                                                workerThreadRanking, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, nextIRIDToSend, 
                                                index, stepOfFailure_c, 
                                                irCounter, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, msg, 
                                                controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..1:
                                                   stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure_c'[self] # 1)
                                         THEN /\ LET destination == IR2SW[nextIRIDToSend[self]] IN
                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![destination] = Append(controller2Switch[destination], ([type |-> INSTALL_FLOW, flow |-> nextIRIDToSend[self], to |-> destination, from |-> self[1]]))]
                                                   /\ IF whichSwitchModel(destination) = SW_COMPLEX_MODEL
                                                         THEN /\ switchLock' = <<NIC_ASIC_IN, destination>>
                                                         ELSE /\ switchLock' = <<SW_SIMPLE_ID, destination>>
                                              /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                         ELSE /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                              /\ UNCHANGED << switchLock, 
                                                              controller2Switch >>
                                   /\ UNCHANGED << rcMessageCounter, 
                                                   controllerLock, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   dependencyGraph, IR2SW, 
                                                   rcInternalState, 
                                                   ofcInternalState, IRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   workerThreadRanking, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   nextIRIDToSend, index, 
                                                   irCounter, monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, 
                                                   controllerFailedModules >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                             /\ UNCHANGED << ofcInternalState, 
                                                             IRQueueNIB, index >>
                                  /\ IF (stepOfFailure_c'[self] # 0)
                                        THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                             /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat >>
                                  /\ UNCHANGED << rcMessageCounter, switchLock, 
                                                  controllerLock, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  FirstInstall, RCProcSet, 
                                                  OFCProcSet, ContProcSet, 
                                                  dependencyGraph, IR2SW, 
                                                  rcInternalState, IRStatus, 
                                                  SwSuspensionStatus, 
                                                  SetScheduledIRs, 
                                                  workerThreadRanking, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, 
                                                  nextIRIDToSend, irCounter, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, 
                                                  controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ moduleIsUp(self)
                                             /\ \/ controllerLock = self
                                                \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (ofcInternalState[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (IRStatus[ofcInternalState[self].next] = IR_SENT)
                                                              THEN /\ IRStatus' = [IRStatus EXCEPT ![ofcInternalState[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED IRStatus
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED IRStatus
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << rcMessageCounter, 
                                                             switchLock, 
                                                             swSeqChangedStatus, 
                                                             controller2Switch, 
                                                             switch2Controller, 
                                                             FirstInstall, 
                                                             RCProcSet, 
                                                             OFCProcSet, 
                                                             ContProcSet, 
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             dependencyGraph, 
                                                             IR2SW, 
                                                             rcInternalState, 
                                                             ofcInternalState, 
                                                             SwSuspensionStatus, 
                                                             IRQueueNIB, 
                                                             SetScheduledIRs, 
                                                             workerThreadRanking, 
                                                             toBeScheduledIRs, 
                                                             nextIR, 
                                                             stepOfFailure_, 
                                                             nextIRIDToSend, 
                                                             index, 
                                                             stepOfFailure_c, 
                                                             irCounter, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, 
                                                             stepOfFailure, 
                                                             msg, 
                                                             controllerFailedModules >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ moduleIsUp(self)
                                    /\ swSeqChangedStatus # <<>>
                                    /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << rcMessageCounter, 
                                                    switchLock, controllerLock, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    FirstInstall, RCProcSet, 
                                                    OFCProcSet, ContProcSet, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    dependencyGraph, IR2SW, 
                                                    rcInternalState, 
                                                    ofcInternalState, IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    workerThreadRanking, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    nextIRIDToSend, index, 
                                                    stepOfFailure_c, irCounter, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, 
                                                    controllerFailedModules >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                   /\ UNCHANGED << rcMessageCounter, 
                                                                   switchLock, 
                                                                   controllerLock, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   FirstInstall, 
                                                                   RCProcSet, 
                                                                   OFCProcSet, 
                                                                   ContProcSet, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   rcInternalState, 
                                                                   IRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
                                                                   workerThreadRanking, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   nextIRIDToSend, 
                                                                   index, 
                                                                   stepOfFailure_c, 
                                                                   irCounter, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, 
                                                                   controllerFailedModules >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ IF    (
                                       /\ controllerSubmoduleFailStat[self] = NotFailed
                                       /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
                                   )
                                   THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                           \/ /\ TRUE
                                              /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat >>
                             /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                   THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED SwSuspensionStatus
                             /\ UNCHANGED << rcMessageCounter, switchLock, 
                                             controllerLock, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, FirstInstall, 
                                             RCProcSet, OFCProcSet, 
                                             ContProcSet, dependencyGraph, 
                                             IR2SW, rcInternalState, 
                                             ofcInternalState, IRStatus, 
                                             IRQueueNIB, SetScheduledIRs, 
                                             workerThreadRanking, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, nextIRIDToSend, 
                                             index, stepOfFailure_c, irCounter, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, 
                                             controllerFailedModules >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..2:
                                                   stepOfFailure' = [stepOfFailure EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure' = [stepOfFailure EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure'[self] # 1)
                                         THEN /\ ofcInternalState' = [ofcInternalState EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                              /\ IF (stepOfFailure'[self] # 2)
                                                    THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED SwSuspensionStatus
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << ofcInternalState, 
                                                              SwSuspensionStatus >>
                                   /\ IF (stepOfFailure'[self] # 0)
                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ UNCHANGED << rcMessageCounter, 
                                                   switchLock, controllerLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   FirstInstall, RCProcSet, 
                                                   OFCProcSet, ContProcSet, 
                                                   dependencyGraph, IR2SW, 
                                                   rcInternalState, IRStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   workerThreadRanking, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   nextIRIDToSend, index, 
                                                   stepOfFailure_c, irCounter, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   controllerFailedModules >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ IF    (
                                                    /\ controllerSubmoduleFailStat[self] = NotFailed
                                                    /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
                                                )
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
                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                          /\ UNCHANGED << rcMessageCounter, 
                                                          switchLock, 
                                                          controllerLock, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          FirstInstall, 
                                                          RCProcSet, 
                                                          OFCProcSet, 
                                                          ContProcSet, 
                                                          dependencyGraph, 
                                                          IR2SW, 
                                                          rcInternalState, 
                                                          ofcInternalState, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          SetScheduledIRs, 
                                                          workerThreadRanking, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          nextIRIDToSend, 
                                                          index, 
                                                          stepOfFailure_c, 
                                                          irCounter, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          controllerFailedModules >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ IF    (
                                     /\ controllerSubmoduleFailStat[self] = NotFailed
                                     /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
                                 )
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
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                      /\ UNCHANGED setIRsToReset
                           /\ UNCHANGED << rcMessageCounter, switchLock, 
                                           controllerLock, swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, FirstInstall, 
                                           RCProcSet, OFCProcSet, ContProcSet, 
                                           dependencyGraph, IR2SW, 
                                           rcInternalState, ofcInternalState, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, SetScheduledIRs, 
                                           workerThreadRanking, 
                                           toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, nextIRIDToSend, 
                                           index, stepOfFailure_c, irCounter, 
                                           monitoringEvent, resetIR, 
                                           stepOfFailure, msg, 
                                           controllerFailedModules >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ IF    (
                               /\ controllerSubmoduleFailStat[self] = NotFailed
                               /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
                           )
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
                                /\ IF IRStatus[resetIR'[self]] # IR_DONE
                                      THEN /\ IRStatus' = [IRStatus EXCEPT ![resetIR'[self]] = IR_NONE]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED IRStatus
                                /\ IF setIRsToReset'[self] = {}
                                      THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                /\ UNCHANGED << IRStatus, setIRsToReset, 
                                                resetIR >>
                     /\ UNCHANGED << rcMessageCounter, switchLock, 
                                     controllerLock, swSeqChangedStatus, 
                                     controller2Switch, switch2Controller, 
                                     FirstInstall, RCProcSet, OFCProcSet, 
                                     ContProcSet, dependencyGraph, IR2SW, 
                                     rcInternalState, ofcInternalState, 
                                     SwSuspensionStatus, IRQueueNIB, 
                                     SetScheduledIRs, workerThreadRanking, 
                                     toBeScheduledIRs, nextIR, stepOfFailure_, 
                                     nextIRIDToSend, index, stepOfFailure_c, 
                                     irCounter, monitoringEvent, stepOfFailure, 
                                     msg, controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus # <<>>
                                                   /\ \/ controllerLock = self
                                                      \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (ofcInternalState[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![ofcInternalState[self].sw] = SW_SUSPEND]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED SwSuspensionStatus
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << rcMessageCounter, 
                                                                   switchLock, 
                                                                   swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   FirstInstall, 
                                                                   RCProcSet, 
                                                                   OFCProcSet, 
                                                                   ContProcSet, 
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   rcInternalState, 
                                                                   ofcInternalState, 
                                                                   IRStatus, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
                                                                   workerThreadRanking, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   nextIRIDToSend, 
                                                                   index, 
                                                                   stepOfFailure_c, 
                                                                   irCounter, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
                                                                   msg, 
                                                                   controllerFailedModules >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ moduleIsUp(self)
                                       /\ switch2Controller # <<>>
                                       /\ \/ controllerLock = self
                                          \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].from = IR2SW[msg'[self].flow], 
                                                 "Failure of assertion at line 426, column 9.")
                                       /\ Assert(msg'[self].type \in {INSTALLED_SUCCESSFULLY}, 
                                                 "Failure of assertion at line 427, column 9.")
                                       /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIR2"]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 438, column 18.")
                                                  /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                       /\ UNCHANGED << rcMessageCounter, 
                                                       switchLock, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       FirstInstall, RCProcSet, 
                                                       OFCProcSet, ContProcSet, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       dependencyGraph, IR2SW, 
                                                       rcInternalState, 
                                                       ofcInternalState, 
                                                       IRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       workerThreadRanking, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       nextIRIDToSend, index, 
                                                       stepOfFailure_c, 
                                                       irCounter, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, 
                                                       controllerFailedModules >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ IF    (
                                                   /\ controllerSubmoduleFailStat[self] = NotFailed
                                                   /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
                                               )
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
                                         /\ UNCHANGED << rcMessageCounter, 
                                                         switchLock, 
                                                         controllerLock, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         FirstInstall, 
                                                         RCProcSet, OFCProcSet, 
                                                         ContProcSet, 
                                                         dependencyGraph, 
                                                         IR2SW, 
                                                         rcInternalState, 
                                                         ofcInternalState, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         workerThreadRanking, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         nextIRIDToSend, index, 
                                                         stepOfFailure_c, 
                                                         irCounter, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         controllerFailedModules >>

ControllerUpdateIR2(self) == /\ pc[self] = "ControllerUpdateIR2"
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ IF    (
                                       /\ controllerSubmoduleFailStat[self] = NotFailed
                                       /\ controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])
                                   )
                                   THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                           \/ /\ TRUE
                                              /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat >>
                             /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                   THEN /\ FirstInstall' = [FirstInstall EXCEPT ![msg[self].flow] = 1]
                                        /\ IRStatus' = [IRStatus EXCEPT ![msg[self].flow] = IR_DONE]
                                        /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                        /\ UNCHANGED << FirstInstall, IRStatus >>
                             /\ UNCHANGED << rcMessageCounter, switchLock, 
                                             controllerLock, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, RCProcSet, 
                                             OFCProcSet, ContProcSet, 
                                             dependencyGraph, IR2SW, 
                                             rcInternalState, ofcInternalState, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, 
                                             workerThreadRanking, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, nextIRIDToSend, 
                                             index, stepOfFailure_c, irCounter, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, 
                                             controllerFailedModules >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerUpdateIR2(self)

ControllerWatchDogProc(self) == /\ pc[self] = "ControllerWatchDogProc"
                                /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerFailedModules' = [controllerFailedModules EXCEPT ![self] = returnControllerFailedModules(self[1])]
                                /\ Cardinality(controllerFailedModules'[self]) > 0
                                /\ \E module \in controllerFailedModules'[self]:
                                     /\ Assert(controllerSubmoduleFailStat[module] = Failed, 
                                               "Failure of assertion at line 461, column 13.")
                                     /\ controllerLock' = module
                                     /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![module] = NotFailed]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerWatchDogProc"]
                                /\ UNCHANGED << rcMessageCounter, switchLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                FirstInstall, RCProcSet, 
                                                OFCProcSet, ContProcSet, 
                                                controllerSubmoduleFailNum, 
                                                dependencyGraph, IR2SW, 
                                                rcInternalState, 
                                                ofcInternalState, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, 
                                                workerThreadRanking, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, nextIRIDToSend, 
                                                index, stepOfFailure_c, 
                                                irCounter, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, msg >>

watchDog(self) == ControllerWatchDogProc(self)

Next == (\E self \in ({rc0} \X {CONT_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))
           \/ (\E self \in ({ofc0, rc0} \X {WATCH_DOG}): watchDog(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({rc0} \X {CONT_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in ({ofc0, rc0} \X {WATCH_DOG}) : WF_vars(watchDog(self))

\* END TRANSLATION 

===============

---------------------------- MODULE zenith ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_SEQ, CONT_MONITOR, CONT_EVENT, WATCH_DOG

ASSUME {"ofc0", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE

(*--fair algorithm stateConsistency
    variables
        switchLock = <<NO_LOCK, NO_LOCK>>,
        controllerLock = <<NO_LOCK, NO_LOCK>>,
        swSeqChangedStatus = <<>>,
        controller2Switch = [x \in SW |-> <<>>],
        switch2Controller = <<>>, 

        FirstInstall = [x \in 1..MaxNumIRs |-> 0],
        ContProcSet = (({rc0} \X {CONT_SEQ})) \cup 
                        (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup 
                        (({ofc0} \X {CONT_EVENT})) \cup 
                        (({ofc0} \X {CONT_MONITOR})),
        
        controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0],
        controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed],
        
        dependencyGraph \in generateConnectedDAG(1..MaxNumIRs),              
        IR2SW = CHOOSE x \in [1..MaxNumIRs -> SW]: 
            ~\E y, z \in DOMAIN x: /\ y > z 
                                   /\ switchOrdering[x[y]] =< switchOrdering[x[z]],
        idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK],
        controllerStateNIB = [
            x \in ContProcSet |-> [
                type |-> NO_STATUS
            ]
        ],
        IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
        SwSuspensionStatus = [x \in SW |-> SW_RUN],
        IRQueueNIB = <<>>,
        SetScheduledIRs = [y \in SW |-> {}],
        switchOrdering = CHOOSE x \in [SW -> 1..Cardinality(SW)]: 
            ~\E y, z \in SW: y # z /\ x[y] = x[z],
        workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: 
            ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
    define
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
        
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

        isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                             /\ IRStatus[y] # IR_DONE
        getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                                  /\ isDependencySatisfied(x)
                                                                  /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRs[IR2SW[x]]}

        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>)
                                                              /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}        
        canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                                  \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NO_TAG 
                                                     /\ NoEntryTaggedWith(threadID) 
                                                     /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
        setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
                                                                                                                        /\ y.tag = <<CID, x>>
                                                                                         /\ pc[<<CID, x>>] = "ControllerThread"}
        threadWithLowerIDGetsTheLock(CID, threadID, nIR, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: 
                                                                                                                z \in setThreadsAttemptingForLock(CID, nIR, IRQueue)}) 
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

    macro controllerSendIR(s)
    begin
        controller2Switch[IR2SW[s]] := Append(
            controller2Switch[IR2SW[s]], 
            [
                type |-> INSTALL_FLOW,
                to |-> IR2SW[s],
                flow |-> s
            ]
        );
        if whichSwitchModel(IR2SW[s]) = SW_COMPLEX_MODEL then 
            switchLock := <<NIC_ASIC_IN, IR2SW[s]>>;
        else
            switchLock := <<SW_SIMPLE_ID, IR2SW[s]>>;
        end if;
    end macro;

    macro modifiedEnqueue()
    begin
        IRQueueNIB := Append(
            IRQueueNIB, [
                IR |-> nextIR, 
                tag |-> NO_TAG
            ]
        );
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

    fair process controllerSequencer \in ({rc0} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}, nextIR = 0, stepOfFailure = 0;
    begin
    ControllerSeqProc:
    while TRUE do
        await moduleIsUp(self);
        controllerWaitForLockFree();
        toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1]);
        await toBeScheduledIRs # {};

        SchedulerMechanism:
        while TRUE do
            controllerWaitForLockFree();
            whichStepToFail(3);
            if (stepOfFailure # 1) then
                nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                if (stepOfFailure # 2) then
                    controllerStateNIB[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
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
                    modifiedEnqueue();
                    toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                    if (stepOfFailure # 2) then
                        controllerStateNIB[self] := [type |-> NO_STATUS];    
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
        if(controllerStateNIB[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] := 
                SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] \ {controllerStateNIB[self].next};
        end if;
        goto ControllerSeqProc;
    end process

    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = 0, rowIndex = -1, rowRemove = -1, stepOfFailure = 0; 
    begin
    ControllerThread:
    while TRUE do
        await moduleIsUp(self);
        await IRQueueNIB # <<>>;
        await canWorkerThreadContinue(self[1], self);
        controllerWaitForLockFree();

        modifiedRead();
        whichStepToFail(2);
        if (stepOfFailure = 1) then
            controllerModuleFails();
            goto ControllerThreadStateReconciliation;
        else 
            controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent];
            if (stepOfFailure = 2) then
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            else    
                if idThreadWorkingOnIR[nextIRToSent] = IR_UNLOCK then
                    await threadWithLowerIDGetsTheLock(self[1], self, nextIRToSent, IRQueueNIB); \* For Reducing Space
                    idThreadWorkingOnIR[nextIRToSent] := self[2]
                else
                    ControllerThreadRemoveQueue1: 
                        controllerWaitForLockFree();
                        modifiedRemove();
                        goto ControllerThread;    
                end if;
            end if;
        end if;

        ControllerThreadSendIR:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                if ~isSwitchSuspended(IR2SW[nextIRToSent]) /\ IRStatus[nextIRToSent] = IR_NONE then
                    IRStatus[nextIRToSent] := IR_SENT;
                    ControllerThreadForwardIR:
                        controllerWaitForLockFree();
                        whichStepToFail(2);
                        if (stepOfFailure # 1) then
                            controllerSendIR(nextIRToSent);
                            if (stepOfFailure # 2) then
                               controllerStateNIB[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRToSent];
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

        WaitForIRToHaveCorrectStatus:  
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then 
                await ~isSwitchSuspended(IR2SW[nextIRToSent]);
            else
                goto ControllerThreadStateReconciliation;
            end if;
            
        ReScheduleifIRNone:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                if IRStatus[nextIRToSent] = IR_NONE then
                    controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent]; 
                    goto ControllerThreadSendIR;
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
            whichStepToFail(3);
            if (stepOfFailure # 1) then 
                SetScheduledIRs[IR2SW[nextIRToSent]] := SetScheduledIRs[IR2SW[nextIRToSent]]\{nextIRToSent};
                if (stepOfFailure # 2) then 
                    controllerStateNIB[self] := [type |-> NO_STATUS];
                    if (stepOfFailure # 3) then 
                        modifiedRemove();
                    end if;
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
        await canWorkerThreadContinue(self[1], self);
        controllerReleaseLock(self);
        if (controllerStateNIB[self].type = STATUS_LOCKING) then
            if (IRStatus[controllerStateNIB[self].next] = IR_SENT) then
                    IRStatus[controllerStateNIB[self].next] := IR_NONE;
            end if;                 
            if (idThreadWorkingOnIR[controllerStateNIB[self].next] = self[2]) then
                idThreadWorkingOnIR[controllerStateNIB[self].next] := IR_UNLOCK;
            end if;        
        elsif (controllerStateNIB[self].type = STATUS_SENT_DONE) then
            SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] := 
                    SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] \cup {controllerStateNIB[self].next};          
            if (idThreadWorkingOnIR[controllerStateNIB[self].next] = self[2]) then
                idThreadWorkingOnIR[controllerStateNIB[self].next] := IR_UNLOCK;
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
                    controllerStateNIB[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
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
                controllerStateNIB[self] := [type |-> NO_STATUS]; 
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
        if (controllerStateNIB[self].type = START_RESET_IR) then
           SwSuspensionStatus[controllerStateNIB[self].sw] := SW_SUSPEND;
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
        assert msg.from = IR2SW[msg.IR];
        assert msg.type \in {INSTALLED_SUCCESSFULLY};
            if msg.type = INSTALLED_SUCCESSFULLY then
                ControllerUpdateIR2:
                    controllerWaitForLockFree(); 
                    controllerModuleFailOrNot();
                    if (controllerSubmoduleFailStat[self] = NotFailed) then
                        FirstInstall[msg.IR] := 1;
                        IRStatus[msg.IR] := IR_DONE;
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
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "12cb0ef3")
\* Process variable stepOfFailure of process controllerSequencer at line 194 col 50 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 253 col 64 changed to stepOfFailure_c
VARIABLES switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
          switch2Controller, FirstInstall, ContProcSet, 
          controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
          dependencyGraph, IR2SW, idThreadWorkingOnIR, controllerStateNIB, 
          IRStatus, SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, 
          switchOrdering, workerThreadRanking, pc

(* define statement *)
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]

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

isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                     /\ IRStatus[y] # IR_DONE
getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                          /\ isDependencySatisfied(x)
                                                          /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                          /\ x \notin SetScheduledIRs[IR2SW[x]]}

isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>)
                                                      /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}
canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                          \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NO_TAG
                                             /\ NoEntryTaggedWith(threadID)
                                             /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
                                                                                                                /\ y.tag = <<CID, x>>
                                                                                 /\ pc[<<CID, x>>] = "ControllerThread"}
threadWithLowerIDGetsTheLock(CID, threadID, nIR, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]:
                                                                                                        z \in setThreadsAttemptingForLock(CID, nIR, IRQueue)})
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

VARIABLES toBeScheduledIRs, nextIR, stepOfFailure_, nextIRToSent, rowIndex, 
          rowRemove, stepOfFailure_c, monitoringEvent, setIRsToReset, resetIR, 
          stepOfFailure, msg, controllerFailedModules

vars == << switchLock, controllerLock, swSeqChangedStatus, controller2Switch, 
           switch2Controller, FirstInstall, ContProcSet, 
           controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
           dependencyGraph, IR2SW, idThreadWorkingOnIR, controllerStateNIB, 
           IRStatus, SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, 
           switchOrdering, workerThreadRanking, pc, toBeScheduledIRs, nextIR, 
           stepOfFailure_, nextIRToSent, rowIndex, rowRemove, stepOfFailure_c, 
           monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, 
           controllerFailedModules >>

ProcSet == (({rc0} \X {CONT_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})) \cup (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        /\ ContProcSet = ((({rc0} \X {CONT_SEQ})) \cup
                            (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup
                            (({ofc0} \X {CONT_EVENT})) \cup
                            (({ofc0} \X {CONT_MONITOR})))
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ IR2SW = (    CHOOSE x \in [1..MaxNumIRs -> SW]:
                    ~\E y, z \in DOMAIN x: /\ y > z
                                           /\ switchOrdering[x[y]] =< switchOrdering[x[z]])
        /\ idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK]
        /\ controllerStateNIB =                      [
                                    x \in ContProcSet |-> [
                                        type |-> NO_STATUS
                                    ]
                                ]
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ switchOrdering = (             CHOOSE x \in [SW -> 1..Cardinality(SW)]:
                             ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ workerThreadRanking = (                  CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]:
                                  ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
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
                           /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1])]
                           /\ toBeScheduledIRs'[self] # {}
                           /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, FirstInstall, 
                                           ContProcSet, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           dependencyGraph, IR2SW, 
                                           idThreadWorkingOnIR, 
                                           controllerStateNIB, IRStatus, 
                                           SwSuspensionStatus, IRQueueNIB, 
                                           SetScheduledIRs, switchOrdering, 
                                           workerThreadRanking, nextIR, 
                                           stepOfFailure_, nextIRToSent, 
                                           rowIndex, rowRemove, 
                                           stepOfFailure_c, monitoringEvent, 
                                           setIRsToReset, resetIR, 
                                           stepOfFailure, msg, 
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
                                             THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_START_SCHEDULING, next |-> nextIR'[self]]]
                                                  /\ IF (stepOfFailure_'[self] # 3)
                                                        THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![IR2SW[nextIR'[self]]] = SetScheduledIRs[IR2SW[nextIR'[self]]] \cup {nextIR'[self]}]
                                                        ELSE /\ TRUE
                                                             /\ UNCHANGED SetScheduledIRs
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << controllerStateNIB, 
                                                                  SetScheduledIRs >>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << controllerStateNIB, 
                                                       SetScheduledIRs, nextIR >>
                            /\ IF (stepOfFailure_'[self] # 0)
                                  THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                       /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                                       /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat >>
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, FirstInstall, 
                                            ContProcSet, dependencyGraph, 
                                            IR2SW, idThreadWorkingOnIR, 
                                            IRStatus, SwSuspensionStatus, 
                                            IRQueueNIB, switchOrdering, 
                                            workerThreadRanking, 
                                            toBeScheduledIRs, nextIRToSent, 
                                            rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, 
                                            controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                             THEN /\ \E num \in 0..2:
                                       stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                             ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                       /\ IF (stepOfFailure_'[self] # 1)
                             THEN /\ IRQueueNIB' =               Append(
                                                       IRQueueNIB, [
                                                           IR |-> nextIR[self],
                                                           tag |-> NO_TAG
                                                       ]
                                                   )
                                  /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
                                  /\ IF (stepOfFailure_'[self] # 2)
                                        THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED controllerStateNIB
                             ELSE /\ TRUE
                                  /\ UNCHANGED << controllerStateNIB, 
                                                  IRQueueNIB, toBeScheduledIRs >>
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
                                       ContProcSet, dependencyGraph, IR2SW, 
                                       idThreadWorkingOnIR, IRStatus, 
                                       SwSuspensionStatus, SetScheduledIRs, 
                                       switchOrdering, workerThreadRanking, 
                                       nextIR, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, 
                                       controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ moduleIsUp(self)
                                          /\ \/ controllerLock = self
                                             \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (controllerStateNIB[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![IR2SW[controllerStateNIB[self].next]] = SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] \ {controllerStateNIB[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
                                          /\ UNCHANGED << switchLock, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          FirstInstall, 
                                                          ContProcSet, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          dependencyGraph, 
                                                          IR2SW, 
                                                          idThreadWorkingOnIR, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          switchOrdering, 
                                                          workerThreadRanking, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
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
                          /\ IRQueueNIB # <<>>
                          /\ canWorkerThreadContinue(self[1], self)
                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                     /\ UNCHANGED << idThreadWorkingOnIR, 
                                                     controllerStateNIB >>
                                ELSE /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent'[self]]]
                                     /\ IF (stepOfFailure_c'[self] = 2)
                                           THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                /\ UNCHANGED idThreadWorkingOnIR
                                           ELSE /\ IF idThreadWorkingOnIR[nextIRToSent'[self]] = IR_UNLOCK
                                                      THEN /\ threadWithLowerIDGetsTheLock(self[1], self, nextIRToSent'[self], IRQueueNIB')
                                                           /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent'[self]] = self[2]]
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveQueue1"]
                                                           /\ UNCHANGED idThreadWorkingOnIR
                                                /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                controllerSubmoduleFailStat >>
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          FirstInstall, ContProcSet, 
                                          dependencyGraph, IR2SW, IRStatus, 
                                          SwSuspensionStatus, SetScheduledIRs, 
                                          switchOrdering, workerThreadRanking, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, rowRemove, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, 
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
                                      THEN /\ IF ~isSwitchSuspended(IR2SW[nextIRToSent[self]]) /\ IRStatus[nextIRToSent[self]] = IR_NONE
                                                 THEN /\ IRStatus' = [IRStatus EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForIRToHaveCorrectStatus"]
                                                      /\ UNCHANGED IRStatus
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                           /\ UNCHANGED IRStatus
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                FirstInstall, ContProcSet, 
                                                dependencyGraph, IR2SW, 
                                                idThreadWorkingOnIR, 
                                                controllerStateNIB, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, 
                                                switchOrdering, 
                                                workerThreadRanking, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..2:
                                                   stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure_c'[self] # 1)
                                         THEN /\ controller2Switch' = [controller2Switch EXCEPT ![IR2SW[nextIRToSent[self]]] =                                Append(
                                                                                                                                   controller2Switch[IR2SW[nextIRToSent[self]]],
                                                                                                                                   [
                                                                                                                                       type |-> INSTALL_FLOW,
                                                                                                                                       to |-> IR2SW[nextIRToSent[self]],
                                                                                                                                       IR |-> nextIRToSent[self]
                                                                                                                                   ]
                                                                                                                               )]
                                              /\ IF whichSwitchModel(IR2SW[nextIRToSent[self]]) = SW_COMPLEX_MODEL
                                                    THEN /\ switchLock' = <<NIC_ASIC_IN, IR2SW[nextIRToSent[self]]>>
                                                    ELSE /\ switchLock' = <<SW_SIMPLE_ID, IR2SW[nextIRToSent[self]]>>
                                              /\ IF (stepOfFailure_c'[self] # 2)
                                                    THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_SENT_DONE, next |-> nextIRToSent[self]]]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED controllerStateNIB
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << switchLock, 
                                                              controller2Switch, 
                                                              controllerStateNIB >>
                                   /\ IF (stepOfFailure_c'[self] # 0)
                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForIRToHaveCorrectStatus"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ UNCHANGED << controllerLock, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   FirstInstall, ContProcSet, 
                                                   dependencyGraph, IR2SW, 
                                                   idThreadWorkingOnIR, 
                                                   IRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   switchOrdering, 
                                                   workerThreadRanking, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, 
                                                   controllerFailedModules >>

WaitForIRToHaveCorrectStatus(self) == /\ pc[self] = "WaitForIRToHaveCorrectStatus"
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
                                            THEN /\ ~isSwitchSuspended(IR2SW[nextIRToSent[self]])
                                                 /\ pc' = [pc EXCEPT ![self] = "ReScheduleifIRNone"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      FirstInstall, 
                                                      ContProcSet, 
                                                      dependencyGraph, IR2SW, 
                                                      idThreadWorkingOnIR, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      switchOrdering, 
                                                      workerThreadRanking, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
                                                      controllerFailedModules >>

ReScheduleifIRNone(self) == /\ pc[self] = "ReScheduleifIRNone"
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
                                  THEN /\ IF IRStatus[nextIRToSent[self]] = IR_NONE
                                             THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent[self]]]
                                                  /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                                  /\ UNCHANGED controllerStateNIB
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                       /\ UNCHANGED controllerStateNIB
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, FirstInstall, 
                                            ContProcSet, dependencyGraph, 
                                            IR2SW, idThreadWorkingOnIR, 
                                            IRStatus, SwSuspensionStatus, 
                                            IRQueueNIB, SetScheduledIRs, 
                                            switchOrdering, 
                                            workerThreadRanking, 
                                            toBeScheduledIRs, nextIR, 
                                            stepOfFailure_, nextIRToSent, 
                                            rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, 
                                            controllerFailedModules >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
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
                                                         FirstInstall, 
                                                         ContProcSet, 
                                                         dependencyGraph, 
                                                         IR2SW, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         switchOrdering, 
                                                         workerThreadRanking, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         controllerFailedModules >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                        THEN /\ \E num \in 0..3:
                                                  stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                        ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                  /\ IF (stepOfFailure_c'[self] # 1)
                                        THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![IR2SW[nextIRToSent[self]]] = SetScheduledIRs[IR2SW[nextIRToSent[self]]]\{nextIRToSent[self]}]
                                             /\ IF (stepOfFailure_c'[self] # 2)
                                                   THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                        /\ IF (stepOfFailure_c'[self] # 3)
                                                              THEN /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self)]
                                                                   /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << IRQueueNIB, 
                                                                                   rowRemove >>
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << controllerStateNIB, 
                                                                        IRQueueNIB, 
                                                                        rowRemove >>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << controllerStateNIB, 
                                                             IRQueueNIB, 
                                                             SetScheduledIRs, 
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
                                                  FirstInstall, ContProcSet, 
                                                  dependencyGraph, IR2SW, 
                                                  idThreadWorkingOnIR, 
                                                  IRStatus, SwSuspensionStatus, 
                                                  switchOrdering, 
                                                  workerThreadRanking, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, nextIRToSent, 
                                                  rowIndex, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, 
                                                  controllerFailedModules >>

ControllerThreadRemoveQueue1(self) == /\ pc[self] = "ControllerThreadRemoveQueue1"
                                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self)]
                                      /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      FirstInstall, 
                                                      ContProcSet, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      dependencyGraph, IR2SW, 
                                                      idThreadWorkingOnIR, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      SetScheduledIRs, 
                                                      switchOrdering, 
                                                      workerThreadRanking, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      nextIRToSent, rowIndex, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
                                                      controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ moduleIsUp(self)
                                             /\ IRQueueNIB # <<>>
                                             /\ canWorkerThreadContinue(self[1], self)
                                             /\ \/ controllerLock = self
                                                \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (controllerStateNIB[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (IRStatus[controllerStateNIB[self].next] = IR_SENT)
                                                              THEN /\ IRStatus' = [IRStatus EXCEPT ![controllerStateNIB[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED IRStatus
                                                        /\ IF (idThreadWorkingOnIR[controllerStateNIB[self].next] = self[2])
                                                              THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![controllerStateNIB[self].next] = IR_UNLOCK]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                        /\ UNCHANGED SetScheduledIRs
                                                   ELSE /\ IF (controllerStateNIB[self].type = STATUS_SENT_DONE)
                                                              THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![IR2SW[controllerStateNIB[self].next]] = SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] \cup {controllerStateNIB[self].next}]
                                                                   /\ IF (idThreadWorkingOnIR[controllerStateNIB[self].next] = self[2])
                                                                         THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![controllerStateNIB[self].next] = IR_UNLOCK]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED idThreadWorkingOnIR
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << idThreadWorkingOnIR, 
                                                                                   SetScheduledIRs >>
                                                        /\ UNCHANGED IRStatus
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << switchLock, 
                                                             swSeqChangedStatus, 
                                                             controller2Switch, 
                                                             switch2Controller, 
                                                             FirstInstall, 
                                                             ContProcSet, 
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             dependencyGraph, 
                                                             IR2SW, 
                                                             controllerStateNIB, 
                                                             SwSuspensionStatus, 
                                                             IRQueueNIB, 
                                                             switchOrdering, 
                                                             workerThreadRanking, 
                                                             toBeScheduledIRs, 
                                                             nextIR, 
                                                             stepOfFailure_, 
                                                             nextIRToSent, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             stepOfFailure_c, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, 
                                                             stepOfFailure, 
                                                             msg, 
                                                             controllerFailedModules >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ WaitForIRToHaveCorrectStatus(self)
                                    \/ ReScheduleifIRNone(self)
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadRemoveQueue1(self)
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
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    FirstInstall, ContProcSet, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    dependencyGraph, IR2SW, 
                                                    idThreadWorkingOnIR, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    switchOrdering, 
                                                    workerThreadRanking, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
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
                                                         THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                              /\ IF (stepOfFailure'[self] # 2)
                                                                    THEN /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED swSeqChangedStatus
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << swSeqChangedStatus, 
                                                                              controllerStateNIB >>
                                                   /\ IF (stepOfFailure'[self] # 0)
                                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                              controllerSubmoduleFailStat >>
                                                   /\ UNCHANGED << switchLock, 
                                                                   controllerLock, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   FirstInstall, 
                                                                   ContProcSet, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   idThreadWorkingOnIR, 
                                                                   IRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
                                                                   switchOrdering, 
                                                                   workerThreadRanking, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
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
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, FirstInstall, 
                                             ContProcSet, dependencyGraph, 
                                             IR2SW, idThreadWorkingOnIR, 
                                             controllerStateNIB, IRStatus, 
                                             IRQueueNIB, SetScheduledIRs, 
                                             switchOrdering, 
                                             workerThreadRanking, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, nextIRToSent, 
                                             rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, 
                                             controllerFailedModules >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..2:
                                                   stepOfFailure' = [stepOfFailure EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure' = [stepOfFailure EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure'[self] # 1)
                                         THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                              /\ IF (stepOfFailure'[self] # 2)
                                                    THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED SwSuspensionStatus
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controllerStateNIB, 
                                                              SwSuspensionStatus >>
                                   /\ IF (stepOfFailure'[self] # 0)
                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   FirstInstall, ContProcSet, 
                                                   dependencyGraph, IR2SW, 
                                                   idThreadWorkingOnIR, 
                                                   IRStatus, IRQueueNIB, 
                                                   SetScheduledIRs, 
                                                   switchOrdering, 
                                                   workerThreadRanking, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
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
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLock, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          FirstInstall, 
                                                          ContProcSet, 
                                                          dependencyGraph, 
                                                          IR2SW, 
                                                          idThreadWorkingOnIR, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          SetScheduledIRs, 
                                                          switchOrdering, 
                                                          workerThreadRanking, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
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
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, FirstInstall, 
                                           ContProcSet, dependencyGraph, IR2SW, 
                                           idThreadWorkingOnIR, 
                                           controllerStateNIB, IRStatus, 
                                           SwSuspensionStatus, IRQueueNIB, 
                                           SetScheduledIRs, switchOrdering, 
                                           workerThreadRanking, 
                                           toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, nextIRToSent, 
                                           rowIndex, rowRemove, 
                                           stepOfFailure_c, monitoringEvent, 
                                           resetIR, stepOfFailure, msg, 
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
                     /\ UNCHANGED << switchLock, controllerLock, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, FirstInstall, 
                                     ContProcSet, dependencyGraph, IR2SW, 
                                     idThreadWorkingOnIR, controllerStateNIB, 
                                     SwSuspensionStatus, IRQueueNIB, 
                                     SetScheduledIRs, switchOrdering, 
                                     workerThreadRanking, toBeScheduledIRs, 
                                     nextIR, stepOfFailure_, nextIRToSent, 
                                     rowIndex, rowRemove, stepOfFailure_c, 
                                     monitoringEvent, stepOfFailure, msg, 
                                     controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus # <<>>
                                                   /\ \/ controllerLock = self
                                                      \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (controllerStateNIB[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![controllerStateNIB[self].sw] = SW_SUSPEND]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED SwSuspensionStatus
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   FirstInstall, 
                                                                   ContProcSet, 
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   idThreadWorkingOnIR, 
                                                                   controllerStateNIB, 
                                                                   IRStatus, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
                                                                   switchOrdering, 
                                                                   workerThreadRanking, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
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
                                       /\ Assert(msg'[self].from = IR2SW[msg'[self].IR], 
                                                 "Failure of assertion at line 493, column 9.")
                                       /\ Assert(msg'[self].type \in {INSTALLED_SUCCESSFULLY}, 
                                                 "Failure of assertion at line 494, column 9.")
                                       /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIR2"]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 505, column 18.")
                                                  /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                       /\ UNCHANGED << switchLock, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       FirstInstall, 
                                                       ContProcSet, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       dependencyGraph, IR2SW, 
                                                       idThreadWorkingOnIR, 
                                                       controllerStateNIB, 
                                                       IRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       switchOrdering, 
                                                       workerThreadRanking, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       nextIRToSent, rowIndex, 
                                                       rowRemove, 
                                                       stepOfFailure_c, 
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
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         FirstInstall, 
                                                         ContProcSet, 
                                                         dependencyGraph, 
                                                         IR2SW, 
                                                         idThreadWorkingOnIR, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         switchOrdering, 
                                                         workerThreadRanking, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
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
                                   THEN /\ FirstInstall' = [FirstInstall EXCEPT ![msg[self].IR] = 1]
                                        /\ IRStatus' = [IRStatus EXCEPT ![msg[self].IR] = IR_DONE]
                                        /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                        /\ UNCHANGED << FirstInstall, IRStatus >>
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, ContProcSet, 
                                             dependencyGraph, IR2SW, 
                                             idThreadWorkingOnIR, 
                                             controllerStateNIB, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, switchOrdering, 
                                             workerThreadRanking, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, nextIRToSent, 
                                             rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, 
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
                                               "Failure of assertion at line 528, column 13.")
                                     /\ controllerLock' = module
                                     /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![module] = NotFailed]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerWatchDogProc"]
                                /\ UNCHANGED << switchLock, swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                FirstInstall, ContProcSet, 
                                                controllerSubmoduleFailNum, 
                                                dependencyGraph, IR2SW, 
                                                idThreadWorkingOnIR, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, 
                                                switchOrdering, 
                                                workerThreadRanking, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg >>

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
=============================================================================

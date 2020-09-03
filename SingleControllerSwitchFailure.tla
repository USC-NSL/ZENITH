--------------------------- MODULE SwitchFailure ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS SW, c0, c1, CONTROLLER_THREAD_POOL, MaxNumIRs, 
          NotFailed, Failed, MAX_NUM_SW_FAILURE, IR_NONE, IR_SENT, IR_PENDING, IR_DONE, SW_SUSPEND, SW_RUN,
          RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, SW_UP, SW_DOWN, KEEP_ALIVE, IR_RECONCILE,
          NIC_ASIC_IN, NIC_ASIC_OUT, OFA_IN, OFA_OUT, INSTALLER, SW_FAILURE_PROC, SW_RESOLVE_PROC,
          CONT_SEQ, CONT_MONITOR, CONT_EVENT, NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN,
          INSTALLER_UP, RECONCILIATION_REQUEST, RECONCILIATION_RESPONSE, INSTALL_FLOW, STATUS_NONE

(*--fair algorithm stateConsistency
    variables \*********** Switch -- Controller Shared Vars *************
              swSeqChangedStatus = <<>>,
              \**************** Switch Global Vars **********************
              switchStatus = [x\in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed, ofa |-> NotFailed, installer |-> NotFailed]],  
              installedIRs = <<>>, \*switch
              failedTimes = [x \in SW |-> 0],
              NicAsic2OfaBuff = [x \in SW |-> <<>>], 
              Ofa2NicAsicBuff = [x \in SW |-> <<>>],
              Ofa2InstallerBuff = [x \in SW |-> <<>>],
              \* OfaCacheReceived = [x \in SW |-> {}],
              \* OfaCacheInstalled = [x \in SW |-> {}],
              Installer2OfaBuff = [x \in SW |-> <<>>],
              TCAM = [x \in SW |-> <<>>],
              \*OfaReceivedConfirmation = [x \in SW |-> <<>>], 
              controlMsgCounter = [x \in SW |-> 0],
              \**************** Switch -- Controller Medium ************
              controller2Switch = [x\in SW |-> <<>>],
              switch2Controller = <<>>,
              \**************** Controller Global Vars ******************
              controllerState = [c0 |-> "primary", c1 |-> "backup"],
              IR2SW \in [1..MaxNumIRs -> SW], 
              controllerThreadPoolIRQueue = [y \in {c0, c1} |-> <<>>], 
              IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
              SwSuspensionStatus = [x \in SW |-> SW_RUN],
              lastScheduledThread = 0,
              SetScheduledIRs = [x \in {c0, c1} |-> [y \in SW |-> {}]],
              \**************** Dependency Graph Definition **************
              dependencyGraph \in PlausibleDependencySet
    define
    
        RECURSIVE Paths(_, _)
        Paths(n, G) ==  IF n = 1
                        THEN 
                          G
                        ELSE
                            LET nextVs(p) == { e[2] : e \in {e \in G : e[1] = p[Len(p)]} }
                                nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
                            IN
                            UNION {nextPaths(p) : p \in Paths(n-1, G)} \cup Paths(n-1, G)
        
        S == 0..MaxNumIRs
        PlausibleDependencySet == {x \in SUBSET (S \X S): /\ ~\E y \in 0..MaxNumIRs: <<y, y>> \in x
                                                          /\ ~\E y, z \in 0..MaxNumIRs: /\  <<y, z>> \in x 
                                                                                        /\  <<z, y>> \in x
                                                          /\ x # {}
                                                          /\ ~\E y \in 1..MaxNumIRs: <<0, y>> \in x
                                                          /\ \A p \in Paths(MaxNumIRs, x): \/ Len(p) = 1
                                                                                           \/ p[1] # p[Len(p)]}
    
       \* SendInstruction(swID) == canUpdate[swID] = 1
        max(set) == CHOOSE x \in set: \A y \in set: x \geq y
        min(set) == CHOOSE x \in set: \A y \in set: x \leq y
       \* RECURSIVE GetFirstNofSet(_, _)
       \* GetFirstNofSet(set, N) == IF Cardinality(set) <= N 
       \*                             THEN set
       \*                             ELSE IF N = 1 THEN {min(set)}
       \*                             ELSE {min(set)} \union GetFirstNofSet(set \ {min(set)}, N-1) 
                                    
       \* CheckSetSWUpdated(set) == \A x \in set: switchState[x] = Updated
       \* maxUpdateRcv == CHOOSE x \in SW: /\ switchState[x] = Updated
       \*                                  /\ (\A y \in 1..x: switchState[y] = Updated)
        controllerIsMaster(controllerID) == IF controllerID = c0 THEN controllerState.c0 = "primary"
                                                                 ELSE controllerState.c1 = "primary"
       \* getFailed(set) == {x \in set: canUpdate[x] = 0}
       \* NoMorePossibleUpdates() == Cardinality({x \in SW: \A y \in Ofa2InstallerBuff:}) = 0 \*should complete this
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        returnSwitchFailedElements(sw) == {x\in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                                                         /\ \/ switchStatus[sw].cpu = NotFailed
                                                                            \/ x \notin {"ofa", "installer"}}
        returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}
        swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed 
        swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                                  /\ switchStatus[sw].ofa = NotFailed
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
        isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                             /\ IRStatus[y] # IR_DONE
        getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                                  /\ isDependencySatisfied(x)
                                                                  /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRs[CID][IR2SW[x]]}
        getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: IR2SW[x] = SID}
                                                               
        \* getIRToSentNext(TID) == controllerThreadPoolIRQueue[TID[1]][TID[2]]
        \*                                    [CHOOSE x \in DOMAIN controllerThreadPoolIRQueue[TID[1]][TID[2]]: 
        \*                                        ~\E y \in DOMAIN controllerThreadPoolIRQueue[TID[1]][TID[2]]: /\ y < x
        \*                                                                                                      /\ IRStatus[controllerThreadPoolIRQueue[TID[1]][TID[2]][y]] = IR_NONE]
        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                        /\ swSeqChangedStatus[x].num > monEvent.num
        installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerFailedOrNot" 
        ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaInFailedOrNot"
                                 /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaOutFailedOrNot"
        nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchNicAsicInFailedOrNot"
                                     /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchNicAsicOutFailedOrNot"
        isFinished == \A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE
        shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                                     \/ monEvent.type = NIC_ASIC_DOWN
                                     \/ /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.status.installerStatus = INSTALLER_DOWN
        canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                           /\ monEvent.status.installerStatus = INSTALLER_UP
        \*getIRSetToReconcile(SID) == {x \in 1..MaxNumIRs: /\ IR2SW[x] = SID
        \*                                                 /\ IRStatus[x] \notin {IR_DONE, IR_NONE, IR_SUSPEND}}
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ IR2SW[x] = SID
                                                     /\ IRStatus[x] \notin {IR_DONE, IR_NONE}}
        getIRSetToSuspend(CID, SID) == {x \in SetScheduledIRs[CID][SID]: IRStatus[x] = IR_NONE}
        getInstallerStatus(stat) == IF stat = NotFailed 
                                    THEN INSTALLER_UP
                                    ELSE INSTALLER_DOWN
                                   
    end define  
 
    
    (*macro switchFailure()
    begin
        if failedTimes[self] < MAX_SW_FAILURE then 
            either 
                skip;
            or
                switchStatus[self].cpu := Failed;
                failedTimes[self] := failedTimes[self] + 1;
                NicAsic2OfaBuff[self] := <<>>;
                Ofa2InstallerBuff[self] := <<>>;
                if swMiddleOfSwitchProcess(self) \/ swMiddleOfSwitchSucceed(self) then 
                    goto Switch;
                end if;
            or
                switchStatus[self].nicAsic := Failed;
                failedTimes[self] := failedTimes[self] + 1;
                controller2SwitchIRs[self] := <<>>;
                if swMiddleOfRecevingPacket(self) then goto SwitchF1; end if;
            or
                switchStatus[self].installer := Failed;
                failedTimes[self] := failedTimes[self] + 1;
                if swMiddleOfSwitchSucceed(self) then goto Switch; end if;
            or  
                switchStatus[self].ofa := Failed;
                failedTimes[self] := failedTimes[self] + 1;
                if swMiddleOfSwitchProcess(self) then goto SwitchF3; end if; 
            end either;
        end if;
    end macro;
    
    macro resolveSwitchFailure()
    begin
        if partiallyFailed(self) then
            either 
                failedElems := returnSwitchFailedElements(self);
                if Cardinality(failedElems) > 0 then
                    with elem \in failedElems do
                        switchStatus[self][elem] := NotFailed
                        CASE elem = "cpu" -> resolveCpuFailure()
                          [] elem = "nicAsic" -> resolveNicAsicFailure()
                          [] elem = "ofa" -> resolveOfaFailure()
                          [] elem = "installer" -> resolveInstallerFailure()
                    end with;      
                end if; 
            or
                skip;
            end either;
        end if;         
    end macro   
    *)
    
    
    \* ------------------------------------------------------------------
    \* -                   Switches (Macros)                            -
    \* ------------------------------------------------------------------
    
    \* ======= NIC/ASIC Failure ========
    macro nicAsicFailure()
    begin
        switchStatus[self[2]].nicAsic := Failed;
        failedTimes[self[2]] := failedTimes[self[2]] + 1;
        controller2Switch[self[2]] := <<>>;
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
        statusMsg := [type |-> NIC_ASIC_DOWN, 
                      swID |-> self[2],
                      num |-> controlMsgCounter[self[2]]];
        swSeqChangedStatus := Append(swSeqChangedStatus, statusMsg);              
    end macro
    \* =================================
    
    \* === Resolving NIC/ASIC Failure ==
    macro resolveNicAsicFailure()
    begin
        await nicAsicStartingMode(self[2]);
        switchStatus[self[2]].nicAsic := NotFailed;
        controller2Switch[self[2]] := <<>>;  
        if switchStatus[self[2]].ofa = Failed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusResolveMsg := [type |-> OFA_DOWN, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]]];
        else
            
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)]];
        end if;
        swSeqChangedStatus := Append(swSeqChangedStatus, statusResolveMsg);            
    end macro
    \* =================================
    
    \* ======= CPU Failure =============
    macro cpuFailure()
    begin
        switchStatus[self[2]].cpu := Failed || switchStatus[self[2]].ofa := Failed || switchStatus[self[2]].installer := Failed;
        failedTimes[self[2]] := failedTimes[self[2]] + 1;
        NicAsic2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2NicAsicBuff[self[2]] := <<>>;        
        \*OfaCacheReceived[self[2]] := {};
        \*OfaCacheInstalled[self[2]] := {};
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusMsg := [type |-> OFA_DOWN, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]]];
            swSeqChangedStatus := Append(swSeqChangedStatus, statusMsg);
        end if;
    end macro
    \* =================================
    
    \* ===== Resolving CPU Failure =====
    macro resolveCpuFailure()
    begin
        await ofaStartingMode(self[2]) /\ installerInStartingMode(self[2]);
        switchStatus[self[2]].cpu := NotFailed || switchStatus[self[2]].ofa := NotFailed || switchStatus[self[2]].installer := NotFailed;
        NicAsic2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2NicAsicBuff[self[2]] := <<>>;       
        \*OfaCacheReceived[self[2]] := {};
        \*OfaCacheInstalled[self[2]] := {};
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)]]; 
            swSeqChangedStatus := Append(swSeqChangedStatus, statusResolveMsg);    
        end if;
    end macro
    \* =================================    
    
    \* ======= OFA Failure =============
    macro ofaFailure()
    begin
        switchStatus[self[2]].ofa := Failed;
        assert switchStatus[self[2]].cpu = NotFailed;
        failedTimes[self[2]] := failedTimes[self[2]] + 1;       
        \*OfaCacheReceived[self[2]] := {};
        \*OfaCacheInstalled[self[2]] := {};
        if switchStatus[self[2]].nicAsic = NotFailed then  
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
            statusMsg := [type |-> OFA_DOWN, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]]];
            swSeqChangedStatus := Append(swSeqChangedStatus, statusMsg);    
        end if;
    end macro
    \* ================================= 
 
    \* ===== Resolving OFA Failure =====
    macro resolveOfaFailure()
    begin
        await ofaStartingMode(self[2]);
        assert switchStatus[self[2]].cpu = NotFailed;
        switchStatus[self[2]].ofa := NotFailed;          
        \*OfaCacheReceived[self[2]] := {};
        \*OfaCacheInstalled[self[2]] := {}; 
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)]];
            
            swSeqChangedStatus := Append(swSeqChangedStatus, statusResolveMsg);             
        end if;
    end macro
    \* =================================  
    
    \* ======= Installer Failure =======
    macro installerFailure()
    begin
        switchStatus[self[2]].installer := Failed;
        assert switchStatus[self[2]].cpu = NotFailed;
        failedTimes[self[2]] := failedTimes[self[2]] + 1;        
        if switchStatus[self[2]].nicAsic = NotFailed /\ switchStatus[self[2]].ofa = NotFailed then
            assert switchStatus[self[2]].installer = Failed;
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;    
            statusMsg := [type |-> KEEP_ALIVE, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]],
                          status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)]];
            swSeqChangedStatus := Append(swSeqChangedStatus, statusMsg);
        end if;
    end macro
    \* =================================
    
    \* == Resolving Installer Failure ==
    macro resolveInstallerFailure()
    begin
        await installerInStartingMode(self[2]);
        assert switchStatus[self[2]].cpu = NotFailed;
        switchStatus[self[2]].installer := NotFailed;         
        if switchStatus[self[2]].nicAsic = NotFailed /\ switchStatus[self[2]].ofa = NotFailed then
            assert switchStatus[self[2]].installer = NotFailed;
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;    
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)]];       
            swSeqChangedStatus := Append(swSeqChangedStatus, statusResolveMsg);    
        end if;
    end macro
    \* =================================
    
    
    \* ------------------------------------------------------------------
    \* -                   Controller (Macros)                          -
    \* ------------------------------------------------------------------
        
    macro failover()
    begin
        if (self = c0 /\ controllerState.c0 = "primary")
        then
            either
                controllerState.c0 := "failed" || controllerState.c1 := "primary";
                goto EndCont;
            or
                skip;
            end either;
        end if; 
    end macro;
    
    macro controllerSendIR(s)
    begin
        controller2Switch[IR2SW[s]] := Append(controller2Switch[IR2SW[s]], [type |-> INSTALL_FLOW,
                                                                            to |-> IR2SW[s],
                                                                            IR |-> s]);
    end macro
    
    \* ------------------------------------------------------------------
    \* -                 Switch (Procedures)                        -
    \* ------------------------------------------------------------------ 
    
    \* == Install Flow Entry ==
    procedure ofaInstallFlowEntry(ofaInIR = 0)
    begin
    (*SendRcvConfirmationToController:
    if swOFACanProcessIRs(self[2]) then
        Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> RECEIVED_SUCCESSFULLY, 
                                                                      from |-> self[2],
                                                                      IR |-> ofaInIR]);
        \*OfaCacheReceived[self[2]] := OfaCacheReceived[self[2]] \cup {ofaInIR};
    else
        goto EndInstallFlowEntry;
    end if;*)
    \* Process packet
    SwitchOFAInsert2InstallerBuff:
    if swOFACanProcessIRs(self[2]) then
        Ofa2InstallerBuff[self[2]] := Append(Ofa2InstallerBuff[self[2]], ofaInIR);
    else
        goto EndInstallFlowEntry;
    end if;
    EndInstallFlowEntry:
    return
    end procedure
    
    \* == Respond To Reconciliation Request ==
    (* procedure ofaProcessReconcileRequest(ofaReconcileIR = 0)
    begin
    OfaLookAtInstalledCache:
    if ~swOFACanProcessIRs(self[2]) then
        goto EndReconcileReq;
    elsif ofaReconcileIR \in OfaCacheInstalled[self[2]] then
        Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> RECONCILIATION_RESPONSE,
                                                                      from |-> self[2],
                                                                      IR |-> ofaReconcileIR,
                                                                      status |-> INSTALLED_SUCCESSFULLY]);
        goto EndReconcileReq;
    end if;
    OfaLookAtReceivedCache:
    if ~swOFACanProcessIRs(self[2]) then
        goto EndReconcileReq;
    elsif ofaReconcileIR \in OfaCacheReceived[self[2]] then
        Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> RECONCILIATION_RESPONSE,
                                                                      from |-> self[2],
                                                                      IR |-> ofaReconcileIR,
                                                                      status |-> RECEIVED_SUCCESSFULLY]);    
        goto EndReconcileReq;
    end if;    
    OfaNoAvailableStatus:
    if swOFACanProcessIRs(self[2]) then
        Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> RECONCILIATION_RESPONSE,
                                                                      from |-> self[2],
                                                                      IR |-> ofaReconcileIR,
                                                                      status |-> STATUS_NONE]);    
    end if;
    EndReconcileReq:
    return;
    end procedure *)
    \* ------------------------------------------------------------------
    \* -                 Controller (Procedures)                        -
    \* ------------------------------------------------------------------ 
    
    procedure scheduleIRs(setIRs = {})
    variables nextThread = lastScheduledThread, nextIR = 0
    begin
    SchedulerMechanism:
    while setIRs # {} /\ controllerIsMaster(self[1]) do
        \*lastScheduledThread := 1 + (lastScheduledThread% MAX_CONT_THREAD_POOL_SIZE);
        nextIR := CHOOSE x \in setIRs: TRUE;
        assert IRStatus[nextIR] \in {IR_NONE, IR_DONE};
               \*\/ /\ IRStatus[nextIR] = IR_SUSPEND
               \*   /\ SwSuspensionStatus[IR2SW[nextIR]] = SW_RUN;
        AddToScheduleIRSet: 
            assert nextIR \notin SetScheduledIRs[self[1]][IR2SW[nextIR]];
            SetScheduledIRs[self[1]][IR2SW[nextIR]] := SetScheduledIRs[self[1]][IR2SW[nextIR]] \cup {nextIR};
        ScheduleTheIR:
            controllerThreadPoolIRQueue[self[1]] := Append(controllerThreadPoolIRQueue[self[1]], nextIR);
            setIRs := setIRs\{nextIR};        
    end while;
    return;
    end procedure
    
   (* procedure reconcileStateWithRecoveredSW(recoveredSwitchID = 0)
    variables setIRsToCheck = {}, reconcileIR = 0;
    begin
    getIRsToBeChecked:
        setIRsToCheck := getIRSetToReconcile(recoveredSwitchID);
    sendReconcileRequest:
    while setIRsToCheck # {} do
        reconcileIR := CHOOSE x \in setIRsToCheck: TRUE;
        setIRsToCheck := setIRsToCheck \ {reconcileIR};
        assert IRStatus[reconcileIR] # IR_DONE;
        ControllerUpdateIRStatAfterReconciliationReq: IRStatus[reconcileIR] := IR_RECONCILE;
        ControllerSendRequest: 
            controller2Switch[recoveredSwitchID] := Append(controller2Switch[recoveredSwitchID], [type |-> RECONCILIATION_REQUEST, 
                                                                                                  to |-> recoveredSwitchID, 
                                                                                                  IR |-> reconcileIR]);
    end while;
    return;    
    end procedure *)
    
    procedure resetStateWithRecoveredSW(switchIDToReset = 0)
    variables setIRsToReset = {}, resetIR = 0
    begin
    getIRsToBeChecked:
        setIRsToReset := getIRSetToReset(switchIDToReset);
    ResetAllIRs:
    while setIRsToReset # {} do
        resetIR := CHOOSE x \in setIRsToReset: TRUE;
        setIRsToReset := setIRsToReset \ {resetIR};
        assert IRStatus[resetIR] \notin {IR_NONE};
        ControllerResetIRStatAfterRecovery: 
            if IRStatus[resetIR] # IR_DONE then
                IRStatus[resetIR] := IR_NONE;
            end if;
    end while;
    return;    
    
    end procedure
    
 (*   procedure suspendInSchedulingIRs(switchIDToSuspend = 0)
    variables setIRsToSuspend = {}, suspendedIR = 0;
    begin
    getIRsToBeSuspended:
        setIRsToSuspend := getIRSetToSuspend(self[1], switchIDToSuspend);
    suspendIRs:
    while setIRsToSuspend # {} do
        suspendedIR := CHOOSE x \in setIRsToSuspend: TRUE;
        setIRsToSuspend := setIRsToSuspend \ {suspendedIR}; 
        ChangeStatusIRToSuspend: IRStatus[suspendedIR] := IR_SUSPEND;
    end while;
    return;
    end procedure
    *)
(*    procedure freeSuspendedIRs(suspendedSwitchID = 0)
    variable toBeFreedIR = 0;
    begin
    freeIR:
    while suspendedIRs[suspendedSwitchID] # {} do
        toBeFreedIR := CHOOSE x \in suspendedIRs[suspendedSwitchID]:TRUE;
        SwSuspensionStatus[toBeFreedIR] := IR_RUN;
        suspendedIRs[suspendedSwitchID] := suspendedIRs[suspendedSwitchID]\{toBeFreedIR};
    end while
    end procedure
    
    procedure suspendIRs(suspendedSwitchID = 0)
    variable toBeSuspendedIR = 0, setToBeSuspendedIRs = {};
    begin
    getToBeSuspendedIRs:
    setToBeSuspendedIRs := getSetIRsForSwitch(suspendedSwitchID);
    suspendToBeSuspendedIRs:
    while setToBeSuspendedIRs # {} do
        toBeSuspendedIR := CHOOSE x \in setToBeSuspendedIRs: TRUE;
        IRSuspensionStatus[toBeSuspendedIR] := IR_SUSPEND;
        suspendedIRs[suspendedSwitchID] := suspendedIRs[suspendedSwitchID] \cup {toBeSuspendedIR};
    end while;
    end procedure  *)
               
    \* ------------------------------------------------------------------
    \* -                   Switches (Modules)                           -
    \* ------------------------------------------------------------------
    
    \* ======== NIC/ASIC Module ========
    fair process swNicAsicProcPacketIn \in ({NIC_ASIC_IN} \X SW)
    variables ingressIR = [type |-> 0]
    begin    
    SwitchNicAsicInFailedOrNot:
        await swCanReceivePackets(self[2]);
    SwitchRcvPacket:
    while ~isFinished do
        if swCanReceivePackets(self[2]) then
            await Len(controller2Switch[self[2]]) > 0;
            ingressIR := Head(controller2Switch[self[2]]);
            assert \/ ingressIR.type = RECONCILIATION_REQUEST
                   \/ ingressIR.type = INSTALL_FLOW;
            controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        else 
            goto SwitchNicAsicInFailedOrNot;
        end if;
        \* Process packet
        SwitchNicAsicInsertToOfaBuff:
            if swCanReceivePackets(self[2]) then
                NicAsic2OfaBuff[self[2]] := Append(NicAsic2OfaBuff[self[2]], ingressIR);
            else
                goto SwitchNicAsicInFailedOrNot;
            end if;
    end while;
    end process
    
    fair process swNicAsicProcPacketOut \in ({NIC_ASIC_OUT} \X SW)
    variables egressMsg = [type |-> 0]
    begin
    SwitchNicAsicOutFailedOrNot:
        await swCanReceivePackets(self[2]);
    SwitchFromOFAPacket:
    while ~isFinished do
        if swCanReceivePackets(self[2]) then
            await  Len(Ofa2NicAsicBuff[self[2]]) > 0;
            egressMsg := Head(Ofa2NicAsicBuff[self[2]]);
            assert \/ egressMsg.type = INSTALLED_SUCCESSFULLY
                   \/ egressMsg.type = RECEIVED_SUCCESSFULLY
                   \/ egressMsg.type = RECONCILIATION_RESPONSE;
            Ofa2NicAsicBuff[self[2]] := Tail(Ofa2NicAsicBuff[self[2]]);
        else 
            goto SwitchNicAsicOutFailedOrNot;
        end if;
        \* Process Msg
        SwitchNicAsicSendOutMsg:
            if swCanReceivePackets(self[2]) then
                switch2Controller := Append(switch2Controller, egressMsg);
            else
                goto SwitchNicAsicOutFailedOrNot;
            end if;
    end while;
    end process
    \* =================================
    
    \* ========== OFA Module ===========
    fair process ofaModuleProcPacketIn \in ({OFA_IN} \X SW)
    variables ofaInMsg = [type |-> 0]
    begin
    \* OFA process the packets and sends packet to Installer
    SwitchOfaInFailedOrNot:
    await swOFACanProcessIRs(self[2]);
    SwitchOfaProcIn: 
    while ~isFinished do
           if swOFACanProcessIRs(self[2]) then
                await Len(NicAsic2OfaBuff[self[2]]) > 0;
                ofaInMsg := Head(NicAsic2OfaBuff[self[2]]);           
                assert ofaInMsg.to = self[2];
                NicAsic2OfaBuff[self[2]] := Tail(NicAsic2OfaBuff[self[2]]);
           else
                goto SwitchOfaInFailedOrNot;
           end if;
 
           SwitchOfaProcessPacket:
           if ofaInMsg.type = INSTALL_FLOW then
                call ofaInstallFlowEntry(ofaInMsg.IR);
           \*elsif ofaInMsg.type = RECONCILIATION_REQUEST then
           \*     call ofaProcessReconcileRequest(ofaInMsg.IR); 
           else
                assert FALSE;               
           end if;
    end while    
    end process
    
    fair process ofaModuleProcPacketOut \in ({OFA_OUT} \X SW)
    variables ofaOutConfirmation = 0
    begin
    SwitchOfaOutFailedOrNot:
        await swOFACanProcessIRs(self[2]);
    SwitchOfaProcOut:
    while ~isFinished do
        if swOFACanProcessIRs(self[2]) then
            await Installer2OfaBuff[self[2]] # <<>>;
            ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
            Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
        else
            goto SwitchOfaOutFailedOrNot;
        end if;
        
        SendInstallationConfirmation:
            if swOFACanProcessIRs(self[2]) then
                Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                              from |-> self[2],
                                                                              IR |-> ofaOutConfirmation]);
                \* OfaCacheInstalled[self[2]] := OfaCacheInstalled[self[2]] \cup {ofaOutConfirmation};                
            else 
                goto SwitchOfaOutFailedOrNot;
            end if;                                                              
    end while;                                                                      
    end process
    \* =================================
    
    \* ======= Installer Module ========
    fair process installerModuleProc \in ({INSTALLER} \X SW)
    variables installerInIR = 0
    begin
    \* Installer installs the packet into TCAM
    SwitchInstallerFailedOrNot:
        await swCanInstallIRs(self[2]);
    SwitchInstallerProc: 
    while ~isFinished do 
       if swCanInstallIRs(self[2]) then 
            await Len(Ofa2InstallerBuff[self[2]]) > 0;
            installerInIR := Head(Ofa2InstallerBuff[self[2]]);
            Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);
       else
            goto SwitchInstallerFailedOrNot;
       end if;
       \* Process packet
       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then   
                installedIRs := Append(installedIRs, installerInIR);
                TCAM[self[2]] := Append(TCAM[self[2]], installerInIR);
            else
                goto SwitchInstallerFailedOrNot;
            end if;
            
       SwitchInstallerSendConfirmation:
            if swCanInstallIRs(self[2]) then
                Installer2OfaBuff[self[2]] := Append(Installer2OfaBuff[self[2]], installerInIR);
            else
                goto SwitchInstallerFailedOrNot;
            end if;
    end while;
    end process
    \* =================================
    
    \* ======= Failure Proccess=========
    fair process swFailureProc \in ({SW_FAILURE_PROC} \X SW)
    variable statusMsg = <<>>, notFailedSet = {}, failedElem = "";
    begin
    SwitchFailure:
    while failedTimes[self[2]] < MAX_NUM_SW_FAILURE /\ ~isFinished do 
        statusMsg := <<>>;
        notFailedSet := returnSwitchElementsNotFailed(self[2]);
        await notFailedSet # {}; 
        with elem \in notFailedSet do
            failedElem := elem;
        end with;
        
        if failedElem = "cpu" then 
            SwitchCpuFailure: 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                cpuFailure();
        elsif failedElem = "ofa" then 
            SwitchOfaFailure: 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                ofaFailure();
        elsif failedElem = "installer" then 
            SwitchInstallerFailure: 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                installerFailure();
        elsif failedElem = "nicAsic" then 
            SwitchNicAsicFailure: 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                nicAsicFailure();
        else assert FALSE;
        end if;
    end while
    end process
    \* =================================
    
    \* ==== Failure Resolve Process ====
    fair process swResolveFailure \in ({SW_RESOLVE_PROC} \X SW)
    variable failedSet = {}, statusResolveMsg = <<>>, recoveredElem = "";
    begin
    SwitchResolveFailure:
    while ~isFinished do
        statusResolveMsg := <<>>;
        failedSet := returnSwitchFailedElements(self[2]);
        await Cardinality(failedSet) > 0;
        with elem \in failedSet do
            recoveredElem := elem;
        end with;
        
        if recoveredElem = "cpu" then SwitchCpuRecovery: resolveCpuFailure();
        elsif recoveredElem = "nicAsic" then SwitchNicAsicRecovery: resolveNicAsicFailure();
        elsif recoveredElem = "ofa" then SwitchOfaRecovery: resolveOfaFailure();
        elsif recoveredElem = "installer" then SwitchInstallerRecovery: resolveInstallerFailure();
        else assert FALSE;
        end if;
        
    end while
    end process
    \* =================================
    
    \* ------------------------------------------------------------------
    \* -                   Controller (Modules)                         -
    \* ------------------------------------------------------------------
   
    \* ======= Sequencer ========
    fair process controllerSequencer \in ({c0, c1} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}
    begin
    ControllerSeqProc:
    await controllerIsMaster(self[1]);
    ControllerObj:
    while ~isFinished /\ controllerIsMaster(self[1]) do
        toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1]);
        await toBeScheduledIRs # {};
        call scheduleIRs(toBeScheduledIRs);                                                
    end while;
    end process
    \* ==========================
    
    \* ====== Thread Pool ======= 
    fair process controllerWorkerThreads \in ({c0, c1} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = 0; 
    begin
    ControllerThread:
    await controllerIsMaster(self[1]);
    ControllerThreadSendIRs:
    while ~isFinished /\ controllerIsMaster(self[1]) do
        await controllerThreadPoolIRQueue[self[1]] # <<>>;
        nextIRToSent := Head(controllerThreadPoolIRQueue[self[1]]);
        controllerThreadPoolIRQueue[self[1]] := Tail(controllerThreadPoolIRQueue[self[1]]);        
        ControllerThreadSendIR:
            if ~isSwitchSuspended(IR2SW[nextIRToSent]) /\ IRStatus[nextIRToSent] = IR_NONE then 
                IRStatus[nextIRToSent] := IR_SENT;
                ControllerThreadForwardIR: controllerSendIR(nextIRToSent);
            end if;
        WaitForIRToHaveCorrectStatus:
            await ~isSwitchSuspended(IR2SW[nextIRToSent]);
        \*IRSuspendedScheduleAgain: \* Should be done in one atomic operation 
        \*    if IRStatus[nextIRToSent] = IR_SUSPEND then
        \*        IRStatus[nextIRToSent] := IR_NONE;
        \*    end if;
        ReScheduleifIRNone:
            if IRStatus[nextIRToSent] = IR_NONE then 
                goto ControllerThreadSendIR;
            end if;
        RemoveFromScheduledIRSet:
            assert nextIRToSent \in SetScheduledIRs[self[1]][IR2SW[nextIRToSent]];
            SetScheduledIRs[self[1]][IR2SW[nextIRToSent]] := SetScheduledIRs[self[1]][IR2SW[nextIRToSent]]\{nextIRToSent};
    end while;
    end process
    \* ==========================
    
    \* ===== Event Handler ======
    fair process controllerEventHandler \in ({c0, c1} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0]
    begin 
    ControllerEventHandlerProc:
    await controllerIsMaster(self[1]);
    ControllerTrack:
    while ~isFinished /\ controllerIsMaster(self[1]) do    
         await swSeqChangedStatus # <<>>;
         monitoringEvent := Head(swSeqChangedStatus);
         swSeqChangedStatus := Tail(swSeqChangedStatus);
         if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            ControllerSuspendSW: SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;        
         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            \*call suspendInSchedulingIRs(monitoringEvent.swID);
            ControllerFreeSuspendedSW: SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
            ControllerCheckIfThisIsLastEvent:
            if ~existsMonitoringEventHigherNum(monitoringEvent) then
                \* call reconcileStateWithRecoveredSW(monitoringEvent.swID);
                call resetStateWithRecoveredSW(monitoringEvent.swID); 
            end if;
         end if;
    end while;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    fair process controllerMonitoringServer \in ({c0, c1} \X {CONT_MONITOR})
    variable msg = [type |-> 0]
    begin
    ControllerMonitorCheckIfMastr:
    await controllerIsMaster(self[1]);
    ControllerMonitorProc:
    while ~isFinished /\ controllerIsMaster(self[1]) do
        await switch2Controller # <<>>;
        msg := Head(switch2Controller);
        switch2Controller := Tail(switch2Controller);
        assert msg.from = IR2SW[msg.IR];
        assert msg.type \in {RECONCILIATION_RESPONSE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY};
        \*if IRStatus[msg.IR] = IR_RECONCILE then 
        \*    if msg.type = RECONCILIATION_RESPONSE then
        \*        if msg.status = INSTALLED_SUCCESSFULLY then
        \*             ControllerUpdateIR3: IRStatus[msg.IR] := IR_DONE; \* Should be done in one atomic operation 
        \*        elsif msg.status = RECEIVED_SUCCESSFULLY then
        \*            ControllerUpdateIR4: IRStatus[msg.IR] := IR_PENDING; \* Should be done in one atomic operation 
        \*        elsif msg.status = STATUS_NONE then
        \*            ControllerUpdateIR5: IRStatus[msg.IR] := IR_NONE; \* Should be done in one atomic operation 
        \*        else assert FALSE;
        \*        end if;
        \*    end if;
        \*else
        (*    if msg.type = RECEIVED_SUCCESSFULLY then 
                ControllerUpdateIR1: 
                    if IRStatus[msg.IR] = IR_SENT then
                        IRStatus[msg.IR] := IR_PENDING; \* Should be done in one atomic operation 
                    end if; *)
            if msg.type = INSTALLED_SUCCESSFULLY then
                ControllerUpdateIR2: IRStatus[msg.IR] := IR_DONE; \* Should be done in one atomic operation
            else assert FALSE;
            end if;
        \*end if; 
    end while
    end process
    \* ==========================
    
    (*fair process c \in {c0, c1}
    variables setNotConsideredIRs={}, latestIRConsidered={}, batchIRs = {}, setIRs = {}, copyBatch={}, s = 0, 
              considered={}, updated={}, numBatch=0, setSwitches={}, copySet={};
    begin
    Controller: skip;
    await controllerIsMaster(self);
    if self = c1 then 
            \* Waiting for all the instructions sent by the previous master controller either fail or install successfully!
            await NoMorePossibleUpdates(setSwitches);
    end if;
    ControllerObj:
    while TRUE do
        \*setSwitches := GetFirstNofSet(SW\1..latestSWConsidered, batchSize);
        setNotConsideredIRs := {x \in controller2SwitchIRs\(1..latestUpdateReceived): x \notin installedIRs};
        batchIRs := GetFirstNofSet(setNotConsideredIRs, batchSize);
        copyBatch := batchIRs;
        if Cardinality(batchIRs) = 0 then goto EndCont; end if;
        check1stbatchForC1:
        if (self = c1 /\ numBatch = 0) then
            await NoMorePossibleUpdates(batchIRs);
        end if;
        Rest:
        latestIRConsidered := max(batchIRs); 
        considered := {};
        SendAllUpdates:
          while TRUE do
             CheckIfFinished:
             if (Cardinality(batchIRs) - Cardinality(considered) = 0) then
                 goto check;
             end if;
             f1: failover();
             sendUpdate: 
                s := min(batchIRs\(considered));
                considered := considered \union {s};
                if numBatch = 0 then
                    if switchState[s] = Updated then
                        goto CheckIfFinished;
                    end if;
                end if;
                sendIRs:
                    controllerSendIR(s);
          end while;
        check:
            failover();
            nofail: 
            await NoMorePossibleUpdates(setSwitches);
            setSwitches := getFailed(copySet);
            if Cardinality(setSwitches) = 0 then
                latestUpdateRcv := max(copySet);
                numBatch := numBatch + 1;
                goto ControllerObj   
            else
                resendUpdates: considered := {};
                               goto SendAllUpdates;
            end if;                
    end while;       
    EndCont:
        continue := FALSE;
    end process *)
    
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-69ba6ab1a3897af906e94f56688937bd
VARIABLES swSeqChangedStatus, switchStatus, installedIRs, failedTimes, 
          NicAsic2OfaBuff, Ofa2NicAsicBuff, Ofa2InstallerBuff, 
          Installer2OfaBuff, TCAM, controlMsgCounter, controller2Switch, 
          switch2Controller, controllerState, IR2SW, 
          controllerThreadPoolIRQueue, IRStatus, SwSuspensionStatus, 
          lastScheduledThread, SetScheduledIRs, dependencyGraph, pc, stack

(* define statement *)
RECURSIVE Paths(_, _)
Paths(n, G) ==  IF n = 1
                THEN
                  G
                ELSE
                    LET nextVs(p) == { e[2] : e \in {e \in G : e[1] = p[Len(p)]} }
                        nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
                    IN
                    UNION {nextPaths(p) : p \in Paths(n-1, G)} \cup Paths(n-1, G)

S == 0..MaxNumIRs
PlausibleDependencySet == {x \in SUBSET (S \X S): /\ ~\E y \in 0..MaxNumIRs: <<y, y>> \in x
                                                  /\ ~\E y, z \in 0..MaxNumIRs: /\  <<y, z>> \in x
                                                                                /\  <<z, y>> \in x
                                                  /\ x # {}
                                                  /\ ~\E y \in 1..MaxNumIRs: <<0, y>> \in x
                                                  /\ \A p \in Paths(MaxNumIRs, x): \/ Len(p) = 1
                                                                                   \/ p[1] # p[Len(p)]}


max(set) == CHOOSE x \in set: \A y \in set: x \geq y
min(set) == CHOOSE x \in set: \A y \in set: x \leq y









controllerIsMaster(controllerID) == IF controllerID = c0 THEN controllerState.c0 = "primary"
                                                         ELSE controllerState.c1 = "primary"


isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
returnSwitchFailedElements(sw) == {x\in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                                                 /\ \/ switchStatus[sw].cpu = NotFailed
                                                                    \/ x \notin {"ofa", "installer"}}
returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}
swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed
swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed
swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed
isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                     /\ IRStatus[y] # IR_DONE
getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                          /\ isDependencySatisfied(x)
                                                          /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                          /\ x \notin SetScheduledIRs[CID][IR2SW[x]]}
getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: IR2SW[x] = SID}





existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                /\ swSeqChangedStatus[x].num > monEvent.num
installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerFailedOrNot"
ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaInFailedOrNot"
                         /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaOutFailedOrNot"
nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchNicAsicInFailedOrNot"
                             /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchNicAsicOutFailedOrNot"
isFinished == \A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE
shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                             \/ monEvent.type = NIC_ASIC_DOWN
                             \/ /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.status.installerStatus = INSTALLER_DOWN
canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                   /\ monEvent.status.installerStatus = INSTALLER_UP


getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ IR2SW[x] = SID
                                             /\ IRStatus[x] \notin {IR_DONE, IR_NONE}}
getIRSetToSuspend(CID, SID) == {x \in SetScheduledIRs[CID][SID]: IRStatus[x] = IR_NONE}
getInstallerStatus(stat) == IF stat = NotFailed
                            THEN INSTALLER_UP
                            ELSE INSTALLER_DOWN

VARIABLES ofaInIR, setIRs, nextThread, nextIR, switchIDToReset, setIRsToReset, 
          resetIR, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, failedSet, 
          statusResolveMsg, recoveredElem, toBeScheduledIRs, nextIRToSent, 
          monitoringEvent, msg

vars == << swSeqChangedStatus, switchStatus, installedIRs, failedTimes, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Ofa2InstallerBuff, 
           Installer2OfaBuff, TCAM, controlMsgCounter, controller2Switch, 
           switch2Controller, controllerState, IR2SW, 
           controllerThreadPoolIRQueue, IRStatus, SwSuspensionStatus, 
           lastScheduledThread, SetScheduledIRs, dependencyGraph, pc, stack, 
           ofaInIR, setIRs, nextThread, nextIR, switchIDToReset, 
           setIRsToReset, resetIR, ingressIR, egressMsg, ofaInMsg, 
           ofaOutConfirmation, installerInIR, statusMsg, notFailedSet, 
           failedElem, failedSet, statusResolveMsg, recoveredElem, 
           toBeScheduledIRs, nextIRToSent, monitoringEvent, msg >>

ProcSet == (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({c0, c1} \X {CONT_SEQ})) \cup (({c0, c1} \X CONTROLLER_THREAD_POOL)) \cup (({c0, c1} \X {CONT_EVENT})) \cup (({c0, c1} \X {CONT_MONITOR}))

Init == (* Global variables *)
        /\ swSeqChangedStatus = <<>>
        /\ switchStatus = [x\in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed, ofa |-> NotFailed, installer |-> NotFailed]]
        /\ installedIRs = <<>>
        /\ failedTimes = [x \in SW |-> 0]
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> <<>>]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ controller2Switch = [x\in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ controllerState = [c0 |-> "primary", c1 |-> "backup"]
        /\ IR2SW \in [1..MaxNumIRs -> SW]
        /\ controllerThreadPoolIRQueue = [y \in {c0, c1} |-> <<>>]
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ lastScheduledThread = 0
        /\ SetScheduledIRs = [x \in {c0, c1} |-> [y \in SW |-> {}]]
        /\ dependencyGraph \in PlausibleDependencySet
        (* Procedure ofaInstallFlowEntry *)
        /\ ofaInIR = [ self \in ProcSet |-> 0]
        (* Procedure scheduleIRs *)
        /\ setIRs = [ self \in ProcSet |-> {}]
        /\ nextThread = [ self \in ProcSet |-> lastScheduledThread]
        /\ nextIR = [ self \in ProcSet |-> 0]
        (* Procedure resetStateWithRecoveredSW *)
        /\ switchIDToReset = [ self \in ProcSet |-> 0]
        /\ setIRsToReset = [ self \in ProcSet |-> {}]
        /\ resetIR = [ self \in ProcSet |-> 0]
        (* Process swNicAsicProcPacketIn *)
        /\ ingressIR = [self \in ({NIC_ASIC_IN} \X SW) |-> [type |-> 0]]
        (* Process swNicAsicProcPacketOut *)
        /\ egressMsg = [self \in ({NIC_ASIC_OUT} \X SW) |-> [type |-> 0]]
        (* Process ofaModuleProcPacketIn *)
        /\ ofaInMsg = [self \in ({OFA_IN} \X SW) |-> [type |-> 0]]
        (* Process ofaModuleProcPacketOut *)
        /\ ofaOutConfirmation = [self \in ({OFA_OUT} \X SW) |-> 0]
        (* Process installerModuleProc *)
        /\ installerInIR = [self \in ({INSTALLER} \X SW) |-> 0]
        (* Process swFailureProc *)
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> <<>>]
        /\ notFailedSet = [self \in ({SW_FAILURE_PROC} \X SW) |-> {}]
        /\ failedElem = [self \in ({SW_FAILURE_PROC} \X SW) |-> ""]
        (* Process swResolveFailure *)
        /\ failedSet = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> <<>>]
        /\ recoveredElem = [self \in ({SW_RESOLVE_PROC} \X SW) |-> ""]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({c0, c1} \X {CONT_SEQ}) |-> {}]
        (* Process controllerWorkerThreads *)
        /\ nextIRToSent = [self \in ({c0, c1} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({c0, c1} \X {CONT_EVENT}) |-> [type |-> 0]]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({c0, c1} \X {CONT_MONITOR}) |-> [type |-> 0]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in ({NIC_ASIC_IN} \X SW) -> "SwitchNicAsicInFailedOrNot"
                                        [] self \in ({NIC_ASIC_OUT} \X SW) -> "SwitchNicAsicOutFailedOrNot"
                                        [] self \in ({OFA_IN} \X SW) -> "SwitchOfaInFailedOrNot"
                                        [] self \in ({OFA_OUT} \X SW) -> "SwitchOfaOutFailedOrNot"
                                        [] self \in ({INSTALLER} \X SW) -> "SwitchInstallerFailedOrNot"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({c0, c1} \X {CONT_SEQ}) -> "ControllerSeqProc"
                                        [] self \in ({c0, c1} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({c0, c1} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({c0, c1} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

SwitchOFAInsert2InstallerBuff(self) == /\ pc[self] = "SwitchOFAInsert2InstallerBuff"
                                       /\ IF swOFACanProcessIRs(self[2])
                                             THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], ofaInIR[self])]
                                                  /\ pc' = [pc EXCEPT ![self] = "EndInstallFlowEntry"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "EndInstallFlowEntry"]
                                                  /\ UNCHANGED Ofa2InstallerBuff
                                       /\ UNCHANGED << swSeqChangedStatus, 
                                                       switchStatus, 
                                                       installedIRs, 
                                                       failedTimes, 
                                                       NicAsic2OfaBuff, 
                                                       Ofa2NicAsicBuff, 
                                                       Installer2OfaBuff, TCAM, 
                                                       controlMsgCounter, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       controllerState, IR2SW, 
                                                       controllerThreadPoolIRQueue, 
                                                       IRStatus, 
                                                       SwSuspensionStatus, 
                                                       lastScheduledThread, 
                                                       SetScheduledIRs, 
                                                       dependencyGraph, stack, 
                                                       ofaInIR, setIRs, 
                                                       nextThread, nextIR, 
                                                       switchIDToReset, 
                                                       setIRsToReset, resetIR, 
                                                       ingressIR, egressMsg, 
                                                       ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       toBeScheduledIRs, 
                                                       nextIRToSent, 
                                                       monitoringEvent, msg >>

EndInstallFlowEntry(self) == /\ pc[self] = "EndInstallFlowEntry"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ ofaInIR' = [ofaInIR EXCEPT ![self] = Head(stack[self]).ofaInIR]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             setIRs, nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, toBeScheduledIRs, 
                                             nextIRToSent, monitoringEvent, 
                                             msg >>

ofaInstallFlowEntry(self) == SwitchOFAInsert2InstallerBuff(self)
                                \/ EndInstallFlowEntry(self)

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ IF setIRs[self] # {} /\ controllerIsMaster(self[1])
                                  THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in setIRs[self]: TRUE]
                                       /\ Assert(IRStatus[nextIR'[self]] \in {IR_NONE, IR_DONE}, 
                                                 "Failure of assertion at line 430, column 9.")
                                       /\ pc' = [pc EXCEPT ![self] = "AddToScheduleIRSet"]
                                       /\ UNCHANGED << stack, setIRs, 
                                                       nextThread >>
                                  ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ nextThread' = [nextThread EXCEPT ![self] = Head(stack[self]).nextThread]
                                       /\ nextIR' = [nextIR EXCEPT ![self] = Head(stack[self]).nextIR]
                                       /\ setIRs' = [setIRs EXCEPT ![self] = Head(stack[self]).setIRs]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                            installedIRs, failedTimes, 
                                            NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                            Ofa2InstallerBuff, 
                                            Installer2OfaBuff, TCAM, 
                                            controlMsgCounter, 
                                            controller2Switch, 
                                            switch2Controller, controllerState, 
                                            IR2SW, controllerThreadPoolIRQueue, 
                                            IRStatus, SwSuspensionStatus, 
                                            lastScheduledThread, 
                                            SetScheduledIRs, dependencyGraph, 
                                            ofaInIR, switchIDToReset, 
                                            setIRsToReset, resetIR, ingressIR, 
                                            egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            toBeScheduledIRs, nextIRToSent, 
                                            monitoringEvent, msg >>

AddToScheduleIRSet(self) == /\ pc[self] = "AddToScheduleIRSet"
                            /\ Assert(nextIR[self] \notin SetScheduledIRs[self[1]][IR2SW[nextIR[self]]], 
                                      "Failure of assertion at line 434, column 13.")
                            /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![self[1]][IR2SW[nextIR[self]]] = SetScheduledIRs[self[1]][IR2SW[nextIR[self]]] \cup {nextIR[self]}]
                            /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                            /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                            installedIRs, failedTimes, 
                                            NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                            Ofa2InstallerBuff, 
                                            Installer2OfaBuff, TCAM, 
                                            controlMsgCounter, 
                                            controller2Switch, 
                                            switch2Controller, controllerState, 
                                            IR2SW, controllerThreadPoolIRQueue, 
                                            IRStatus, SwSuspensionStatus, 
                                            lastScheduledThread, 
                                            dependencyGraph, stack, ofaInIR, 
                                            setIRs, nextThread, nextIR, 
                                            switchIDToReset, setIRsToReset, 
                                            resetIR, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, toBeScheduledIRs, 
                                            nextIRToSent, monitoringEvent, msg >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]] = Append(controllerThreadPoolIRQueue[self[1]], nextIR[self])]
                       /\ setIRs' = [setIRs EXCEPT ![self] = setIRs[self]\{nextIR[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                       /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                       installedIRs, failedTimes, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Ofa2InstallerBuff, Installer2OfaBuff, 
                                       TCAM, controlMsgCounter, 
                                       controller2Switch, switch2Controller, 
                                       controllerState, IR2SW, IRStatus, 
                                       SwSuspensionStatus, lastScheduledThread, 
                                       SetScheduledIRs, dependencyGraph, stack, 
                                       ofaInIR, nextThread, nextIR, 
                                       switchIDToReset, setIRsToReset, resetIR, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       statusMsg, notFailedSet, failedElem, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, toBeScheduledIRs, 
                                       nextIRToSent, monitoringEvent, msg >>

scheduleIRs(self) == SchedulerMechanism(self) \/ AddToScheduleIRSet(self)
                        \/ ScheduleTheIR(self)

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = getIRSetToReset(switchIDToReset[self])]
                           /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                           /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                           installedIRs, failedTimes, 
                                           NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                           Ofa2InstallerBuff, 
                                           Installer2OfaBuff, TCAM, 
                                           controlMsgCounter, 
                                           controller2Switch, 
                                           switch2Controller, controllerState, 
                                           IR2SW, controllerThreadPoolIRQueue, 
                                           IRStatus, SwSuspensionStatus, 
                                           lastScheduledThread, 
                                           SetScheduledIRs, dependencyGraph, 
                                           stack, ofaInIR, setIRs, nextThread, 
                                           nextIR, switchIDToReset, resetIR, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, toBeScheduledIRs, 
                                           nextIRToSent, monitoringEvent, msg >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ IF setIRsToReset[self] # {}
                           THEN /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                                /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                                /\ Assert(IRStatus[resetIR'[self]] \notin {IR_NONE}, 
                                          "Failure of assertion at line 471, column 9.")
                                /\ pc' = [pc EXCEPT ![self] = "ControllerResetIRStatAfterRecovery"]
                                /\ UNCHANGED << stack, switchIDToReset >>
                           ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = Head(stack[self]).setIRsToReset]
                                /\ resetIR' = [resetIR EXCEPT ![self] = Head(stack[self]).resetIR]
                                /\ switchIDToReset' = [switchIDToReset EXCEPT ![self] = Head(stack[self]).switchIDToReset]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                     installedIRs, failedTimes, 
                                     NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                     Ofa2InstallerBuff, Installer2OfaBuff, 
                                     TCAM, controlMsgCounter, 
                                     controller2Switch, switch2Controller, 
                                     controllerState, IR2SW, 
                                     controllerThreadPoolIRQueue, IRStatus, 
                                     SwSuspensionStatus, lastScheduledThread, 
                                     SetScheduledIRs, dependencyGraph, ofaInIR, 
                                     setIRs, nextThread, nextIR, ingressIR, 
                                     egressMsg, ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, failedSet, statusResolveMsg, 
                                     recoveredElem, toBeScheduledIRs, 
                                     nextIRToSent, monitoringEvent, msg >>

ControllerResetIRStatAfterRecovery(self) == /\ pc[self] = "ControllerResetIRStatAfterRecovery"
                                            /\ IF IRStatus[resetIR[self]] # IR_DONE
                                                  THEN /\ IRStatus' = [IRStatus EXCEPT ![resetIR[self]] = IR_NONE]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED IRStatus
                                            /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                            /\ UNCHANGED << swSeqChangedStatus, 
                                                            switchStatus, 
                                                            installedIRs, 
                                                            failedTimes, 
                                                            NicAsic2OfaBuff, 
                                                            Ofa2NicAsicBuff, 
                                                            Ofa2InstallerBuff, 
                                                            Installer2OfaBuff, 
                                                            TCAM, 
                                                            controlMsgCounter, 
                                                            controller2Switch, 
                                                            switch2Controller, 
                                                            controllerState, 
                                                            IR2SW, 
                                                            controllerThreadPoolIRQueue, 
                                                            SwSuspensionStatus, 
                                                            lastScheduledThread, 
                                                            SetScheduledIRs, 
                                                            dependencyGraph, 
                                                            stack, ofaInIR, 
                                                            setIRs, nextThread, 
                                                            nextIR, 
                                                            switchIDToReset, 
                                                            setIRsToReset, 
                                                            resetIR, ingressIR, 
                                                            egressMsg, 
                                                            ofaInMsg, 
                                                            ofaOutConfirmation, 
                                                            installerInIR, 
                                                            statusMsg, 
                                                            notFailedSet, 
                                                            failedElem, 
                                                            failedSet, 
                                                            statusResolveMsg, 
                                                            recoveredElem, 
                                                            toBeScheduledIRs, 
                                                            nextIRToSent, 
                                                            monitoringEvent, 
                                                            msg >>

resetStateWithRecoveredSW(self) == getIRsToBeChecked(self)
                                      \/ ResetAllIRs(self)
                                      \/ ControllerResetIRStatAfterRecovery(self)

SwitchNicAsicInFailedOrNot(self) == /\ pc[self] = "SwitchNicAsicInFailedOrNot"
                                    /\ swCanReceivePackets(self[2])
                                    /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                    switchStatus, installedIRs, 
                                                    failedTimes, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Ofa2InstallerBuff, 
                                                    Installer2OfaBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    controllerState, IR2SW, 
                                                    controllerThreadPoolIRQueue, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    lastScheduledThread, 
                                                    SetScheduledIRs, 
                                                    dependencyGraph, stack, 
                                                    ofaInIR, setIRs, 
                                                    nextThread, nextIR, 
                                                    switchIDToReset, 
                                                    setIRsToReset, resetIR, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, 
                                                    nextIRToSent, 
                                                    monitoringEvent, msg >>

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ IF ~isFinished
                               THEN /\ IF swCanReceivePackets(self[2])
                                          THEN /\ Len(controller2Switch[self[2]]) > 0
                                               /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                                               /\ Assert(\/ ingressIR'[self].type = RECONCILIATION_REQUEST
                                                         \/ ingressIR'[self].type = INSTALL_FLOW, 
                                                         "Failure of assertion at line 534, column 13.")
                                               /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInFailedOrNot"]
                                               /\ UNCHANGED << controller2Switch, 
                                                               ingressIR >>
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << controller2Switch, 
                                                    ingressIR >>
                         /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                         installedIRs, failedTimes, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Ofa2InstallerBuff, Installer2OfaBuff, 
                                         TCAM, controlMsgCounter, 
                                         switch2Controller, controllerState, 
                                         IR2SW, controllerThreadPoolIRQueue, 
                                         IRStatus, SwSuspensionStatus, 
                                         lastScheduledThread, SetScheduledIRs, 
                                         dependencyGraph, stack, ofaInIR, 
                                         setIRs, nextThread, nextIR, 
                                         switchIDToReset, setIRsToReset, 
                                         resetIR, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, toBeScheduledIRs, 
                                         nextIRToSent, monitoringEvent, msg >>

SwitchNicAsicInsertToOfaBuff(self) == /\ pc[self] = "SwitchNicAsicInsertToOfaBuff"
                                      /\ IF swCanReceivePackets(self[2])
                                            THEN /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Append(NicAsic2OfaBuff[self[2]], ingressIR[self])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInFailedOrNot"]
                                                 /\ UNCHANGED NicAsic2OfaBuff
                                      /\ UNCHANGED << swSeqChangedStatus, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      failedTimes, 
                                                      Ofa2NicAsicBuff, 
                                                      Ofa2InstallerBuff, 
                                                      Installer2OfaBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      controllerState, IR2SW, 
                                                      controllerThreadPoolIRQueue, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      dependencyGraph, stack, 
                                                      ofaInIR, setIRs, 
                                                      nextThread, nextIR, 
                                                      switchIDToReset, 
                                                      setIRsToReset, resetIR, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, 
                                                      nextIRToSent, 
                                                      monitoringEvent, msg >>

swNicAsicProcPacketIn(self) == SwitchNicAsicInFailedOrNot(self)
                                  \/ SwitchRcvPacket(self)
                                  \/ SwitchNicAsicInsertToOfaBuff(self)

SwitchNicAsicOutFailedOrNot(self) == /\ pc[self] = "SwitchNicAsicOutFailedOrNot"
                                     /\ swCanReceivePackets(self[2])
                                     /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                     switchStatus, 
                                                     installedIRs, failedTimes, 
                                                     NicAsic2OfaBuff, 
                                                     Ofa2NicAsicBuff, 
                                                     Ofa2InstallerBuff, 
                                                     Installer2OfaBuff, TCAM, 
                                                     controlMsgCounter, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     controllerState, IR2SW, 
                                                     controllerThreadPoolIRQueue, 
                                                     IRStatus, 
                                                     SwSuspensionStatus, 
                                                     lastScheduledThread, 
                                                     SetScheduledIRs, 
                                                     dependencyGraph, stack, 
                                                     ofaInIR, setIRs, 
                                                     nextThread, nextIR, 
                                                     switchIDToReset, 
                                                     setIRsToReset, resetIR, 
                                                     ingressIR, egressMsg, 
                                                     ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     installerInIR, statusMsg, 
                                                     notFailedSet, failedElem, 
                                                     failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, 
                                                     toBeScheduledIRs, 
                                                     nextIRToSent, 
                                                     monitoringEvent, msg >>

SwitchFromOFAPacket(self) == /\ pc[self] = "SwitchFromOFAPacket"
                             /\ IF ~isFinished
                                   THEN /\ IF swCanReceivePackets(self[2])
                                              THEN /\ Len(Ofa2NicAsicBuff[self[2]]) > 0
                                                   /\ egressMsg' = [egressMsg EXCEPT ![self] = Head(Ofa2NicAsicBuff[self[2]])]
                                                   /\ Assert(\/ egressMsg'[self].type = INSTALLED_SUCCESSFULLY
                                                             \/ egressMsg'[self].type = RECEIVED_SUCCESSFULLY
                                                             \/ egressMsg'[self].type = RECONCILIATION_RESPONSE, 
                                                             "Failure of assertion at line 560, column 13.")
                                                   /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                                                   /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicOutFailedOrNot"]
                                                   /\ UNCHANGED << Ofa2NicAsicBuff, 
                                                                   egressMsg >>
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED << Ofa2NicAsicBuff, 
                                                        egressMsg >>
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             stack, ofaInIR, setIRs, 
                                             nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIRToSent, 
                                             monitoringEvent, msg >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ switch2Controller' = Append(switch2Controller, egressMsg[self])
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicOutFailedOrNot"]
                                            /\ UNCHANGED switch2Controller
                                 /\ UNCHANGED << swSeqChangedStatus, 
                                                 switchStatus, installedIRs, 
                                                 failedTimes, NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Ofa2InstallerBuff, 
                                                 Installer2OfaBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 controller2Switch, 
                                                 controllerState, IR2SW, 
                                                 controllerThreadPoolIRQueue, 
                                                 IRStatus, SwSuspensionStatus, 
                                                 lastScheduledThread, 
                                                 SetScheduledIRs, 
                                                 dependencyGraph, stack, 
                                                 ofaInIR, setIRs, nextThread, 
                                                 nextIR, switchIDToReset, 
                                                 setIRsToReset, resetIR, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, 
                                                 nextIRToSent, monitoringEvent, 
                                                 msg >>

swNicAsicProcPacketOut(self) == SwitchNicAsicOutFailedOrNot(self)
                                   \/ SwitchFromOFAPacket(self)
                                   \/ SwitchNicAsicSendOutMsg(self)

SwitchOfaInFailedOrNot(self) == /\ pc[self] = "SwitchOfaInFailedOrNot"
                                /\ swOFACanProcessIRs(self[2])
                                /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                /\ UNCHANGED << swSeqChangedStatus, 
                                                switchStatus, installedIRs, 
                                                failedTimes, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Ofa2InstallerBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                controllerState, IR2SW, 
                                                controllerThreadPoolIRQueue, 
                                                IRStatus, SwSuspensionStatus, 
                                                lastScheduledThread, 
                                                SetScheduledIRs, 
                                                dependencyGraph, stack, 
                                                ofaInIR, setIRs, nextThread, 
                                                nextIR, switchIDToReset, 
                                                setIRsToReset, resetIR, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIRToSent, 
                                                monitoringEvent, msg >>

SwitchOfaProcIn(self) == /\ pc[self] = "SwitchOfaProcIn"
                         /\ IF ~isFinished
                               THEN /\ IF swOFACanProcessIRs(self[2])
                                          THEN /\ Len(NicAsic2OfaBuff[self[2]]) > 0
                                               /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = Head(NicAsic2OfaBuff[self[2]])]
                                               /\ Assert(ofaInMsg'[self].to = self[2], 
                                                         "Failure of assertion at line 590, column 17.")
                                               /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchOfaInFailedOrNot"]
                                               /\ UNCHANGED << NicAsic2OfaBuff, 
                                                               ofaInMsg >>
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << NicAsic2OfaBuff, ofaInMsg >>
                         /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                         installedIRs, failedTimes, 
                                         Ofa2NicAsicBuff, Ofa2InstallerBuff, 
                                         Installer2OfaBuff, TCAM, 
                                         controlMsgCounter, controller2Switch, 
                                         switch2Controller, controllerState, 
                                         IR2SW, controllerThreadPoolIRQueue, 
                                         IRStatus, SwSuspensionStatus, 
                                         lastScheduledThread, SetScheduledIRs, 
                                         dependencyGraph, stack, ofaInIR, 
                                         setIRs, nextThread, nextIR, 
                                         switchIDToReset, setIRsToReset, 
                                         resetIR, ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, toBeScheduledIRs, 
                                         nextIRToSent, monitoringEvent, msg >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                      THEN /\ /\ ofaInIR' = [ofaInIR EXCEPT ![self] = ofaInMsg[self].IR]
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ofaInstallFlowEntry",
                                                                                       pc        |->  "SwitchOfaProcIn",
                                                                                       ofaInIR   |->  ofaInIR[self] ] >>
                                                                                   \o stack[self]]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOFAInsert2InstallerBuff"]
                                      ELSE /\ Assert(FALSE, 
                                                     "Failure of assertion at line 602, column 17.")
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED << stack, ofaInIR >>
                                /\ UNCHANGED << swSeqChangedStatus, 
                                                switchStatus, installedIRs, 
                                                failedTimes, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Ofa2InstallerBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                controllerState, IR2SW, 
                                                controllerThreadPoolIRQueue, 
                                                IRStatus, SwSuspensionStatus, 
                                                lastScheduledThread, 
                                                SetScheduledIRs, 
                                                dependencyGraph, setIRs, 
                                                nextThread, nextIR, 
                                                switchIDToReset, setIRsToReset, 
                                                resetIR, ingressIR, egressMsg, 
                                                ofaInMsg, ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIRToSent, 
                                                monitoringEvent, msg >>

ofaModuleProcPacketIn(self) == SwitchOfaInFailedOrNot(self)
                                  \/ SwitchOfaProcIn(self)
                                  \/ SwitchOfaProcessPacket(self)

SwitchOfaOutFailedOrNot(self) == /\ pc[self] = "SwitchOfaOutFailedOrNot"
                                 /\ swOFACanProcessIRs(self[2])
                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                 /\ UNCHANGED << swSeqChangedStatus, 
                                                 switchStatus, installedIRs, 
                                                 failedTimes, NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Ofa2InstallerBuff, 
                                                 Installer2OfaBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 controllerState, IR2SW, 
                                                 controllerThreadPoolIRQueue, 
                                                 IRStatus, SwSuspensionStatus, 
                                                 lastScheduledThread, 
                                                 SetScheduledIRs, 
                                                 dependencyGraph, stack, 
                                                 ofaInIR, setIRs, nextThread, 
                                                 nextIR, switchIDToReset, 
                                                 setIRsToReset, resetIR, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, 
                                                 nextIRToSent, monitoringEvent, 
                                                 msg >>

SwitchOfaProcOut(self) == /\ pc[self] = "SwitchOfaProcOut"
                          /\ IF ~isFinished
                                THEN /\ IF swOFACanProcessIRs(self[2])
                                           THEN /\ Installer2OfaBuff[self[2]] # <<>>
                                                /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = Head(Installer2OfaBuff[self[2]])]
                                                /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Tail(Installer2OfaBuff[self[2]])]
                                                /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchOfaOutFailedOrNot"]
                                                /\ UNCHANGED << Installer2OfaBuff, 
                                                                ofaOutConfirmation >>
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED << Installer2OfaBuff, 
                                                     ofaOutConfirmation >>
                          /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                          installedIRs, failedTimes, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, controller2Switch, 
                                          switch2Controller, controllerState, 
                                          IR2SW, controllerThreadPoolIRQueue, 
                                          IRStatus, SwSuspensionStatus, 
                                          lastScheduledThread, SetScheduledIRs, 
                                          dependencyGraph, stack, ofaInIR, 
                                          setIRs, nextThread, nextIR, 
                                          switchIDToReset, setIRsToReset, 
                                          resetIR, ingressIR, egressMsg, 
                                          ofaInMsg, installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, nextIRToSent, 
                                          monitoringEvent, msg >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                                                                                              from |-> self[2],
                                                                                                                                              IR |-> ofaOutConfirmation[self]])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchOfaOutFailedOrNot"]
                                                 /\ UNCHANGED Ofa2NicAsicBuff
                                      /\ UNCHANGED << swSeqChangedStatus, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      failedTimes, 
                                                      NicAsic2OfaBuff, 
                                                      Ofa2InstallerBuff, 
                                                      Installer2OfaBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      controllerState, IR2SW, 
                                                      controllerThreadPoolIRQueue, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      dependencyGraph, stack, 
                                                      ofaInIR, setIRs, 
                                                      nextThread, nextIR, 
                                                      switchIDToReset, 
                                                      setIRsToReset, resetIR, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, 
                                                      nextIRToSent, 
                                                      monitoringEvent, msg >>

ofaModuleProcPacketOut(self) == SwitchOfaOutFailedOrNot(self)
                                   \/ SwitchOfaProcOut(self)
                                   \/ SendInstallationConfirmation(self)

SwitchInstallerFailedOrNot(self) == /\ pc[self] = "SwitchInstallerFailedOrNot"
                                    /\ swCanInstallIRs(self[2])
                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                    switchStatus, installedIRs, 
                                                    failedTimes, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Ofa2InstallerBuff, 
                                                    Installer2OfaBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    controllerState, IR2SW, 
                                                    controllerThreadPoolIRQueue, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    lastScheduledThread, 
                                                    SetScheduledIRs, 
                                                    dependencyGraph, stack, 
                                                    ofaInIR, setIRs, 
                                                    nextThread, nextIR, 
                                                    switchIDToReset, 
                                                    setIRsToReset, resetIR, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, 
                                                    nextIRToSent, 
                                                    monitoringEvent, msg >>

SwitchInstallerProc(self) == /\ pc[self] = "SwitchInstallerProc"
                             /\ IF ~isFinished
                                   THEN /\ IF swCanInstallIRs(self[2])
                                              THEN /\ Len(Ofa2InstallerBuff[self[2]]) > 0
                                                   /\ installerInIR' = [installerInIR EXCEPT ![self] = Head(Ofa2InstallerBuff[self[2]])]
                                                   /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                                                   /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerFailedOrNot"]
                                                   /\ UNCHANGED << Ofa2InstallerBuff, 
                                                                   installerInIR >>
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED << Ofa2InstallerBuff, 
                                                        installerInIR >>
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             stack, ofaInIR, setIRs, 
                                             nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIRToSent, 
                                             monitoringEvent, msg >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ installedIRs' = Append(installedIRs, installerInIR[self])
                                               /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], installerInIR[self])]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerSendConfirmation"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerFailedOrNot"]
                                               /\ UNCHANGED << installedIRs, 
                                                               TCAM >>
                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                    switchStatus, failedTimes, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Ofa2InstallerBuff, 
                                                    Installer2OfaBuff, 
                                                    controlMsgCounter, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    controllerState, IR2SW, 
                                                    controllerThreadPoolIRQueue, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    lastScheduledThread, 
                                                    SetScheduledIRs, 
                                                    dependencyGraph, stack, 
                                                    ofaInIR, setIRs, 
                                                    nextThread, nextIR, 
                                                    switchIDToReset, 
                                                    setIRsToReset, resetIR, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, 
                                                    nextIRToSent, 
                                                    monitoringEvent, msg >>

SwitchInstallerSendConfirmation(self) == /\ pc[self] = "SwitchInstallerSendConfirmation"
                                         /\ IF swCanInstallIRs(self[2])
                                               THEN /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Append(Installer2OfaBuff[self[2]], installerInIR[self])]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerFailedOrNot"]
                                                    /\ UNCHANGED Installer2OfaBuff
                                         /\ UNCHANGED << swSeqChangedStatus, 
                                                         switchStatus, 
                                                         installedIRs, 
                                                         failedTimes, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         controllerState, 
                                                         IR2SW, 
                                                         controllerThreadPoolIRQueue, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         lastScheduledThread, 
                                                         SetScheduledIRs, 
                                                         dependencyGraph, 
                                                         stack, ofaInIR, 
                                                         setIRs, nextThread, 
                                                         nextIR, 
                                                         switchIDToReset, 
                                                         setIRsToReset, 
                                                         resetIR, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, 
                                                         nextIRToSent, 
                                                         monitoringEvent, msg >>

installerModuleProc(self) == SwitchInstallerFailedOrNot(self)
                                \/ SwitchInstallerProc(self)
                                \/ SwitchInstallerInsert2TCAM(self)
                                \/ SwitchInstallerSendConfirmation(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ IF failedTimes[self[2]] < MAX_NUM_SW_FAILURE /\ ~isFinished
                             THEN /\ statusMsg' = [statusMsg EXCEPT ![self] = <<>>]
                                  /\ notFailedSet' = [notFailedSet EXCEPT ![self] = returnSwitchElementsNotFailed(self[2])]
                                  /\ notFailedSet'[self] # {}
                                  /\ \E elem \in notFailedSet'[self]:
                                       failedElem' = [failedElem EXCEPT ![self] = elem]
                                  /\ IF failedElem'[self] = "cpu"
                                        THEN /\ pc' = [pc EXCEPT ![self] = "SwitchCpuFailure"]
                                        ELSE /\ IF failedElem'[self] = "ofa"
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "SwitchOfaFailure"]
                                                   ELSE /\ IF failedElem'[self] = "installer"
                                                              THEN /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerFailure"]
                                                              ELSE /\ IF failedElem'[self] = "nicAsic"
                                                                         THEN /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicFailure"]
                                                                         ELSE /\ Assert(FALSE, 
                                                                                        "Failure of assertion at line 699, column 14.")
                                                                              /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << statusMsg, notFailedSet, 
                                                  failedElem >>
                       /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                       installedIRs, failedTimes, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Ofa2InstallerBuff, Installer2OfaBuff, 
                                       TCAM, controlMsgCounter, 
                                       controller2Switch, switch2Controller, 
                                       controllerState, IR2SW, 
                                       controllerThreadPoolIRQueue, IRStatus, 
                                       SwSuspensionStatus, lastScheduledThread, 
                                       SetScheduledIRs, dependencyGraph, stack, 
                                       ofaInIR, setIRs, nextThread, nextIR, 
                                       switchIDToReset, setIRsToReset, resetIR, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, toBeScheduledIRs, 
                                       nextIRToSent, monitoringEvent, msg >>

SwitchCpuFailure(self) == /\ pc[self] = "SwitchCpuFailure"
                          /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = Failed,
                                                                  ![self[2]].ofa = Failed,
                                                                  ![self[2]].installer = Failed]
                          /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                          /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                          /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                          /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                          /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                     /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                  swID |-> self[2],
                                                                                  num |-> controlMsgCounter'[self[2]]]]
                                     /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                ELSE /\ TRUE
                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                     controlMsgCounter, 
                                                     statusMsg >>
                          /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                          /\ UNCHANGED << installedIRs, TCAM, 
                                          controller2Switch, switch2Controller, 
                                          controllerState, IR2SW, 
                                          controllerThreadPoolIRQueue, 
                                          IRStatus, SwSuspensionStatus, 
                                          lastScheduledThread, SetScheduledIRs, 
                                          dependencyGraph, stack, ofaInIR, 
                                          setIRs, nextThread, nextIR, 
                                          switchIDToReset, setIRsToReset, 
                                          resetIR, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, notFailedSet, 
                                          failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, nextIRToSent, 
                                          monitoringEvent, msg >>

SwitchOfaFailure(self) == /\ pc[self] = "SwitchOfaFailure"
                          /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = Failed]
                          /\ Assert(switchStatus'[self[2]].cpu = NotFailed, 
                                    "Failure of assertion at line 264, column 9 of macro called at line 690, column 17.")
                          /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                     /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                  swID |-> self[2],
                                                                                  num |-> controlMsgCounter'[self[2]]]]
                                     /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                ELSE /\ TRUE
                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                     controlMsgCounter, 
                                                     statusMsg >>
                          /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                          /\ UNCHANGED << installedIRs, NicAsic2OfaBuff, 
                                          Ofa2NicAsicBuff, Ofa2InstallerBuff, 
                                          Installer2OfaBuff, TCAM, 
                                          controller2Switch, switch2Controller, 
                                          controllerState, IR2SW, 
                                          controllerThreadPoolIRQueue, 
                                          IRStatus, SwSuspensionStatus, 
                                          lastScheduledThread, SetScheduledIRs, 
                                          dependencyGraph, stack, ofaInIR, 
                                          setIRs, nextThread, nextIR, 
                                          switchIDToReset, setIRsToReset, 
                                          resetIR, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, notFailedSet, 
                                          failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, nextIRToSent, 
                                          monitoringEvent, msg >>

SwitchInstallerFailure(self) == /\ pc[self] = "SwitchInstallerFailure"
                                /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                /\ Assert(switchStatus'[self[2]].cpu = NotFailed, 
                                          "Failure of assertion at line 302, column 9 of macro called at line 694, column 17.")
                                /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                                /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                      THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                     "Failure of assertion at line 305, column 13 of macro called at line 694, column 17.")
                                           /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                           /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                        swID |-> self[2],
                                                                                        num |-> controlMsgCounter'[self[2]],
                                                                                        status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                           /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << swSeqChangedStatus, 
                                                           controlMsgCounter, 
                                                           statusMsg >>
                                /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                                /\ UNCHANGED << installedIRs, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Ofa2InstallerBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                controllerState, IR2SW, 
                                                controllerThreadPoolIRQueue, 
                                                IRStatus, SwSuspensionStatus, 
                                                lastScheduledThread, 
                                                SetScheduledIRs, 
                                                dependencyGraph, stack, 
                                                ofaInIR, setIRs, nextThread, 
                                                nextIR, switchIDToReset, 
                                                setIRsToReset, resetIR, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, notFailedSet, 
                                                failedElem, failedSet, 
                                                statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIRToSent, 
                                                monitoringEvent, msg >>

SwitchNicAsicFailure(self) == /\ pc[self] = "SwitchNicAsicFailure"
                              /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                              /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                              /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                              /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                              /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                           swID |-> self[2],
                                                                           num |-> controlMsgCounter'[self[2]]]]
                              /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                              /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                              /\ UNCHANGED << installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Ofa2InstallerBuff, 
                                              Installer2OfaBuff, TCAM, 
                                              switch2Controller, 
                                              controllerState, IR2SW, 
                                              controllerThreadPoolIRQueue, 
                                              IRStatus, SwSuspensionStatus, 
                                              lastScheduledThread, 
                                              SetScheduledIRs, dependencyGraph, 
                                              stack, ofaInIR, setIRs, 
                                              nextThread, nextIR, 
                                              switchIDToReset, setIRsToReset, 
                                              resetIR, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, notFailedSet, 
                                              failedElem, failedSet, 
                                              statusResolveMsg, recoveredElem, 
                                              toBeScheduledIRs, nextIRToSent, 
                                              monitoringEvent, msg >>

swFailureProc(self) == SwitchFailure(self) \/ SwitchCpuFailure(self)
                          \/ SwitchOfaFailure(self)
                          \/ SwitchInstallerFailure(self)
                          \/ SwitchNicAsicFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ IF ~isFinished
                                    THEN /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = <<>>]
                                         /\ failedSet' = [failedSet EXCEPT ![self] = returnSwitchFailedElements(self[2])]
                                         /\ Cardinality(failedSet'[self]) > 0
                                         /\ \E elem \in failedSet'[self]:
                                              recoveredElem' = [recoveredElem EXCEPT ![self] = elem]
                                         /\ IF recoveredElem'[self] = "cpu"
                                               THEN /\ pc' = [pc EXCEPT ![self] = "SwitchCpuRecovery"]
                                               ELSE /\ IF recoveredElem'[self] = "nicAsic"
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicRecovery"]
                                                          ELSE /\ IF recoveredElem'[self] = "ofa"
                                                                     THEN /\ pc' = [pc EXCEPT ![self] = "SwitchOfaRecovery"]
                                                                     ELSE /\ IF recoveredElem'[self] = "installer"
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerRecovery"]
                                                                                ELSE /\ Assert(FALSE, 
                                                                                               "Failure of assertion at line 722, column 14.")
                                                                                     /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                         /\ UNCHANGED << failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem >>
                              /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                              installedIRs, failedTimes, 
                                              NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                              Ofa2InstallerBuff, 
                                              Installer2OfaBuff, TCAM, 
                                              controlMsgCounter, 
                                              controller2Switch, 
                                              switch2Controller, 
                                              controllerState, IR2SW, 
                                              controllerThreadPoolIRQueue, 
                                              IRStatus, SwSuspensionStatus, 
                                              lastScheduledThread, 
                                              SetScheduledIRs, dependencyGraph, 
                                              stack, ofaInIR, setIRs, 
                                              nextThread, nextIR, 
                                              switchIDToReset, setIRsToReset, 
                                              resetIR, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              toBeScheduledIRs, nextIRToSent, 
                                              monitoringEvent, msg >>

SwitchCpuRecovery(self) == /\ pc[self] = "SwitchCpuRecovery"
                           /\ ofaStartingMode(self[2]) /\ installerInStartingMode(self[2])
                           /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = NotFailed,
                                                                   ![self[2]].ofa = NotFailed,
                                                                   ![self[2]].installer = NotFailed]
                           /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                           /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                           /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                           /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                           /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                 THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                      /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                 swID |-> self[2],
                                                                                                 num |-> controlMsgCounter'[self[2]],
                                                                                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                      /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusResolveMsg'[self])
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << swSeqChangedStatus, 
                                                      controlMsgCounter, 
                                                      statusResolveMsg >>
                           /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                           /\ UNCHANGED << installedIRs, failedTimes, TCAM, 
                                           controller2Switch, 
                                           switch2Controller, controllerState, 
                                           IR2SW, controllerThreadPoolIRQueue, 
                                           IRStatus, SwSuspensionStatus, 
                                           lastScheduledThread, 
                                           SetScheduledIRs, dependencyGraph, 
                                           stack, ofaInIR, setIRs, nextThread, 
                                           nextIR, switchIDToReset, 
                                           setIRsToReset, resetIR, ingressIR, 
                                           egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, recoveredElem, 
                                           toBeScheduledIRs, nextIRToSent, 
                                           monitoringEvent, msg >>

SwitchNicAsicRecovery(self) == /\ pc[self] = "SwitchNicAsicRecovery"
                               /\ nicAsicStartingMode(self[2])
                               /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = NotFailed]
                               /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                               /\ IF switchStatus'[self[2]].ofa = Failed
                                     THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                          /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                                     swID |-> self[2],
                                                                                                     num |-> controlMsgCounter'[self[2]]]]
                                     ELSE /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                          /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                     swID |-> self[2],
                                                                                                     num |-> controlMsgCounter'[self[2]],
                                                                                                     status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                               /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusResolveMsg'[self])
                               /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                               /\ UNCHANGED << installedIRs, failedTimes, 
                                               NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Ofa2InstallerBuff, 
                                               Installer2OfaBuff, TCAM, 
                                               switch2Controller, 
                                               controllerState, IR2SW, 
                                               controllerThreadPoolIRQueue, 
                                               IRStatus, SwSuspensionStatus, 
                                               lastScheduledThread, 
                                               SetScheduledIRs, 
                                               dependencyGraph, stack, ofaInIR, 
                                               setIRs, nextThread, nextIR, 
                                               switchIDToReset, setIRsToReset, 
                                               resetIR, ingressIR, egressMsg, 
                                               ofaInMsg, ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               failedSet, recoveredElem, 
                                               toBeScheduledIRs, nextIRToSent, 
                                               monitoringEvent, msg >>

SwitchOfaRecovery(self) == /\ pc[self] = "SwitchOfaRecovery"
                           /\ ofaStartingMode(self[2])
                           /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                     "Failure of assertion at line 282, column 9 of macro called at line 720, column 61.")
                           /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = NotFailed]
                           /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                 THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                      /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                 swID |-> self[2],
                                                                                                 num |-> controlMsgCounter'[self[2]],
                                                                                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                      /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusResolveMsg'[self])
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << swSeqChangedStatus, 
                                                      controlMsgCounter, 
                                                      statusResolveMsg >>
                           /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                           /\ UNCHANGED << installedIRs, failedTimes, 
                                           NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                           Ofa2InstallerBuff, 
                                           Installer2OfaBuff, TCAM, 
                                           controller2Switch, 
                                           switch2Controller, controllerState, 
                                           IR2SW, controllerThreadPoolIRQueue, 
                                           IRStatus, SwSuspensionStatus, 
                                           lastScheduledThread, 
                                           SetScheduledIRs, dependencyGraph, 
                                           stack, ofaInIR, setIRs, nextThread, 
                                           nextIR, switchIDToReset, 
                                           setIRsToReset, resetIR, ingressIR, 
                                           egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, recoveredElem, 
                                           toBeScheduledIRs, nextIRToSent, 
                                           monitoringEvent, msg >>

SwitchInstallerRecovery(self) == /\ pc[self] = "SwitchInstallerRecovery"
                                 /\ installerInStartingMode(self[2])
                                 /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                           "Failure of assertion at line 320, column 9 of macro called at line 721, column 73.")
                                 /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                 /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                       THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                      "Failure of assertion at line 323, column 13 of macro called at line 721, column 73.")
                                            /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                            /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                       swID |-> self[2],
                                                                                                       num |-> controlMsgCounter'[self[2]],
                                                                                                       status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                            /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusResolveMsg'[self])
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << swSeqChangedStatus, 
                                                            controlMsgCounter, 
                                                            statusResolveMsg >>
                                 /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                                 /\ UNCHANGED << installedIRs, failedTimes, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Ofa2InstallerBuff, 
                                                 Installer2OfaBuff, TCAM, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 controllerState, IR2SW, 
                                                 controllerThreadPoolIRQueue, 
                                                 IRStatus, SwSuspensionStatus, 
                                                 lastScheduledThread, 
                                                 SetScheduledIRs, 
                                                 dependencyGraph, stack, 
                                                 ofaInIR, setIRs, nextThread, 
                                                 nextIR, switchIDToReset, 
                                                 setIRsToReset, resetIR, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, recoveredElem, 
                                                 toBeScheduledIRs, 
                                                 nextIRToSent, monitoringEvent, 
                                                 msg >>

swResolveFailure(self) == SwitchResolveFailure(self)
                             \/ SwitchCpuRecovery(self)
                             \/ SwitchNicAsicRecovery(self)
                             \/ SwitchOfaRecovery(self)
                             \/ SwitchInstallerRecovery(self)

ControllerSeqProc(self) == /\ pc[self] = "ControllerSeqProc"
                           /\ controllerIsMaster(self[1])
                           /\ pc' = [pc EXCEPT ![self] = "ControllerObj"]
                           /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                           installedIRs, failedTimes, 
                                           NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                           Ofa2InstallerBuff, 
                                           Installer2OfaBuff, TCAM, 
                                           controlMsgCounter, 
                                           controller2Switch, 
                                           switch2Controller, controllerState, 
                                           IR2SW, controllerThreadPoolIRQueue, 
                                           IRStatus, SwSuspensionStatus, 
                                           lastScheduledThread, 
                                           SetScheduledIRs, dependencyGraph, 
                                           stack, ofaInIR, setIRs, nextThread, 
                                           nextIR, switchIDToReset, 
                                           setIRsToReset, resetIR, ingressIR, 
                                           egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, toBeScheduledIRs, 
                                           nextIRToSent, monitoringEvent, msg >>

ControllerObj(self) == /\ pc[self] = "ControllerObj"
                       /\ IF ~isFinished /\ controllerIsMaster(self[1])
                             THEN /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1])]
                                  /\ toBeScheduledIRs'[self] # {}
                                  /\ /\ setIRs' = [setIRs EXCEPT ![self] = toBeScheduledIRs'[self]]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "scheduleIRs",
                                                                              pc        |->  "ControllerObj",
                                                                              nextThread |->  nextThread[self],
                                                                              nextIR    |->  nextIR[self],
                                                                              setIRs    |->  setIRs[self] ] >>
                                                                          \o stack[self]]
                                  /\ nextThread' = [nextThread EXCEPT ![self] = lastScheduledThread]
                                  /\ nextIR' = [nextIR EXCEPT ![self] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << stack, setIRs, nextThread, 
                                                  nextIR, toBeScheduledIRs >>
                       /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                       installedIRs, failedTimes, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Ofa2InstallerBuff, Installer2OfaBuff, 
                                       TCAM, controlMsgCounter, 
                                       controller2Switch, switch2Controller, 
                                       controllerState, IR2SW, 
                                       controllerThreadPoolIRQueue, IRStatus, 
                                       SwSuspensionStatus, lastScheduledThread, 
                                       SetScheduledIRs, dependencyGraph, 
                                       ofaInIR, switchIDToReset, setIRsToReset, 
                                       resetIR, ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       statusMsg, notFailedSet, failedElem, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, nextIRToSent, 
                                       monitoringEvent, msg >>

controllerSequencer(self) == ControllerSeqProc(self) \/ ControllerObj(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerIsMaster(self[1])
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIRs"]
                          /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                          installedIRs, failedTimes, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, Installer2OfaBuff, 
                                          TCAM, controlMsgCounter, 
                                          controller2Switch, switch2Controller, 
                                          controllerState, IR2SW, 
                                          controllerThreadPoolIRQueue, 
                                          IRStatus, SwSuspensionStatus, 
                                          lastScheduledThread, SetScheduledIRs, 
                                          dependencyGraph, stack, ofaInIR, 
                                          setIRs, nextThread, nextIR, 
                                          switchIDToReset, setIRsToReset, 
                                          resetIR, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, nextIRToSent, 
                                          monitoringEvent, msg >>

ControllerThreadSendIRs(self) == /\ pc[self] = "ControllerThreadSendIRs"
                                 /\ IF ~isFinished /\ controllerIsMaster(self[1])
                                       THEN /\ controllerThreadPoolIRQueue[self[1]] # <<>>
                                            /\ nextIRToSent' = [nextIRToSent EXCEPT ![self] = Head(controllerThreadPoolIRQueue[self[1]])]
                                            /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]] = Tail(controllerThreadPoolIRQueue[self[1]])]
                                            /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                            /\ UNCHANGED << controllerThreadPoolIRQueue, 
                                                            nextIRToSent >>
                                 /\ UNCHANGED << swSeqChangedStatus, 
                                                 switchStatus, installedIRs, 
                                                 failedTimes, NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Ofa2InstallerBuff, 
                                                 Installer2OfaBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 controllerState, IR2SW, 
                                                 IRStatus, SwSuspensionStatus, 
                                                 lastScheduledThread, 
                                                 SetScheduledIRs, 
                                                 dependencyGraph, stack, 
                                                 ofaInIR, setIRs, nextThread, 
                                                 nextIR, switchIDToReset, 
                                                 setIRsToReset, resetIR, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, 
                                                 monitoringEvent, msg >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ IF ~isSwitchSuspended(IR2SW[nextIRToSent[self]]) /\ IRStatus[nextIRToSent[self]] = IR_NONE
                                      THEN /\ IRStatus' = [IRStatus EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForIRToHaveCorrectStatus"]
                                           /\ UNCHANGED IRStatus
                                /\ UNCHANGED << swSeqChangedStatus, 
                                                switchStatus, installedIRs, 
                                                failedTimes, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Ofa2InstallerBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                controllerState, IR2SW, 
                                                controllerThreadPoolIRQueue, 
                                                SwSuspensionStatus, 
                                                lastScheduledThread, 
                                                SetScheduledIRs, 
                                                dependencyGraph, stack, 
                                                ofaInIR, setIRs, nextThread, 
                                                nextIR, switchIDToReset, 
                                                setIRsToReset, resetIR, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIRToSent, 
                                                monitoringEvent, msg >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controller2Switch' = [controller2Switch EXCEPT ![IR2SW[nextIRToSent[self]]] = Append(controller2Switch[IR2SW[nextIRToSent[self]]], [type |-> INSTALL_FLOW,
                                                                                                                                                                          to |-> IR2SW[nextIRToSent[self]],
                                                                                                                                                                          IR |-> nextIRToSent[self]])]
                                   /\ pc' = [pc EXCEPT ![self] = "WaitForIRToHaveCorrectStatus"]
                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                   switchStatus, installedIRs, 
                                                   failedTimes, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Ofa2InstallerBuff, 
                                                   Installer2OfaBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switch2Controller, 
                                                   controllerState, IR2SW, 
                                                   controllerThreadPoolIRQueue, 
                                                   IRStatus, 
                                                   SwSuspensionStatus, 
                                                   lastScheduledThread, 
                                                   SetScheduledIRs, 
                                                   dependencyGraph, stack, 
                                                   ofaInIR, setIRs, nextThread, 
                                                   nextIR, switchIDToReset, 
                                                   setIRsToReset, resetIR, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, 
                                                   nextIRToSent, 
                                                   monitoringEvent, msg >>

WaitForIRToHaveCorrectStatus(self) == /\ pc[self] = "WaitForIRToHaveCorrectStatus"
                                      /\ ~isSwitchSuspended(IR2SW[nextIRToSent[self]])
                                      /\ pc' = [pc EXCEPT ![self] = "ReScheduleifIRNone"]
                                      /\ UNCHANGED << swSeqChangedStatus, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      failedTimes, 
                                                      NicAsic2OfaBuff, 
                                                      Ofa2NicAsicBuff, 
                                                      Ofa2InstallerBuff, 
                                                      Installer2OfaBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      controllerState, IR2SW, 
                                                      controllerThreadPoolIRQueue, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      dependencyGraph, stack, 
                                                      ofaInIR, setIRs, 
                                                      nextThread, nextIR, 
                                                      switchIDToReset, 
                                                      setIRsToReset, resetIR, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, 
                                                      nextIRToSent, 
                                                      monitoringEvent, msg >>

ReScheduleifIRNone(self) == /\ pc[self] = "ReScheduleifIRNone"
                            /\ IF IRStatus[nextIRToSent[self]] = IR_NONE
                                  THEN /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                            /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                            installedIRs, failedTimes, 
                                            NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                            Ofa2InstallerBuff, 
                                            Installer2OfaBuff, TCAM, 
                                            controlMsgCounter, 
                                            controller2Switch, 
                                            switch2Controller, controllerState, 
                                            IR2SW, controllerThreadPoolIRQueue, 
                                            IRStatus, SwSuspensionStatus, 
                                            lastScheduledThread, 
                                            SetScheduledIRs, dependencyGraph, 
                                            stack, ofaInIR, setIRs, nextThread, 
                                            nextIR, switchIDToReset, 
                                            setIRsToReset, resetIR, ingressIR, 
                                            egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            toBeScheduledIRs, nextIRToSent, 
                                            monitoringEvent, msg >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ Assert(nextIRToSent[self] \in SetScheduledIRs[self[1]][IR2SW[nextIRToSent[self]]], 
                                            "Failure of assertion at line 775, column 13.")
                                  /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![self[1]][IR2SW[nextIRToSent[self]]] = SetScheduledIRs[self[1]][IR2SW[nextIRToSent[self]]]\{nextIRToSent[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIRs"]
                                  /\ UNCHANGED << swSeqChangedStatus, 
                                                  switchStatus, installedIRs, 
                                                  failedTimes, NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Ofa2InstallerBuff, 
                                                  Installer2OfaBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  controllerState, IR2SW, 
                                                  controllerThreadPoolIRQueue, 
                                                  IRStatus, SwSuspensionStatus, 
                                                  lastScheduledThread, 
                                                  dependencyGraph, stack, 
                                                  ofaInIR, setIRs, nextThread, 
                                                  nextIR, switchIDToReset, 
                                                  setIRsToReset, resetIR, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, 
                                                  toBeScheduledIRs, 
                                                  nextIRToSent, 
                                                  monitoringEvent, msg >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIRs(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ WaitForIRToHaveCorrectStatus(self)
                                    \/ ReScheduleifIRNone(self)
                                    \/ RemoveFromScheduledIRSet(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerIsMaster(self[1])
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerTrack"]
                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                    switchStatus, installedIRs, 
                                                    failedTimes, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Ofa2InstallerBuff, 
                                                    Installer2OfaBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    controllerState, IR2SW, 
                                                    controllerThreadPoolIRQueue, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    lastScheduledThread, 
                                                    SetScheduledIRs, 
                                                    dependencyGraph, stack, 
                                                    ofaInIR, setIRs, 
                                                    nextThread, nextIR, 
                                                    switchIDToReset, 
                                                    setIRsToReset, resetIR, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, 
                                                    nextIRToSent, 
                                                    monitoringEvent, msg >>

ControllerTrack(self) == /\ pc[self] = "ControllerTrack"
                         /\ IF ~isFinished /\ controllerIsMaster(self[1])
                               THEN /\ swSeqChangedStatus # <<>>
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTrack"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                    monitoringEvent >>
                         /\ UNCHANGED << switchStatus, installedIRs, 
                                         failedTimes, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Ofa2InstallerBuff, 
                                         Installer2OfaBuff, TCAM, 
                                         controlMsgCounter, controller2Switch, 
                                         switch2Controller, controllerState, 
                                         IR2SW, controllerThreadPoolIRQueue, 
                                         IRStatus, SwSuspensionStatus, 
                                         lastScheduledThread, SetScheduledIRs, 
                                         dependencyGraph, stack, ofaInIR, 
                                         setIRs, nextThread, nextIR, 
                                         switchIDToReset, setIRsToReset, 
                                         resetIR, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         toBeScheduledIRs, nextIRToSent, msg >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                             /\ pc' = [pc EXCEPT ![self] = "ControllerTrack"]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             stack, ofaInIR, setIRs, 
                                             nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, toBeScheduledIRs, 
                                             nextIRToSent, monitoringEvent, 
                                             msg >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                   switchStatus, installedIRs, 
                                                   failedTimes, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Ofa2InstallerBuff, 
                                                   Installer2OfaBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   controllerState, IR2SW, 
                                                   controllerThreadPoolIRQueue, 
                                                   IRStatus, 
                                                   lastScheduledThread, 
                                                   SetScheduledIRs, 
                                                   dependencyGraph, stack, 
                                                   ofaInIR, setIRs, nextThread, 
                                                   nextIR, switchIDToReset, 
                                                   setIRsToReset, resetIR, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, 
                                                   nextIRToSent, 
                                                   monitoringEvent, msg >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "resetStateWithRecoveredSW",
                                                                                                 pc        |->  "ControllerTrack",
                                                                                                 setIRsToReset |->  setIRsToReset[self],
                                                                                                 resetIR   |->  resetIR[self],
                                                                                                 switchIDToReset |->  switchIDToReset[self] ] >>
                                                                                             \o stack[self]]
                                                        /\ switchIDToReset' = [switchIDToReset EXCEPT ![self] = monitoringEvent[self].swID]
                                                     /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = {}]
                                                     /\ resetIR' = [resetIR EXCEPT ![self] = 0]
                                                     /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTrack"]
                                                     /\ UNCHANGED << stack, 
                                                                     switchIDToReset, 
                                                                     setIRsToReset, 
                                                                     resetIR >>
                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                          switchStatus, 
                                                          installedIRs, 
                                                          failedTimes, 
                                                          NicAsic2OfaBuff, 
                                                          Ofa2NicAsicBuff, 
                                                          Ofa2InstallerBuff, 
                                                          Installer2OfaBuff, 
                                                          TCAM, 
                                                          controlMsgCounter, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          controllerState, 
                                                          IR2SW, 
                                                          controllerThreadPoolIRQueue, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          lastScheduledThread, 
                                                          SetScheduledIRs, 
                                                          dependencyGraph, 
                                                          ofaInIR, setIRs, 
                                                          nextThread, nextIR, 
                                                          ingressIR, egressMsg, 
                                                          ofaInMsg, 
                                                          ofaOutConfirmation, 
                                                          installerInIR, 
                                                          statusMsg, 
                                                          notFailedSet, 
                                                          failedElem, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, 
                                                          toBeScheduledIRs, 
                                                          nextIRToSent, 
                                                          monitoringEvent, msg >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerTrack(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ controllerIsMaster(self[1])
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorProc"]
                                       /\ UNCHANGED << swSeqChangedStatus, 
                                                       switchStatus, 
                                                       installedIRs, 
                                                       failedTimes, 
                                                       NicAsic2OfaBuff, 
                                                       Ofa2NicAsicBuff, 
                                                       Ofa2InstallerBuff, 
                                                       Installer2OfaBuff, TCAM, 
                                                       controlMsgCounter, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       controllerState, IR2SW, 
                                                       controllerThreadPoolIRQueue, 
                                                       IRStatus, 
                                                       SwSuspensionStatus, 
                                                       lastScheduledThread, 
                                                       SetScheduledIRs, 
                                                       dependencyGraph, stack, 
                                                       ofaInIR, setIRs, 
                                                       nextThread, nextIR, 
                                                       switchIDToReset, 
                                                       setIRsToReset, resetIR, 
                                                       ingressIR, egressMsg, 
                                                       ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       toBeScheduledIRs, 
                                                       nextIRToSent, 
                                                       monitoringEvent, msg >>

ControllerMonitorProc(self) == /\ pc[self] = "ControllerMonitorProc"
                               /\ IF ~isFinished /\ controllerIsMaster(self[1])
                                     THEN /\ switch2Controller # <<>>
                                          /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                          /\ switch2Controller' = Tail(switch2Controller)
                                          /\ Assert(msg'[self].from = IR2SW[msg'[self].IR], 
                                                    "Failure of assertion at line 818, column 9.")
                                          /\ Assert(msg'[self].type \in {RECONCILIATION_RESPONSE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                    "Failure of assertion at line 819, column 9.")
                                          /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIR2"]
                                                ELSE /\ Assert(FALSE, 
                                                               "Failure of assertion at line 839, column 18.")
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorProc"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                          /\ UNCHANGED << switch2Controller, 
                                                          msg >>
                               /\ UNCHANGED << swSeqChangedStatus, 
                                               switchStatus, installedIRs, 
                                               failedTimes, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Ofa2InstallerBuff, 
                                               Installer2OfaBuff, TCAM, 
                                               controlMsgCounter, 
                                               controller2Switch, 
                                               controllerState, IR2SW, 
                                               controllerThreadPoolIRQueue, 
                                               IRStatus, SwSuspensionStatus, 
                                               lastScheduledThread, 
                                               SetScheduledIRs, 
                                               dependencyGraph, stack, ofaInIR, 
                                               setIRs, nextThread, nextIR, 
                                               switchIDToReset, setIRsToReset, 
                                               resetIR, ingressIR, egressMsg, 
                                               ofaInMsg, ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, toBeScheduledIRs, 
                                               nextIRToSent, monitoringEvent >>

ControllerUpdateIR2(self) == /\ pc[self] = "ControllerUpdateIR2"
                             /\ IRStatus' = [IRStatus EXCEPT ![msg[self].IR] = IR_DONE]
                             /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorProc"]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             stack, ofaInIR, setIRs, 
                                             nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, toBeScheduledIRs, 
                                             nextIRToSent, monitoringEvent, 
                                             msg >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ ControllerMonitorProc(self)
                                       \/ ControllerUpdateIR2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ ofaInstallFlowEntry(self)
                               \/ scheduleIRs(self)
                               \/ resetStateWithRecoveredSW(self))
           \/ (\E self \in ({NIC_ASIC_IN} \X SW): swNicAsicProcPacketIn(self))
           \/ (\E self \in ({NIC_ASIC_OUT} \X SW): swNicAsicProcPacketOut(self))
           \/ (\E self \in ({OFA_IN} \X SW): ofaModuleProcPacketIn(self))
           \/ (\E self \in ({OFA_OUT} \X SW): ofaModuleProcPacketOut(self))
           \/ (\E self \in ({INSTALLER} \X SW): installerModuleProc(self))
           \/ (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
           \/ (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
           \/ (\E self \in ({c0, c1} \X {CONT_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({c0, c1} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({c0, c1} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({c0, c1} \X {CONT_MONITOR}): controllerMonitoringServer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({NIC_ASIC_IN} \X SW) : WF_vars(swNicAsicProcPacketIn(self))
        /\ \A self \in ({NIC_ASIC_OUT} \X SW) : WF_vars(swNicAsicProcPacketOut(self))
        /\ \A self \in ({OFA_IN} \X SW) : /\ WF_vars(ofaModuleProcPacketIn(self))
                                          /\ WF_vars(ofaInstallFlowEntry(self))
        /\ \A self \in ({OFA_OUT} \X SW) : WF_vars(ofaModuleProcPacketOut(self))
        /\ \A self \in ({INSTALLER} \X SW) : WF_vars(installerModuleProc(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(swResolveFailure(self))
        /\ \A self \in ({c0, c1} \X {CONT_SEQ}) : WF_vars(controllerSequencer(self)) /\ WF_vars(scheduleIRs(self))
        /\ \A self \in ({c0, c1} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({c0, c1} \X {CONT_EVENT}) : /\ WF_vars(controllerEventHandler(self))
                                                    /\ WF_vars(resetStateWithRecoveredSW(self))
        /\ \A self \in ({c0, c1} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-289dd9a47aba06a4e2b0edcba0a5c1d6
SwProcSet == (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) 
ContProcSet == (({c0, c1} \X {CONT_SEQ})) \cup (({c0, c1} \X CONTROLLER_THREAD_POOL)) \cup (({c0, c1} \X {CONT_EVENT})) \cup (({c0, c1} \X {CONT_MONITOR}))


SystemFinished == <>(/\ \A self \in SwProcSet: pc[self] = "Done" 
                     /\ \A self \in ContProcSet: \/ /\ controllerState.c1 = "backup"
                                                       \/ self[1] = c1
                                                       \/ /\ self[1] = c0 
                                                          /\ pc[self] = "Done"
                                                 \/ /\ controllerState.c1 = "primary" 
                                                    /\ pc[self] = "Done")
                                                            
AllInstalled == <>[](\A x \in 1..MaxNumIRs: \E y \in DOMAIN installedIRs: installedIRs[y] = x)
AllDoneStatusController == <>[](\A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE)
ConsistencyReq == <>[](\A <<x,y>> \in dependencyGraph: \/ y = 0
                                                       \/ \E z, w \in DOMAIN installedIRs: /\ installedIRs[z] = x
                                                                                           /\ installedIRs[w] = y
                                                                                           /\ z < w )


=============================================================================
\* Modification History
\* Last modified Thu Sep 03 03:34:09 UTC 2020 by root
\* Created Sat Aug 08 17:44:35 UTC 2020 by root

--------------------------- MODULE SwitchFailure ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS SW, c0, c1, CONTROLLER_THREAD_POOL, MaxNumIRs,
          NotFailed, Failed, MAX_NUM_SW_FAILURE, IR_NONE, IR_SENT, IR_PENDING, IR_DONE, SW_SUSPEND, SW_RUN,
          RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, SW_UP, SW_DOWN, KEEP_ALIVE, IR_RECONCILE,
          NIC_ASIC_IN, NIC_ASIC_OUT, OFA_IN, OFA_OUT, INSTALLER, SW_FAILURE_PROC, SW_RESOLVE_PROC,
          CONT_SEQ, CONT_MONITOR, CONT_EVENT, NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN,
          INSTALLER_UP, RECONCILIATION_REQUEST, RECONCILIATION_RESPONSE, INSTALL_FLOW, STATUS_NONE,
          SW_SIMPLE_ID, SW_SIMPLE_MODEL, SW_COMPLEX_MODEL, NO_LOCK, GHOST_UNLOCK_PROC, PRINT_PROC
          
ASSUME Cardinality(SW) >= MaxNumIRs

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
              switchOrdering = CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z],
              IR2SW =  CHOOSE x \in [1..Cardinality(SW) -> SW]: ~\E y, z \in DOMAIN x: /\ y > z 
                                                                                        /\ switchOrdering[x[y]] =< switchOrdering[x[z]],
              controllerThreadPoolIRQueue = [y \in {c0, c1} |-> <<>>], 
              IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
              SwSuspensionStatus = [x \in SW |-> SW_RUN],
              lastScheduledThread = 0,
              SetScheduledIRs = [x \in {c0, c1} |-> [y \in SW |-> {}]],
              \**************** Dependency Graph Definition **************
\*              dependencyGraph \in PlausibleDependencySet,
              dependencyGraph \in generateConnectedDAG(1..MaxNumIRs),
              \**************** Ghost Variables *************************
              workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
              workerThreadStatus = [x \in CONTROLLER_THREAD_POOL |-> 0],
              switchLock = <<NO_LOCK, NO_LOCK>>,
              FirstInstall = [x \in 1..MaxNumIRs |-> 0]
    define
    
         max(set) == CHOOSE x \in set: \A y \in set: x \geq y
         min(set) == CHOOSE x \in set: \A y \in set: x \leq y 
         rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
         isFinished == \A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE
        
         RECURSIVE sum(_, _)
         sum(seqS, indexToSum) == IF indexToSum = 0
                                  THEN 
                                     0
                                  ELSE
                                     IF indexToSum = 1
                                     THEN
                                         seqS[1]
                                  ELSE
                                     seqS[1] + sum(Tail(seqS), indexToSum - 1)
        
         RECURSIVE Paths(_, _)
         Paths(n, G) ==  IF n = 1
                         THEN 
                           G
                         ELSE
                             LET nextVs(p) == { e[2] : e \in {e \in G : e[1] = p[Len(p)]} }
                                 nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
                             IN
                             UNION {nextPaths(p) : p \in Paths(n-1, G)} \cup Paths(n-1, G)
                            
        RECURSIVE AllPossibleSizes(_, _)
        AllPossibleSizes(maxSize, sumUpToNow) == IF sumUpToNow = 0
                                                 THEN
                                                     {<<0>>}
                                                 ELSE
                                                     LET Upperbound == min({sumUpToNow, maxSize})
                                                     IN
                                                     UNION {{<<x>> \o y: y \in AllPossibleSizes(x, sumUpToNow-x)}: x \in 1..Upperbound}  
        
         generateConnectedDAG(S) == {x \in SUBSET (S \X S): /\ ~\E y \in S: <<y, y>> \in x
                                                            /\ ~\E y, z \in S: /\  <<y, z>> \in x 
                                                                               /\  <<z, y>> \in x
                                                            /\ \A y \in S: ~\E z \in S: /\ <<z, y>> \in x
                                                                                        /\ z >= y
                                                            /\ \/ Cardinality(S) = 1
                                                               \/ \A y \in S: \E z \in S: \/ <<y, z>> \in x
                                                                                          \/ <<z, y>> \in x
                                                            /\ \/ x = {}
                                                               \/ ~\E p1, p2 \in Paths(Cardinality(x), x): /\ p1 # p2
                                                                                                           /\ p1[1] = p2[1]
                                                                                                           /\ p2[Len(p2)] = p1[Len(p1)]
                                                            /\ Cardinality(x) >= Cardinality(S) - 1                                                                                                                        
                                                            /\  \/ x = {}
                                                                \/ \A p \in Paths(Cardinality(x), x): \/ Len(p) = 1
                                                                                                      \/ p[1] # p[Len(p)]}
        SetSetUnion(Aset, Bset) == {x \cup y: x \in Aset, y \in Bset}
       
        RECURSIVE GeneralSetSetUnion(_)
        GeneralSetSetUnion(A) == IF Cardinality(A) = 1
                                 THEN
                                     CHOOSE x \in A: TRUE
                                 ELSE 
                                     LET
                                         rndA1 == CHOOSE x \in A:TRUE
                                         rndA2 == CHOOSE x \in A\{rndA1}: TRUE
                                     IN
                                         GeneralSetSetUnion({SetSetUnion(rndA1, rndA2)} \cup (A\{rndA1, rndA2}))
                                        
        PlausibleDependencySet == UNION {GeneralSetSetUnion({generateConnectedDAG(((sum(allSizes, y-1) + 1)..(sum(allSizes, y)))): y \in 1..(Len(allSizes) - 1)}): allSizes \in AllPossibleSizes(MaxNumIRs, MaxNumIRs)} 
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
                                                               
        \* getIRToSentNext(TID) == controllerThreadPoolIRQueue[TID[1]][TID[2]]
        \*                                    [CHOOSE x \in DOMAIN controllerThreadPoolIRQueue[TID[1]][TID[2]]: 
        \*                                        ~\E y \in DOMAIN controllerThreadPoolIRQueue[TID[1]][TID[2]]: /\ y < x
        \*                                                                                                      /\ IRStatus[controllerThreadPoolIRQueue[TID[1]][TID[2]][y]] = IR_NONE]
        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                        /\ swSeqChangedStatus[x].num > monEvent.num
        installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerProc" 
        ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaProcIn"
                                 /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaProcOut"
        nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchRcvPacket"
                                     /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchFromOFAPacket"
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
        canWorkerThreadContinue(CID, threadID) == /\ Len(controllerThreadPoolIRQueue[CID]) > 0
                                                  /\ workerThreadRanking[threadID] = min({workerThreadRanking[z]: z \in {y \in CONTROLLER_THREAD_POOL: workerThreadStatus[y] = 0}})
        whichSwitchModel(swID) == IF MAX_NUM_SW_FAILURE = 0
                                    THEN SW_SIMPLE_MODEL
                                    ELSE SW_COMPLEX_MODEL                            
    end define 
    
    \* ------------------------------------------------------------------
    \* -                   Switches (Macros)                            -
    \* ------------------------------------------------------------------
    
    \* ======= NIC/ASIC Failure ========
    macro nicAsicFailure()
    begin
        assert switchStatus[self[2]].nicAsic = NotFailed;
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
        assert switchStatus[self[2]].nicAsic = Failed;
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
        assert switchStatus[self[2]].cpu = NotFailed;
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
        assert switchStatus[self[2]].cpu = Failed;
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
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed;
        switchStatus[self[2]].ofa := Failed;
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
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = Failed;
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
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed;
        switchStatus[self[2]].installer := Failed;
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
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = Failed;
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
    
    \* ===========Wait for Lock==========
    macro switchWaitForLock()
    begin
        await switchLock \in {<<NO_LOCK, NO_LOCK>>, self};
    end macro;
    \* =================================
    
    \* ===========Acquire Lock==========
    macro acquireLock()
    begin
        switchWaitForLock();
        switchLock := self;
    end macro;
    \* =================================
        
    \* ====== Acquire & Change Lock =====
    macro acquireAndChangeLock(nextLockHolder)
    begin
        switchWaitForLock();
        switchLock := nextLockHolder;
    end macro;
    \* =================================
    
    \* ========= Release Lock ==========
    macro releaseLock(prevLockHolder)
    begin
        assert \/ switchLock[2] = prevLockHolder[2]
               \/ switchLock[2] = NO_LOCK;
        switchLock := <<NO_LOCK, NO_LOCK>>;
    end macro;
    \* =================================
    
    \* ========= Is Lock free ==========
    macro waitForLockFree()
    begin
        await switchLock = <<NO_LOCK, NO_LOCK>>;
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
    (*procedure ofaInstallFlowEntry(ofaInIR = 0)
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
    end procedure*)
    
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
        waitForLockFree();
        assert IRStatus[nextIR] \in {IR_NONE, IR_DONE};
               \*\/ /\ IRStatus[nextIR] = IR_SUSPEND
               \*   /\ SwSuspensionStatus[IR2SW[nextIR]] = SW_RUN;
        AddToScheduleIRSet: 
            waitForLockFree();
            assert nextIR \notin SetScheduledIRs[self[1]][IR2SW[nextIR]];
            SetScheduledIRs[self[1]][IR2SW[nextIR]] := SetScheduledIRs[self[1]][IR2SW[nextIR]] \cup {nextIR};
        ScheduleTheIR:
            waitForLockFree();
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
    
    \* ------------------------------------------------------------------
    \* -                   Switches SIMPLE Model                        -
    \* ------------------------------------------------------------------
    fair process swProcess \in ({SW_SIMPLE_ID} \X SW)
    variables ingressPkt = [type |-> 0]
    begin
    SwitchSimpleProcess:
    while TRUE do
        await whichSwitchModel(self[2]) = SW_SIMPLE_MODEL;          
        await Len(controller2Switch[self[2]]) > 0;
        ingressPkt := Head(controller2Switch[self[2]]);
        assert ingressPkt.type = INSTALL_FLOW;
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        installedIRs := Append(installedIRs, ingressPkt.IR);
        TCAM[self[2]] := Append(TCAM[self[2]], ingressPkt.IR);
        switch2Controller := Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                        from |-> self[2],
                                                        IR |-> ingressPkt.IR]);
        
    end while;
    end process;
    \* ------------------------------------------------------------------
    \* -                   Switches COMPLEX (Modules)                   -
    \* ------------------------------------------------------------------
    
    \* ======== NIC/ASIC Module ========
    fair process swNicAsicProcPacketIn \in ({NIC_ASIC_IN} \X SW)
    variables ingressIR = [type |-> 0]
    begin
    SwitchRcvPacket:
    while TRUE do
        await whichSwitchModel(self[2]) = SW_COMPLEX_MODEL;
        await swCanReceivePackets(self[2]);
        await Len(controller2Switch[self[2]]) > 0;
        ingressIR := Head(controller2Switch[self[2]]);
        assert \/ ingressIR.type = RECONCILIATION_REQUEST
               \/ ingressIR.type = INSTALL_FLOW;
        acquireLock();
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        \* Process packet
        SwitchNicAsicInsertToOfaBuff:
            if swCanReceivePackets(self[2]) then
                acquireAndChangeLock(<<OFA_IN, self[2]>>);
                NicAsic2OfaBuff[self[2]] := Append(NicAsic2OfaBuff[self[2]], ingressIR);
            else
                ingressIR := [type |-> 0];
                goto SwitchRcvPacket;
            end if;
    end while;
    end process
    
    fair process swNicAsicProcPacketOut \in ({NIC_ASIC_OUT} \X SW)
    variables egressMsg = [type |-> 0]
    begin
    SwitchFromOFAPacket:
    while TRUE do
        await swCanReceivePackets(self[2]);
        await  Len(Ofa2NicAsicBuff[self[2]]) > 0;
        egressMsg := Head(Ofa2NicAsicBuff[self[2]]);
        acquireLock();
        assert \/ egressMsg.type = INSTALLED_SUCCESSFULLY
               \/ egressMsg.type = RECEIVED_SUCCESSFULLY
               \/ egressMsg.type = RECONCILIATION_RESPONSE;
        Ofa2NicAsicBuff[self[2]] := Tail(Ofa2NicAsicBuff[self[2]]);
        \* Process Msg
        SwitchNicAsicSendOutMsg:
            if swCanReceivePackets(self[2]) then
                switchWaitForLock();
                releaseLock(self);
                switch2Controller := Append(switch2Controller, egressMsg);
            else
                egressMsg := [type |-> 0];
                goto SwitchFromOFAPacket;
            end if;
    end while;
    end process
    \* =================================
    
    \* ========== OFA Module ===========
    fair process ofaModuleProcPacketIn \in ({OFA_IN} \X SW)
    variables ofaInMsg = [type |-> 0]
    begin
    \* OFA process the packets and sends packet to Installer
    SwitchOfaProcIn: 
    while TRUE do
        await swOFACanProcessIRs(self[2]);
        await Len(NicAsic2OfaBuff[self[2]]) > 0;
        acquireLock();
        ofaInMsg := Head(NicAsic2OfaBuff[self[2]]);           
        assert ofaInMsg.to = self[2];
        assert ofaInMsg.IR  \in 1..MaxNumIRs;
        NicAsic2OfaBuff[self[2]] := Tail(NicAsic2OfaBuff[self[2]]);
        
        SwitchOfaProcessPacket:
           if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<INSTALLER, self[2]>>);
                if ofaInMsg.type = INSTALL_FLOW then
                \* call ofaInstallFlowEntry(ofaInMsg.IR)
                    Ofa2InstallerBuff[self[2]] := Append(Ofa2InstallerBuff[self[2]], ofaInMsg.IR);
                \*elsif ofaInMsg.type = RECONCILIATION_REQUEST then
                \*     call ofaProcessReconcileRequest(ofaInMsg.IR); 
                else
                    assert FALSE;               
                end if;
           else
                ofaInMsg := [type |-> 0];
                goto SwitchOfaProcIn;
           end if;
    end while    
    end process
    
    fair process ofaModuleProcPacketOut \in ({OFA_OUT} \X SW)
    variables ofaOutConfirmation = 0
    begin
    SwitchOfaProcOut:
    while TRUE do
        await swOFACanProcessIRs(self[2]);
        await Installer2OfaBuff[self[2]] # <<>>;
        acquireLock();
        ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
        Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
        assert ofaOutConfirmation \in 1..MaxNumIRs;
        
        SendInstallationConfirmation:
            if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                              from |-> self[2],
                                                                              IR |-> ofaOutConfirmation]);
                \* OfaCacheInstalled[self[2]] := OfaCacheInstalled[self[2]] \cup {ofaOutConfirmation};                
            else 
                ofaOutConfirmation := 0;
                goto SwitchOfaProcOut;
            end if;                                                              
    end while;                                                                      
    end process
    \* =================================
    
    \* ======= Installer Module ========
    fair process installerModuleProc \in ({INSTALLER} \X SW)
    variables installerInIR = 0
    begin
    \* Installer installs the packet into TCAM
    SwitchInstallerProc: 
    while TRUE do      
       await swCanInstallIRs(self[2]);
       await Len(Ofa2InstallerBuff[self[2]]) > 0;
       acquireLock();
       installerInIR := Head(Ofa2InstallerBuff[self[2]]);
       assert installerInIR \in 1..MaxNumIRs;
       Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);
       \* Process packet
       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then 
                acquireLock();     
                installedIRs := Append(installedIRs, installerInIR);
                TCAM[self[2]] := Append(TCAM[self[2]], installerInIR);
            else
                installerInIR := 0;
                goto SwitchInstallerProc;
            end if;
            
       SwitchInstallerSendConfirmation:
            if swCanInstallIRs(self[2]) then
                acquireAndChangeLock(<<OFA_OUT, self[2]>>);
                Installer2OfaBuff[self[2]] := Append(Installer2OfaBuff[self[2]], installerInIR);
            else
                installerInIR := 0;
                goto SwitchInstallerProc;
            end if;
    end while;
    end process
    \* =================================
    
    \* ======= Failure Proccess=========
    fair process swFailureProc \in ({SW_FAILURE_PROC} \X SW)
    variable statusMsg = <<>>, notFailedSet = {}, failedElem = "";
    begin
    SwitchFailure:
    while TRUE do 
        notFailedSet := returnSwitchElementsNotFailed(self[2]);
        await notFailedSet # {}; 
        await failedTimes[self[2]] < MAX_NUM_SW_FAILURE;
        await ~isFinished;
        await \/ switchLock = <<NO_LOCK, NO_LOCK>>
              \/ switchLock[2] = self[2];
        with elem \in notFailedSet do
            failedElem := elem;
        end with;
        
        if failedElem = "cpu" then 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                cpuFailure();
        elsif failedElem = "ofa" then 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                ofaFailure();
        elsif failedElem = "installer" then 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                installerFailure();
        elsif failedElem = "nicAsic" then 
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
                nicAsicFailure();
        else assert FALSE;
        end if;
        
        releaseLock(self);
    end while
    end process
    \* =================================
    
    \* ==== Failure Resolve Process ====
    fair process swResolveFailure \in ({SW_RESOLVE_PROC} \X SW)
    variable failedSet = {}, statusResolveMsg = <<>>, recoveredElem = "";
    begin
    SwitchResolveFailure:
    while TRUE do
        failedSet := returnSwitchFailedElements(self[2]);
        await Cardinality(failedSet) > 0;
        await switchLock = <<NO_LOCK, NO_LOCK>>;
        await ~isFinished;
        with elem \in failedSet do
            recoveredElem := elem;
        end with;
        
        if recoveredElem = "cpu" then resolveCpuFailure();
        elsif recoveredElem = "nicAsic" then resolveNicAsicFailure();
        elsif recoveredElem = "ofa" then resolveOfaFailure();
        elsif recoveredElem = "installer" then resolveInstallerFailure();
        else assert FALSE;
        end if;
        
    end while
    end process
    \* =================================
    
    \* ======== Ghost UNLOCK ===========
    fair process ghostUnlockProcess \in ({GHOST_UNLOCK_PROC} \X SW)
    begin
    ghostProc:
    while TRUE do
        await /\ switchLock # <<NO_LOCK, NO_LOCK>>
              /\ switchLock[2] = self[2];
        if switchStatus[switchLock[2]].cpu = Failed /\ switchLock[1] = NIC_ASIC_OUT then
            await pc[switchLock] = "SwitchFromOFAPacket";
        else
            if switchLock[1] \in {NIC_ASIC_IN, NIC_ASIC_OUT} then 
                await switchStatus[switchLock[2]].nicAsic = Failed;
                await /\ pc[<<NIC_ASIC_IN, self[2]>>] = "SwitchRcvPacket"
                      /\ pc[<<NIC_ASIC_OUT, self[2]>>] = "SwitchFromOFAPacket"; 
            elsif switchLock[1] \in {OFA_IN, OFA_OUT} then 
                await switchStatus[switchLock[2]].ofa = Failed;
                await /\ pc[<<OFA_IN, self[2]>>] = "SwitchOfaProcIn"
                      /\ pc[<<OFA_OUT, self[2]>>] = "SwitchOfaProcOut";
            elsif switchLock[1] \in {INSTALLER} then
                await switchStatus[switchLock[2]].installer = Failed;
                await pc[<<INSTALLER, self[2]>>] = "SwitchInstallerProc"; 
            end if;
        end if;
        releaseLock(self);
    end while
    end process
    \* =================================
    
    \* ------------------------------------------------------------------
    \* -                   Controller (Modules)                         -
    \* ------------------------------------------------------------------
   
    \* ======= Sequencer ========
    fair process controllerSequencer \in ({c0} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}
    begin
    ControllerSeqProc:
    while TRUE do
        await controllerIsMaster(self[1]);
        waitForLockFree();
        toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1]);
        await toBeScheduledIRs # {};
        call scheduleIRs(toBeScheduledIRs);                                                
    end while;
    end process
    \* ==========================
    
    \* ====== Thread Pool ======= 
    fair process controllerWorkerThreads \in ({c0} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = 0; 
    begin
    ControllerThread:
    while TRUE do
        await controllerIsMaster(self[1]);
        await controllerThreadPoolIRQueue[self[1]] # <<>>;
        await canWorkerThreadContinue(self[1], self[2]);
        waitForLockFree();
        workerThreadStatus[self[2]] := 1;
        nextIRToSent := Head(controllerThreadPoolIRQueue[self[1]]);
        controllerThreadPoolIRQueue[self[1]] := Tail(controllerThreadPoolIRQueue[self[1]]);        
        ControllerThreadSendIR:
            waitForLockFree();
            if ~isSwitchSuspended(IR2SW[nextIRToSent]) /\ IRStatus[nextIRToSent] = IR_NONE then 
                IRStatus[nextIRToSent] := IR_SENT;
                ControllerThreadForwardIR: 
                    waitForLockFree();
                    controllerSendIR(nextIRToSent);
            end if;
        WaitForIRToHaveCorrectStatus:
            waitForLockFree();
            await ~isSwitchSuspended(IR2SW[nextIRToSent]);
        ReScheduleifIRNone:
            waitForLockFree();
            if IRStatus[nextIRToSent] = IR_NONE then 
                goto ControllerThreadSendIR;
            end if;
        RemoveFromScheduledIRSet:
            waitForLockFree();
            assert nextIRToSent \in SetScheduledIRs[self[1]][IR2SW[nextIRToSent]];
            SetScheduledIRs[self[1]][IR2SW[nextIRToSent]] := SetScheduledIRs[self[1]][IR2SW[nextIRToSent]]\{nextIRToSent};
            workerThreadStatus[self[2]] := 0;
    end while;
    end process
    \* ==========================
    
    \* ===== Event Handler ======
    fair process controllerEventHandler \in ({c0} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0]
    begin 
    ControllerEventHandlerProc:
    while TRUE do 
         await controllerIsMaster(self[1]);   
         await swSeqChangedStatus # <<>>;
         waitForLockFree();
         monitoringEvent := Head(swSeqChangedStatus);
         swSeqChangedStatus := Tail(swSeqChangedStatus);
         if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            ControllerSuspendSW: 
                waitForLockFree();
                SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;        
         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            \*call suspendInSchedulingIRs(monitoringEvent.swID);
            ControllerFreeSuspendedSW: 
                waitForLockFree();
                SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
            ControllerCheckIfThisIsLastEvent:
                waitForLockFree();
                if ~existsMonitoringEventHigherNum(monitoringEvent) then
                    \* call reconcileStateWithRecoveredSW(monitoringEvent.swID);
                    call resetStateWithRecoveredSW(monitoringEvent.swID); 
                end if;
         end if;
    end while;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    fair process controllerMonitoringServer \in ({c0} \X {CONT_MONITOR})
    variable msg = [type |-> 0]
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        await controllerIsMaster(self[1]);
        await switch2Controller # <<>>;
        msg := Head(switch2Controller);
        waitForLockFree();
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
                ControllerUpdateIR2:
                    waitForLockFree(); 
                    FirstInstall[msg.IR] := 1;
                    IRStatus[msg.IR] := IR_DONE; \* Should be done in one atomic operation
            else assert FALSE;
            end if;
        \*end if; 
    end while
    end process
    \* ==========================    
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-da4478f5aaed7ac3f9e6818834311035
VARIABLES swSeqChangedStatus, switchStatus, installedIRs, failedTimes, 
          NicAsic2OfaBuff, Ofa2NicAsicBuff, Ofa2InstallerBuff, 
          Installer2OfaBuff, TCAM, controlMsgCounter, controller2Switch, 
          switch2Controller, controllerState, switchOrdering, IR2SW, 
          controllerThreadPoolIRQueue, IRStatus, SwSuspensionStatus, 
          lastScheduledThread, SetScheduledIRs, dependencyGraph, 
          workerThreadRanking, workerThreadStatus, switchLock, FirstInstall, 
          pc, stack

(* define statement *)
 max(set) == CHOOSE x \in set: \A y \in set: x \geq y
 min(set) == CHOOSE x \in set: \A y \in set: x \leq y
 rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
 isFinished == \A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE

 RECURSIVE sum(_, _)
 sum(seqS, indexToSum) == IF indexToSum = 0
                          THEN
                             0
                          ELSE
                             IF indexToSum = 1
                             THEN
                                 seqS[1]
                          ELSE
                             seqS[1] + sum(Tail(seqS), indexToSum - 1)

 RECURSIVE Paths(_, _)
 Paths(n, G) ==  IF n = 1
                 THEN
                   G
                 ELSE
                     LET nextVs(p) == { e[2] : e \in {e \in G : e[1] = p[Len(p)]} }
                         nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
                     IN
                     UNION {nextPaths(p) : p \in Paths(n-1, G)} \cup Paths(n-1, G)

RECURSIVE AllPossibleSizes(_, _)
AllPossibleSizes(maxSize, sumUpToNow) == IF sumUpToNow = 0
                                         THEN
                                             {<<0>>}
                                         ELSE
                                             LET Upperbound == min({sumUpToNow, maxSize})
                                             IN
                                             UNION {{<<x>> \o y: y \in AllPossibleSizes(x, sumUpToNow-x)}: x \in 1..Upperbound}

 generateConnectedDAG(S) == {x \in SUBSET (S \X S): /\ ~\E y \in S: <<y, y>> \in x
                                                    /\ ~\E y, z \in S: /\  <<y, z>> \in x
                                                                       /\  <<z, y>> \in x
                                                    /\ \A y \in S: ~\E z \in S: /\ <<z, y>> \in x
                                                                                /\ z >= y
                                                    /\ \/ Cardinality(S) = 1
                                                       \/ \A y \in S: \E z \in S: \/ <<y, z>> \in x
                                                                                  \/ <<z, y>> \in x
                                                    /\ \/ x = {}
                                                       \/ ~\E p1, p2 \in Paths(Cardinality(x), x): /\ p1 # p2
                                                                                                   /\ p1[1] = p2[1]
                                                                                                   /\ p2[Len(p2)] = p1[Len(p1)]
                                                    /\ Cardinality(x) >= Cardinality(S) - 1
                                                    /\  \/ x = {}
                                                        \/ \A p \in Paths(Cardinality(x), x): \/ Len(p) = 1
                                                                                              \/ p[1] # p[Len(p)]}
SetSetUnion(Aset, Bset) == {x \cup y: x \in Aset, y \in Bset}

RECURSIVE GeneralSetSetUnion(_)
GeneralSetSetUnion(A) == IF Cardinality(A) = 1
                         THEN
                             CHOOSE x \in A: TRUE
                         ELSE
                             LET
                                 rndA1 == CHOOSE x \in A:TRUE
                                 rndA2 == CHOOSE x \in A\{rndA1}: TRUE
                             IN
                                 GeneralSetSetUnion({SetSetUnion(rndA1, rndA2)} \cup (A\{rndA1, rndA2}))

PlausibleDependencySet == UNION {GeneralSetSetUnion({generateConnectedDAG(((sum(allSizes, y-1) + 1)..(sum(allSizes, y)))): y \in 1..(Len(allSizes) - 1)}): allSizes \in AllPossibleSizes(MaxNumIRs, MaxNumIRs)}
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
installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerProc"
ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaProcIn"
                         /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaProcOut"
nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchRcvPacket"
                             /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchFromOFAPacket"
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
canWorkerThreadContinue(CID, threadID) == /\ Len(controllerThreadPoolIRQueue[CID]) > 0
                                          /\ workerThreadRanking[threadID] = min({workerThreadRanking[z]: z \in {y \in CONTROLLER_THREAD_POOL: workerThreadStatus[y] = 0}})
whichSwitchModel(swID) == IF MAX_NUM_SW_FAILURE = 0
                            THEN SW_SIMPLE_MODEL
                            ELSE SW_COMPLEX_MODEL

VARIABLES setIRs, nextThread, nextIR, switchIDToReset, setIRsToReset, resetIR, 
          ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, failedSet, 
          statusResolveMsg, recoveredElem, toBeScheduledIRs, nextIRToSent, 
          monitoringEvent, msg

vars == << swSeqChangedStatus, switchStatus, installedIRs, failedTimes, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Ofa2InstallerBuff, 
           Installer2OfaBuff, TCAM, controlMsgCounter, controller2Switch, 
           switch2Controller, controllerState, switchOrdering, IR2SW, 
           controllerThreadPoolIRQueue, IRStatus, SwSuspensionStatus, 
           lastScheduledThread, SetScheduledIRs, dependencyGraph, 
           workerThreadRanking, workerThreadStatus, switchLock, FirstInstall, 
           pc, stack, setIRs, nextThread, nextIR, switchIDToReset, 
           setIRsToReset, resetIR, ingressPkt, ingressIR, egressMsg, ofaInMsg, 
           ofaOutConfirmation, installerInIR, statusMsg, notFailedSet, 
           failedElem, failedSet, statusResolveMsg, recoveredElem, 
           toBeScheduledIRs, nextIRToSent, monitoringEvent, msg >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({c0} \X {CONT_SEQ})) \cup (({c0} \X CONTROLLER_THREAD_POOL)) \cup (({c0} \X {CONT_EVENT})) \cup (({c0} \X {CONT_MONITOR}))

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
        /\ switchOrdering = (CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ IR2SW = (CHOOSE x \in [1..Cardinality(SW) -> SW]: ~\E y, z \in DOMAIN x: /\ y > z
                                                                                     /\ switchOrdering[x[y]] =< switchOrdering[x[z]])
        /\ controllerThreadPoolIRQueue = [y \in {c0, c1} |-> <<>>]
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ lastScheduledThread = 0
        /\ SetScheduledIRs = [x \in {c0, c1} |-> [y \in SW |-> {}]]
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ workerThreadStatus = [x \in CONTROLLER_THREAD_POOL |-> 0]
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        (* Procedure scheduleIRs *)
        /\ setIRs = [ self \in ProcSet |-> {}]
        /\ nextThread = [ self \in ProcSet |-> lastScheduledThread]
        /\ nextIR = [ self \in ProcSet |-> 0]
        (* Procedure resetStateWithRecoveredSW *)
        /\ switchIDToReset = [ self \in ProcSet |-> 0]
        /\ setIRsToReset = [ self \in ProcSet |-> {}]
        /\ resetIR = [ self \in ProcSet |-> 0]
        (* Process swProcess *)
        /\ ingressPkt = [self \in ({SW_SIMPLE_ID} \X SW) |-> [type |-> 0]]
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
        /\ toBeScheduledIRs = [self \in ({c0} \X {CONT_SEQ}) |-> {}]
        (* Process controllerWorkerThreads *)
        /\ nextIRToSent = [self \in ({c0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({c0} \X {CONT_EVENT}) |-> [type |-> 0]]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({c0} \X {CONT_MONITOR}) |-> [type |-> 0]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({NIC_ASIC_IN} \X SW) -> "SwitchRcvPacket"
                                        [] self \in ({NIC_ASIC_OUT} \X SW) -> "SwitchFromOFAPacket"
                                        [] self \in ({OFA_IN} \X SW) -> "SwitchOfaProcIn"
                                        [] self \in ({OFA_OUT} \X SW) -> "SwitchOfaProcOut"
                                        [] self \in ({INSTALLER} \X SW) -> "SwitchInstallerProc"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({c0} \X {CONT_SEQ}) -> "ControllerSeqProc"
                                        [] self \in ({c0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({c0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({c0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ IF setIRs[self] # {} /\ controllerIsMaster(self[1])
                                  THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in setIRs[self]: TRUE]
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ Assert(IRStatus[nextIR'[self]] \in {IR_NONE, IR_DONE}, 
                                                 "Failure of assertion at line 466, column 9.")
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
                                            switchOrdering, IR2SW, 
                                            controllerThreadPoolIRQueue, 
                                            IRStatus, SwSuspensionStatus, 
                                            lastScheduledThread, 
                                            SetScheduledIRs, dependencyGraph, 
                                            workerThreadRanking, 
                                            workerThreadStatus, switchLock, 
                                            FirstInstall, switchIDToReset, 
                                            setIRsToReset, resetIR, ingressPkt, 
                                            ingressIR, egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            toBeScheduledIRs, nextIRToSent, 
                                            monitoringEvent, msg >>

AddToScheduleIRSet(self) == /\ pc[self] = "AddToScheduleIRSet"
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ Assert(nextIR[self] \notin SetScheduledIRs[self[1]][IR2SW[nextIR[self]]], 
                                      "Failure of assertion at line 471, column 13.")
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
                                            switchOrdering, IR2SW, 
                                            controllerThreadPoolIRQueue, 
                                            IRStatus, SwSuspensionStatus, 
                                            lastScheduledThread, 
                                            dependencyGraph, 
                                            workerThreadRanking, 
                                            workerThreadStatus, switchLock, 
                                            FirstInstall, stack, setIRs, 
                                            nextThread, nextIR, 
                                            switchIDToReset, setIRsToReset, 
                                            resetIR, ingressPkt, ingressIR, 
                                            egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            toBeScheduledIRs, nextIRToSent, 
                                            monitoringEvent, msg >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]] = Append(controllerThreadPoolIRQueue[self[1]], nextIR[self])]
                       /\ setIRs' = [setIRs EXCEPT ![self] = setIRs[self]\{nextIR[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                       /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                       installedIRs, failedTimes, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Ofa2InstallerBuff, Installer2OfaBuff, 
                                       TCAM, controlMsgCounter, 
                                       controller2Switch, switch2Controller, 
                                       controllerState, switchOrdering, IR2SW, 
                                       IRStatus, SwSuspensionStatus, 
                                       lastScheduledThread, SetScheduledIRs, 
                                       dependencyGraph, workerThreadRanking, 
                                       workerThreadStatus, switchLock, 
                                       FirstInstall, stack, nextThread, nextIR, 
                                       switchIDToReset, setIRsToReset, resetIR, 
                                       ingressPkt, ingressIR, egressMsg, 
                                       ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, failedSet, statusResolveMsg, 
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
                                           switchOrdering, IR2SW, 
                                           controllerThreadPoolIRQueue, 
                                           IRStatus, SwSuspensionStatus, 
                                           lastScheduledThread, 
                                           SetScheduledIRs, dependencyGraph, 
                                           workerThreadRanking, 
                                           workerThreadStatus, switchLock, 
                                           FirstInstall, stack, setIRs, 
                                           nextThread, nextIR, switchIDToReset, 
                                           resetIR, ingressPkt, ingressIR, 
                                           egressMsg, ofaInMsg, 
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
                                          "Failure of assertion at line 509, column 9.")
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
                                     controllerState, switchOrdering, IR2SW, 
                                     controllerThreadPoolIRQueue, IRStatus, 
                                     SwSuspensionStatus, lastScheduledThread, 
                                     SetScheduledIRs, dependencyGraph, 
                                     workerThreadRanking, workerThreadStatus, 
                                     switchLock, FirstInstall, setIRs, 
                                     nextThread, nextIR, ingressPkt, ingressIR, 
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
                                                            switchOrdering, 
                                                            IR2SW, 
                                                            controllerThreadPoolIRQueue, 
                                                            SwSuspensionStatus, 
                                                            lastScheduledThread, 
                                                            SetScheduledIRs, 
                                                            dependencyGraph, 
                                                            workerThreadRanking, 
                                                            workerThreadStatus, 
                                                            switchLock, 
                                                            FirstInstall, 
                                                            stack, setIRs, 
                                                            nextThread, nextIR, 
                                                            switchIDToReset, 
                                                            setIRsToReset, 
                                                            resetIR, 
                                                            ingressPkt, 
                                                            ingressIR, 
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

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type = INSTALL_FLOW, 
                                       "Failure of assertion at line 530, column 9.")
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ installedIRs' = Append(installedIRs, ingressPkt'[self].IR)
                             /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], ingressPkt'[self].IR)]
                             /\ switch2Controller' = Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                                                from |-> self[2],
                                                                                IR |-> ingressPkt'[self].IR])
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             failedTimes, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, 
                                             controlMsgCounter, 
                                             controllerState, switchOrdering, 
                                             IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             workerThreadRanking, 
                                             workerThreadStatus, switchLock, 
                                             FirstInstall, stack, setIRs, 
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

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(\/ ingressIR'[self].type = RECONCILIATION_REQUEST
                                   \/ ingressIR'[self].type = INSTALL_FLOW, 
                                   "Failure of assertion at line 554, column 9.")
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                         installedIRs, failedTimes, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Ofa2InstallerBuff, Installer2OfaBuff, 
                                         TCAM, controlMsgCounter, 
                                         switch2Controller, controllerState, 
                                         switchOrdering, IR2SW, 
                                         controllerThreadPoolIRQueue, IRStatus, 
                                         SwSuspensionStatus, 
                                         lastScheduledThread, SetScheduledIRs, 
                                         dependencyGraph, workerThreadRanking, 
                                         workerThreadStatus, FirstInstall, 
                                         stack, setIRs, nextThread, nextIR, 
                                         switchIDToReset, setIRsToReset, 
                                         resetIR, ingressPkt, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         toBeScheduledIRs, nextIRToSent, 
                                         monitoringEvent, msg >>

SwitchNicAsicInsertToOfaBuff(self) == /\ pc[self] = "SwitchNicAsicInsertToOfaBuff"
                                      /\ IF swCanReceivePackets(self[2])
                                            THEN /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                 /\ switchLock' = <<OFA_IN, self[2]>>
                                                 /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Append(NicAsic2OfaBuff[self[2]], ingressIR[self])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                                 /\ UNCHANGED ingressIR
                                            ELSE /\ ingressIR' = [ingressIR EXCEPT ![self] = [type |-> 0]]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                                 /\ UNCHANGED << NicAsic2OfaBuff, 
                                                                 switchLock >>
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
                                                      controllerState, 
                                                      switchOrdering, IR2SW, 
                                                      controllerThreadPoolIRQueue, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      workerThreadStatus, 
                                                      FirstInstall, stack, 
                                                      setIRs, nextThread, 
                                                      nextIR, switchIDToReset, 
                                                      setIRsToReset, resetIR, 
                                                      ingressPkt, egressMsg, 
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

swNicAsicProcPacketIn(self) == SwitchRcvPacket(self)
                                  \/ SwitchNicAsicInsertToOfaBuff(self)

SwitchFromOFAPacket(self) == /\ pc[self] = "SwitchFromOFAPacket"
                             /\ swCanReceivePackets(self[2])
                             /\ Len(Ofa2NicAsicBuff[self[2]]) > 0
                             /\ egressMsg' = [egressMsg EXCEPT ![self] = Head(Ofa2NicAsicBuff[self[2]])]
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ switchLock' = self
                             /\ Assert(\/ egressMsg'[self].type = INSTALLED_SUCCESSFULLY
                                       \/ egressMsg'[self].type = RECEIVED_SUCCESSFULLY
                                       \/ egressMsg'[self].type = RECONCILIATION_RESPONSE, 
                                       "Failure of assertion at line 579, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, switchOrdering, 
                                             IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             workerThreadRanking, 
                                             workerThreadStatus, FirstInstall, 
                                             stack, setIRs, nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressPkt, ingressIR, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, toBeScheduledIRs, 
                                             nextIRToSent, monitoringEvent, 
                                             msg >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 357, column 9 of macro called at line 587, column 17.")
                                            /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ switch2Controller' = Append(switch2Controller, egressMsg[self])
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED egressMsg
                                       ELSE /\ egressMsg' = [egressMsg EXCEPT ![self] = [type |-> 0]]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED << switch2Controller, 
                                                            switchLock >>
                                 /\ UNCHANGED << swSeqChangedStatus, 
                                                 switchStatus, installedIRs, 
                                                 failedTimes, NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Ofa2InstallerBuff, 
                                                 Installer2OfaBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 controller2Switch, 
                                                 controllerState, 
                                                 switchOrdering, IR2SW, 
                                                 controllerThreadPoolIRQueue, 
                                                 IRStatus, SwSuspensionStatus, 
                                                 lastScheduledThread, 
                                                 SetScheduledIRs, 
                                                 dependencyGraph, 
                                                 workerThreadRanking, 
                                                 workerThreadStatus, 
                                                 FirstInstall, stack, setIRs, 
                                                 nextThread, nextIR, 
                                                 switchIDToReset, 
                                                 setIRsToReset, resetIR, 
                                                 ingressPkt, ingressIR, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, 
                                                 nextIRToSent, monitoringEvent, 
                                                 msg >>

swNicAsicProcPacketOut(self) == SwitchFromOFAPacket(self)
                                   \/ SwitchNicAsicSendOutMsg(self)

SwitchOfaProcIn(self) == /\ pc[self] = "SwitchOfaProcIn"
                         /\ swOFACanProcessIRs(self[2])
                         /\ Len(NicAsic2OfaBuff[self[2]]) > 0
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = Head(NicAsic2OfaBuff[self[2]])]
                         /\ Assert(ofaInMsg'[self].to = self[2], 
                                   "Failure of assertion at line 608, column 9.")
                         /\ Assert(ofaInMsg'[self].IR  \in 1..MaxNumIRs, 
                                   "Failure of assertion at line 609, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                         installedIRs, failedTimes, 
                                         Ofa2NicAsicBuff, Ofa2InstallerBuff, 
                                         Installer2OfaBuff, TCAM, 
                                         controlMsgCounter, controller2Switch, 
                                         switch2Controller, controllerState, 
                                         switchOrdering, IR2SW, 
                                         controllerThreadPoolIRQueue, IRStatus, 
                                         SwSuspensionStatus, 
                                         lastScheduledThread, SetScheduledIRs, 
                                         dependencyGraph, workerThreadRanking, 
                                         workerThreadStatus, FirstInstall, 
                                         stack, setIRs, nextThread, nextIR, 
                                         switchIDToReset, setIRsToReset, 
                                         resetIR, ingressPkt, ingressIR, 
                                         egressMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         toBeScheduledIRs, nextIRToSent, 
                                         monitoringEvent, msg >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           /\ switchLock' = <<INSTALLER, self[2]>>
                                           /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                                 THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], ofaInMsg[self].IR)]
                                                 ELSE /\ Assert(FALSE, 
                                                                "Failure of assertion at line 621, column 21.")
                                                      /\ UNCHANGED Ofa2InstallerBuff
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED ofaInMsg
                                      ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED << Ofa2InstallerBuff, 
                                                           switchLock >>
                                /\ UNCHANGED << swSeqChangedStatus, 
                                                switchStatus, installedIRs, 
                                                failedTimes, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                controllerState, 
                                                switchOrdering, IR2SW, 
                                                controllerThreadPoolIRQueue, 
                                                IRStatus, SwSuspensionStatus, 
                                                lastScheduledThread, 
                                                SetScheduledIRs, 
                                                dependencyGraph, 
                                                workerThreadRanking, 
                                                workerThreadStatus, 
                                                FirstInstall, stack, setIRs, 
                                                nextThread, nextIR, 
                                                switchIDToReset, setIRsToReset, 
                                                resetIR, ingressPkt, ingressIR, 
                                                egressMsg, ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIRToSent, 
                                                monitoringEvent, msg >>

ofaModuleProcPacketIn(self) == SwitchOfaProcIn(self)
                                  \/ SwitchOfaProcessPacket(self)

SwitchOfaProcOut(self) == /\ pc[self] = "SwitchOfaProcOut"
                          /\ swOFACanProcessIRs(self[2])
                          /\ Installer2OfaBuff[self[2]] # <<>>
                          /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                          /\ switchLock' = self
                          /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = Head(Installer2OfaBuff[self[2]])]
                          /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Tail(Installer2OfaBuff[self[2]])]
                          /\ Assert(ofaOutConfirmation'[self] \in 1..MaxNumIRs, 
                                    "Failure of assertion at line 640, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                          installedIRs, failedTimes, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, controller2Switch, 
                                          switch2Controller, controllerState, 
                                          switchOrdering, IR2SW, 
                                          controllerThreadPoolIRQueue, 
                                          IRStatus, SwSuspensionStatus, 
                                          lastScheduledThread, SetScheduledIRs, 
                                          dependencyGraph, workerThreadRanking, 
                                          workerThreadStatus, FirstInstall, 
                                          stack, setIRs, nextThread, nextIR, 
                                          switchIDToReset, setIRsToReset, 
                                          resetIR, ingressPkt, ingressIR, 
                                          egressMsg, ofaInMsg, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, toBeScheduledIRs, 
                                          nextIRToSent, monitoringEvent, msg >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                 /\ switchLock' = <<NIC_ASIC_OUT, self[2]>>
                                                 /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                                                                                              from |-> self[2],
                                                                                                                                              IR |-> ofaOutConfirmation[self]])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                 /\ UNCHANGED ofaOutConfirmation
                                            ELSE /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = 0]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                 /\ UNCHANGED << Ofa2NicAsicBuff, 
                                                                 switchLock >>
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
                                                      controllerState, 
                                                      switchOrdering, IR2SW, 
                                                      controllerThreadPoolIRQueue, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      workerThreadStatus, 
                                                      FirstInstall, stack, 
                                                      setIRs, nextThread, 
                                                      nextIR, switchIDToReset, 
                                                      setIRsToReset, resetIR, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, 
                                                      nextIRToSent, 
                                                      monitoringEvent, msg >>

ofaModuleProcPacketOut(self) == SwitchOfaProcOut(self)
                                   \/ SendInstallationConfirmation(self)

SwitchInstallerProc(self) == /\ pc[self] = "SwitchInstallerProc"
                             /\ swCanInstallIRs(self[2])
                             /\ Len(Ofa2InstallerBuff[self[2]]) > 0
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ switchLock' = self
                             /\ installerInIR' = [installerInIR EXCEPT ![self] = Head(Ofa2InstallerBuff[self[2]])]
                             /\ Assert(installerInIR'[self] \in 1..MaxNumIRs, 
                                       "Failure of assertion at line 668, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, switchOrdering, 
                                             IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             workerThreadRanking, 
                                             workerThreadStatus, FirstInstall, 
                                             stack, setIRs, nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressPkt, ingressIR, 
                                             egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, toBeScheduledIRs, 
                                             nextIRToSent, monitoringEvent, 
                                             msg >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                               /\ switchLock' = self
                                               /\ installedIRs' = Append(installedIRs, installerInIR[self])
                                               /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], installerInIR[self])]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerSendConfirmation"]
                                               /\ UNCHANGED installerInIR
                                          ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = 0]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                               /\ UNCHANGED << installedIRs, 
                                                               TCAM, 
                                                               switchLock >>
                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                    switchStatus, failedTimes, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Ofa2InstallerBuff, 
                                                    Installer2OfaBuff, 
                                                    controlMsgCounter, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    controllerState, 
                                                    switchOrdering, IR2SW, 
                                                    controllerThreadPoolIRQueue, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    lastScheduledThread, 
                                                    SetScheduledIRs, 
                                                    dependencyGraph, 
                                                    workerThreadRanking, 
                                                    workerThreadStatus, 
                                                    FirstInstall, stack, 
                                                    setIRs, nextThread, nextIR, 
                                                    switchIDToReset, 
                                                    setIRsToReset, resetIR, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, 
                                                    nextIRToSent, 
                                                    monitoringEvent, msg >>

SwitchInstallerSendConfirmation(self) == /\ pc[self] = "SwitchInstallerSendConfirmation"
                                         /\ IF swCanInstallIRs(self[2])
                                               THEN /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                    /\ switchLock' = <<OFA_OUT, self[2]>>
                                                    /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Append(Installer2OfaBuff[self[2]], installerInIR[self])]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED installerInIR
                                               ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = 0]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED << Installer2OfaBuff, 
                                                                    switchLock >>
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
                                                         switchOrdering, IR2SW, 
                                                         controllerThreadPoolIRQueue, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         lastScheduledThread, 
                                                         SetScheduledIRs, 
                                                         dependencyGraph, 
                                                         workerThreadRanking, 
                                                         workerThreadStatus, 
                                                         FirstInstall, stack, 
                                                         setIRs, nextThread, 
                                                         nextIR, 
                                                         switchIDToReset, 
                                                         setIRsToReset, 
                                                         resetIR, ingressPkt, 
                                                         ingressIR, egressMsg, 
                                                         ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, 
                                                         nextIRToSent, 
                                                         monitoringEvent, msg >>

installerModuleProc(self) == SwitchInstallerProc(self)
                                \/ SwitchInstallerInsert2TCAM(self)
                                \/ SwitchInstallerSendConfirmation(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ notFailedSet' = [notFailedSet EXCEPT ![self] = returnSwitchElementsNotFailed(self[2])]
                       /\ notFailedSet'[self] # {}
                       /\ failedTimes[self[2]] < MAX_NUM_SW_FAILURE
                       /\ ~isFinished
                       /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                          \/ switchLock[2] = self[2]
                       /\ \E elem \in notFailedSet'[self]:
                            failedElem' = [failedElem EXCEPT ![self] = elem]
                       /\ IF failedElem'[self] = "cpu"
                             THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                  /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                            "Failure of assertion at line 215, column 9 of macro called at line 711, column 17.")
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
                                  /\ UNCHANGED controller2Switch
                             ELSE /\ IF failedElem'[self] = "ofa"
                                        THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                             /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed, 
                                                       "Failure of assertion at line 260, column 9 of macro called at line 714, column 17.")
                                             /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = Failed]
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
                                             /\ UNCHANGED controller2Switch
                                        ELSE /\ IF failedElem'[self] = "installer"
                                                   THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                                        /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed, 
                                                                  "Failure of assertion at line 298, column 9 of macro called at line 717, column 17.")
                                                        /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                        /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                                                        /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                              THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                             "Failure of assertion at line 302, column 13 of macro called at line 717, column 17.")
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
                                                        /\ UNCHANGED controller2Switch
                                                   ELSE /\ IF failedElem'[self] = "nicAsic"
                                                              THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                                                   /\ Assert(switchStatus[self[2]].nicAsic = NotFailed, 
                                                                             "Failure of assertion at line 176, column 9 of macro called at line 720, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                   /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]]]]
                                                                   /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                                              ELSE /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 721, column 14.")
                                                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                                                   switchStatus, 
                                                                                   failedTimes, 
                                                                                   controlMsgCounter, 
                                                                                   controller2Switch, 
                                                                                   statusMsg >>
                                  /\ UNCHANGED << NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Ofa2InstallerBuff, 
                                                  Installer2OfaBuff >>
                       /\ Assert(\/ switchLock[2] = self[2]
                                 \/ switchLock[2] = NO_LOCK, 
                                 "Failure of assertion at line 357, column 9 of macro called at line 724, column 9.")
                       /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                       /\ UNCHANGED << installedIRs, TCAM, switch2Controller, 
                                       controllerState, switchOrdering, IR2SW, 
                                       controllerThreadPoolIRQueue, IRStatus, 
                                       SwSuspensionStatus, lastScheduledThread, 
                                       SetScheduledIRs, dependencyGraph, 
                                       workerThreadRanking, workerThreadStatus, 
                                       FirstInstall, stack, setIRs, nextThread, 
                                       nextIR, switchIDToReset, setIRsToReset, 
                                       resetIR, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, failedSet, 
                                       statusResolveMsg, recoveredElem, 
                                       toBeScheduledIRs, nextIRToSent, 
                                       monitoringEvent, msg >>

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ failedSet' = [failedSet EXCEPT ![self] = returnSwitchFailedElements(self[2])]
                              /\ Cardinality(failedSet'[self]) > 0
                              /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ ~isFinished
                              /\ \E elem \in failedSet'[self]:
                                   recoveredElem' = [recoveredElem EXCEPT ![self] = elem]
                              /\ IF recoveredElem'[self] = "cpu"
                                    THEN /\ ofaStartingMode(self[2]) /\ installerInStartingMode(self[2])
                                         /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                   "Failure of assertion at line 238, column 9 of macro called at line 743, column 39.")
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
                                         /\ UNCHANGED controller2Switch
                                    ELSE /\ IF recoveredElem'[self] = "nicAsic"
                                               THEN /\ nicAsicStartingMode(self[2])
                                                    /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                              "Failure of assertion at line 192, column 9 of macro called at line 744, column 46.")
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
                                               ELSE /\ IF recoveredElem'[self] = "ofa"
                                                          THEN /\ ofaStartingMode(self[2])
                                                               /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = Failed, 
                                                                         "Failure of assertion at line 279, column 9 of macro called at line 745, column 42.")
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
                                                          ELSE /\ IF recoveredElem'[self] = "installer"
                                                                     THEN /\ installerInStartingMode(self[2])
                                                                          /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = Failed, 
                                                                                    "Failure of assertion at line 317, column 9 of macro called at line 746, column 48.")
                                                                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                               "Failure of assertion at line 320, column 13 of macro called at line 746, column 48.")
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
                                                                     ELSE /\ Assert(FALSE, 
                                                                                    "Failure of assertion at line 747, column 14.")
                                                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                                                          switchStatus, 
                                                                                          controlMsgCounter, 
                                                                                          statusResolveMsg >>
                                                    /\ UNCHANGED controller2Switch
                                         /\ UNCHANGED << NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Ofa2InstallerBuff, 
                                                         Installer2OfaBuff >>
                              /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                              /\ UNCHANGED << installedIRs, failedTimes, TCAM, 
                                              switch2Controller, 
                                              controllerState, switchOrdering, 
                                              IR2SW, 
                                              controllerThreadPoolIRQueue, 
                                              IRStatus, SwSuspensionStatus, 
                                              lastScheduledThread, 
                                              SetScheduledIRs, dependencyGraph, 
                                              workerThreadRanking, 
                                              workerThreadStatus, switchLock, 
                                              FirstInstall, stack, setIRs, 
                                              nextThread, nextIR, 
                                              switchIDToReset, setIRsToReset, 
                                              resetIR, ingressPkt, ingressIR, 
                                              egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              toBeScheduledIRs, nextIRToSent, 
                                              monitoringEvent, msg >>

swResolveFailure(self) == SwitchResolveFailure(self)

ghostProc(self) == /\ pc[self] = "ghostProc"
                   /\ /\ switchLock # <<NO_LOCK, NO_LOCK>>
                      /\ switchLock[2] = self[2]
                   /\ IF switchStatus[switchLock[2]].cpu = Failed /\ switchLock[1] = NIC_ASIC_OUT
                         THEN /\ pc[switchLock] = "SwitchFromOFAPacket"
                         ELSE /\ IF switchLock[1] \in {NIC_ASIC_IN, NIC_ASIC_OUT}
                                    THEN /\ switchStatus[switchLock[2]].nicAsic = Failed
                                         /\ /\ pc[<<NIC_ASIC_IN, self[2]>>] = "SwitchRcvPacket"
                                            /\ pc[<<NIC_ASIC_OUT, self[2]>>] = "SwitchFromOFAPacket"
                                    ELSE /\ IF switchLock[1] \in {OFA_IN, OFA_OUT}
                                               THEN /\ switchStatus[switchLock[2]].ofa = Failed
                                                    /\ /\ pc[<<OFA_IN, self[2]>>] = "SwitchOfaProcIn"
                                                       /\ pc[<<OFA_OUT, self[2]>>] = "SwitchOfaProcOut"
                                               ELSE /\ IF switchLock[1] \in {INSTALLER}
                                                          THEN /\ switchStatus[switchLock[2]].installer = Failed
                                                               /\ pc[<<INSTALLER, self[2]>>] = "SwitchInstallerProc"
                                                          ELSE /\ TRUE
                   /\ Assert(\/ switchLock[2] = self[2]
                             \/ switchLock[2] = NO_LOCK, 
                             "Failure of assertion at line 357, column 9 of macro called at line 777, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                   installedIRs, failedTimes, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Ofa2InstallerBuff, 
                                   Installer2OfaBuff, TCAM, controlMsgCounter, 
                                   controller2Switch, switch2Controller, 
                                   controllerState, switchOrdering, IR2SW, 
                                   controllerThreadPoolIRQueue, IRStatus, 
                                   SwSuspensionStatus, lastScheduledThread, 
                                   SetScheduledIRs, dependencyGraph, 
                                   workerThreadRanking, workerThreadStatus, 
                                   FirstInstall, stack, setIRs, nextThread, 
                                   nextIR, switchIDToReset, setIRsToReset, 
                                   resetIR, ingressPkt, ingressIR, egressMsg, 
                                   ofaInMsg, ofaOutConfirmation, installerInIR, 
                                   statusMsg, notFailedSet, failedElem, 
                                   failedSet, statusResolveMsg, recoveredElem, 
                                   toBeScheduledIRs, nextIRToSent, 
                                   monitoringEvent, msg >>

ghostUnlockProcess(self) == ghostProc(self)

ControllerSeqProc(self) == /\ pc[self] = "ControllerSeqProc"
                           /\ controllerIsMaster(self[1])
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1])]
                           /\ toBeScheduledIRs'[self] # {}
                           /\ /\ setIRs' = [setIRs EXCEPT ![self] = toBeScheduledIRs'[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "scheduleIRs",
                                                                       pc        |->  "ControllerSeqProc",
                                                                       nextThread |->  nextThread[self],
                                                                       nextIR    |->  nextIR[self],
                                                                       setIRs    |->  setIRs[self] ] >>
                                                                   \o stack[self]]
                           /\ nextThread' = [nextThread EXCEPT ![self] = lastScheduledThread]
                           /\ nextIR' = [nextIR EXCEPT ![self] = 0]
                           /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                           /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                           installedIRs, failedTimes, 
                                           NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                           Ofa2InstallerBuff, 
                                           Installer2OfaBuff, TCAM, 
                                           controlMsgCounter, 
                                           controller2Switch, 
                                           switch2Controller, controllerState, 
                                           switchOrdering, IR2SW, 
                                           controllerThreadPoolIRQueue, 
                                           IRStatus, SwSuspensionStatus, 
                                           lastScheduledThread, 
                                           SetScheduledIRs, dependencyGraph, 
                                           workerThreadRanking, 
                                           workerThreadStatus, switchLock, 
                                           FirstInstall, switchIDToReset, 
                                           setIRsToReset, resetIR, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, nextIRToSent, 
                                           monitoringEvent, msg >>

controllerSequencer(self) == ControllerSeqProc(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerIsMaster(self[1])
                          /\ controllerThreadPoolIRQueue[self[1]] # <<>>
                          /\ canWorkerThreadContinue(self[1], self[2])
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ workerThreadStatus' = [workerThreadStatus EXCEPT ![self[2]] = 1]
                          /\ nextIRToSent' = [nextIRToSent EXCEPT ![self] = Head(controllerThreadPoolIRQueue[self[1]])]
                          /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]] = Tail(controllerThreadPoolIRQueue[self[1]])]
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                          /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                          installedIRs, failedTimes, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, Installer2OfaBuff, 
                                          TCAM, controlMsgCounter, 
                                          controller2Switch, switch2Controller, 
                                          controllerState, switchOrdering, 
                                          IR2SW, IRStatus, SwSuspensionStatus, 
                                          lastScheduledThread, SetScheduledIRs, 
                                          dependencyGraph, workerThreadRanking, 
                                          switchLock, FirstInstall, stack, 
                                          setIRs, nextThread, nextIR, 
                                          switchIDToReset, setIRsToReset, 
                                          resetIR, ingressPkt, ingressIR, 
                                          egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, toBeScheduledIRs, 
                                          monitoringEvent, msg >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                controllerState, 
                                                switchOrdering, IR2SW, 
                                                controllerThreadPoolIRQueue, 
                                                SwSuspensionStatus, 
                                                lastScheduledThread, 
                                                SetScheduledIRs, 
                                                dependencyGraph, 
                                                workerThreadRanking, 
                                                workerThreadStatus, switchLock, 
                                                FirstInstall, stack, setIRs, 
                                                nextThread, nextIR, 
                                                switchIDToReset, setIRsToReset, 
                                                resetIR, ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIRToSent, 
                                                monitoringEvent, msg >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                   controllerState, 
                                                   switchOrdering, IR2SW, 
                                                   controllerThreadPoolIRQueue, 
                                                   IRStatus, 
                                                   SwSuspensionStatus, 
                                                   lastScheduledThread, 
                                                   SetScheduledIRs, 
                                                   dependencyGraph, 
                                                   workerThreadRanking, 
                                                   workerThreadStatus, 
                                                   switchLock, FirstInstall, 
                                                   stack, setIRs, nextThread, 
                                                   nextIR, switchIDToReset, 
                                                   setIRsToReset, resetIR, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, 
                                                   nextIRToSent, 
                                                   monitoringEvent, msg >>

WaitForIRToHaveCorrectStatus(self) == /\ pc[self] = "WaitForIRToHaveCorrectStatus"
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                      controllerState, 
                                                      switchOrdering, IR2SW, 
                                                      controllerThreadPoolIRQueue, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      workerThreadStatus, 
                                                      switchLock, FirstInstall, 
                                                      stack, setIRs, 
                                                      nextThread, nextIR, 
                                                      switchIDToReset, 
                                                      setIRsToReset, resetIR, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
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
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                            switchOrdering, IR2SW, 
                                            controllerThreadPoolIRQueue, 
                                            IRStatus, SwSuspensionStatus, 
                                            lastScheduledThread, 
                                            SetScheduledIRs, dependencyGraph, 
                                            workerThreadRanking, 
                                            workerThreadStatus, switchLock, 
                                            FirstInstall, stack, setIRs, 
                                            nextThread, nextIR, 
                                            switchIDToReset, setIRsToReset, 
                                            resetIR, ingressPkt, ingressIR, 
                                            egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            toBeScheduledIRs, nextIRToSent, 
                                            monitoringEvent, msg >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ Assert(nextIRToSent[self] \in SetScheduledIRs[self[1]][IR2SW[nextIRToSent[self]]], 
                                            "Failure of assertion at line 832, column 13.")
                                  /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![self[1]][IR2SW[nextIRToSent[self]]] = SetScheduledIRs[self[1]][IR2SW[nextIRToSent[self]]]\{nextIRToSent[self]}]
                                  /\ workerThreadStatus' = [workerThreadStatus EXCEPT ![self[2]] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                  /\ UNCHANGED << swSeqChangedStatus, 
                                                  switchStatus, installedIRs, 
                                                  failedTimes, NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Ofa2InstallerBuff, 
                                                  Installer2OfaBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  controllerState, 
                                                  switchOrdering, IR2SW, 
                                                  controllerThreadPoolIRQueue, 
                                                  IRStatus, SwSuspensionStatus, 
                                                  lastScheduledThread, 
                                                  dependencyGraph, 
                                                  workerThreadRanking, 
                                                  switchLock, FirstInstall, 
                                                  stack, setIRs, nextThread, 
                                                  nextIR, switchIDToReset, 
                                                  setIRsToReset, resetIR, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, 
                                                  toBeScheduledIRs, 
                                                  nextIRToSent, 
                                                  monitoringEvent, msg >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ WaitForIRToHaveCorrectStatus(self)
                                    \/ ReScheduleifIRNone(self)
                                    \/ RemoveFromScheduledIRSet(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerIsMaster(self[1])
                                    /\ swSeqChangedStatus # <<>>
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                    /\ UNCHANGED << switchStatus, installedIRs, 
                                                    failedTimes, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Ofa2InstallerBuff, 
                                                    Installer2OfaBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    controllerState, 
                                                    switchOrdering, IR2SW, 
                                                    controllerThreadPoolIRQueue, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    lastScheduledThread, 
                                                    SetScheduledIRs, 
                                                    dependencyGraph, 
                                                    workerThreadRanking, 
                                                    workerThreadStatus, 
                                                    switchLock, FirstInstall, 
                                                    stack, setIRs, nextThread, 
                                                    nextIR, switchIDToReset, 
                                                    setIRsToReset, resetIR, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, 
                                                    nextIRToSent, msg >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                             /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, switchOrdering, 
                                             IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             IRStatus, lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             workerThreadRanking, 
                                             workerThreadStatus, switchLock, 
                                             FirstInstall, stack, setIRs, 
                                             nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressPkt, ingressIR, 
                                             egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIRToSent, 
                                             monitoringEvent, msg >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                   controllerState, 
                                                   switchOrdering, IR2SW, 
                                                   controllerThreadPoolIRQueue, 
                                                   IRStatus, 
                                                   lastScheduledThread, 
                                                   SetScheduledIRs, 
                                                   dependencyGraph, 
                                                   workerThreadRanking, 
                                                   workerThreadStatus, 
                                                   switchLock, FirstInstall, 
                                                   stack, setIRs, nextThread, 
                                                   nextIR, switchIDToReset, 
                                                   setIRsToReset, resetIR, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, 
                                                   nextIRToSent, 
                                                   monitoringEvent, msg >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "resetStateWithRecoveredSW",
                                                                                                 pc        |->  "ControllerEventHandlerProc",
                                                                                                 setIRsToReset |->  setIRsToReset[self],
                                                                                                 resetIR   |->  resetIR[self],
                                                                                                 switchIDToReset |->  switchIDToReset[self] ] >>
                                                                                             \o stack[self]]
                                                        /\ switchIDToReset' = [switchIDToReset EXCEPT ![self] = monitoringEvent[self].swID]
                                                     /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = {}]
                                                     /\ resetIR' = [resetIR EXCEPT ![self] = 0]
                                                     /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
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
                                                          switchOrdering, 
                                                          IR2SW, 
                                                          controllerThreadPoolIRQueue, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          lastScheduledThread, 
                                                          SetScheduledIRs, 
                                                          dependencyGraph, 
                                                          workerThreadRanking, 
                                                          workerThreadStatus, 
                                                          switchLock, 
                                                          FirstInstall, setIRs, 
                                                          nextThread, nextIR, 
                                                          ingressPkt, 
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
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ controllerIsMaster(self[1])
                                       /\ switch2Controller # <<>>
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ switch2Controller' = Tail(switch2Controller)
                                       /\ Assert(msg'[self].from = IR2SW[msg'[self].IR], 
                                                 "Failure of assertion at line 881, column 9.")
                                       /\ Assert(msg'[self].type \in {RECONCILIATION_RESPONSE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                 "Failure of assertion at line 882, column 9.")
                                       /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIR2"]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 905, column 18.")
                                                  /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
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
                                                       controllerState, 
                                                       switchOrdering, IR2SW, 
                                                       controllerThreadPoolIRQueue, 
                                                       IRStatus, 
                                                       SwSuspensionStatus, 
                                                       lastScheduledThread, 
                                                       SetScheduledIRs, 
                                                       dependencyGraph, 
                                                       workerThreadRanking, 
                                                       workerThreadStatus, 
                                                       switchLock, 
                                                       FirstInstall, stack, 
                                                       setIRs, nextThread, 
                                                       nextIR, switchIDToReset, 
                                                       setIRsToReset, resetIR, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       toBeScheduledIRs, 
                                                       nextIRToSent, 
                                                       monitoringEvent >>

ControllerUpdateIR2(self) == /\ pc[self] = "ControllerUpdateIR2"
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ FirstInstall' = [FirstInstall EXCEPT ![msg[self].IR] = 1]
                             /\ IRStatus' = [IRStatus EXCEPT ![msg[self].IR] = IR_DONE]
                             /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                             /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                             installedIRs, failedTimes, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Ofa2InstallerBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controller2Switch, 
                                             switch2Controller, 
                                             controllerState, switchOrdering, 
                                             IR2SW, 
                                             controllerThreadPoolIRQueue, 
                                             SwSuspensionStatus, 
                                             lastScheduledThread, 
                                             SetScheduledIRs, dependencyGraph, 
                                             workerThreadRanking, 
                                             workerThreadStatus, switchLock, 
                                             stack, setIRs, nextThread, nextIR, 
                                             switchIDToReset, setIRsToReset, 
                                             resetIR, ingressPkt, ingressIR, 
                                             egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIRToSent, 
                                             monitoringEvent, msg >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ ControllerUpdateIR2(self)

Next == (\E self \in ProcSet:  \/ scheduleIRs(self)
                               \/ resetStateWithRecoveredSW(self))
           \/ (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
           \/ (\E self \in ({NIC_ASIC_IN} \X SW): swNicAsicProcPacketIn(self))
           \/ (\E self \in ({NIC_ASIC_OUT} \X SW): swNicAsicProcPacketOut(self))
           \/ (\E self \in ({OFA_IN} \X SW): ofaModuleProcPacketIn(self))
           \/ (\E self \in ({OFA_OUT} \X SW): ofaModuleProcPacketOut(self))
           \/ (\E self \in ({INSTALLER} \X SW): installerModuleProc(self))
           \/ (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
           \/ (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
           \/ (\E self \in ({GHOST_UNLOCK_PROC} \X SW): ghostUnlockProcess(self))
           \/ (\E self \in ({c0} \X {CONT_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({c0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({c0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({c0} \X {CONT_MONITOR}): controllerMonitoringServer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(swProcess(self))
        /\ \A self \in ({NIC_ASIC_IN} \X SW) : WF_vars(swNicAsicProcPacketIn(self))
        /\ \A self \in ({NIC_ASIC_OUT} \X SW) : WF_vars(swNicAsicProcPacketOut(self))
        /\ \A self \in ({OFA_IN} \X SW) : WF_vars(ofaModuleProcPacketIn(self))
        /\ \A self \in ({OFA_OUT} \X SW) : WF_vars(ofaModuleProcPacketOut(self))
        /\ \A self \in ({INSTALLER} \X SW) : WF_vars(installerModuleProc(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(swResolveFailure(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_vars(ghostUnlockProcess(self))
        /\ \A self \in ({c0} \X {CONT_SEQ}) : WF_vars(controllerSequencer(self)) /\ WF_vars(scheduleIRs(self))
        /\ \A self \in ({c0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({c0} \X {CONT_EVENT}) : /\ WF_vars(controllerEventHandler(self))
                                                /\ WF_vars(resetStateWithRecoveredSW(self))
        /\ \A self \in ({c0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-1127f38265f9486bb7d8f26f54b8d128

\* Liveness Properties
AllInstalled == (\A x \in 1..MaxNumIRs: \E y \in DOMAIN installedIRs: installedIRs[y] = x)
AllDoneStatusController == (\A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE)
InstallationLivenessProp == <>[] (AllInstalled /\ AllDoneStatusController)
\* Safety Properties
RedundantInstallation == \A x \in 1..MaxNumIRs: \/ IRStatus[x] = IR_DONE
                                                \/ FirstInstall[x] = 0
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)
                                                         /\ <<y, x>> \notin dependencyGraph
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<x, y>> \notin dependencyGraph

=============================================================================
\* Modification History
\* Last modified Sat Sep 19 21:32:11 UTC 2020 by root
\* Created Sat Aug 08 17:44:35 UTC 2020 by root


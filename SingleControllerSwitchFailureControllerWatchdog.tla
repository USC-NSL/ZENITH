---------- MODULE SingleControllerSwitchFailureControllerWatchdog ----------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS SW, c0, c1, CONTROLLER_THREAD_POOL, MaxNumIRs, WATCH_DOG,
          NotFailed, Failed, MAX_NUM_SW_FAILURE, IR_NONE, IR_SENT, IR_PENDING, IR_DONE, SW_SUSPEND, SW_RUN,
          RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, SW_UP, SW_DOWN, KEEP_ALIVE, IR_RECONCILE,
          NIC_ASIC_IN, NIC_ASIC_OUT, OFA_IN, OFA_OUT, INSTALLER, SW_FAILURE_PROC, SW_RESOLVE_PROC,
          CONT_SEQ, CONT_MONITOR, CONT_EVENT, NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN, MAX_NUM_CONTROLLER_FAILURE,
          INSTALLER_UP, RECONCILIATION_REQUEST, RECONCILIATION_RESPONSE, INSTALL_FLOW, STATUS_NONE,
          NO_STATUS, STATUS_START_SCHEDULING, STATUS_LOCKING, STATUS_SENT_DONE,
          START_RESET_IR, NO_TAG, SW_SIMPLE_ID, SW_SIMPLE_MODEL, SW_COMPLEX_MODEL, NO_LOCK, 
          GHOST_UNLOCK_PROC, IR_UNLOCK

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
              IR2SW = CHOOSE x \in [1..MaxNumIRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z 
                                                                                /\ switchOrdering[x[y]] =< switchOrdering[x[z]],
              controllerThreadPoolIRQueue = [y \in {c0, c1} |-> <<>>], 
              IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
              SwSuspensionStatus = [x \in SW |-> SW_RUN],
              lastScheduledThread = 0,
              SetScheduledIRs = [x \in {c0, c1} |-> [y \in SW |-> {}]],
              controllerInternalFailedTimes = [x \in {c0, c1} |-> 0],
              ContProcSet = (({c0, c1} \X {CONT_SEQ})) \cup (({c0, c1} \X CONTROLLER_THREAD_POOL)) \cup (({c0, c1} \X {CONT_EVENT})) \cup (({c0, c1} \X {CONT_MONITOR})),
              SwProcSet = (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)),
              controllerStatus = [x \in ContProcSet |-> NotFailed],
              idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK],
              \************* Controller Permanent DB ******************
              controllerDB = [x \in ContProcSet |-> [type |-> NO_STATUS]],
              \**************** Dependency Graph Definition **************
\*              dependencyGraph \in PlausibleDependencySet,
              dependencyGraph \in generateConnectedDAG(1..MaxNumIRs),
              \**************** Ghost Vars ****************************
              workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
              switchLock = <<NO_LOCK, NO_LOCK>>,
              controllerLock = <<NO_LOCK, NO_LOCK>>, 
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
        returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                                   /\ controllerStatus[x] = Failed}
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
                                                                  /\ x \notin SetScheduledIRs[CID][IR2SW[x]]
                                                                  /\ idThreadWorkingOnIR[x] = IR_UNLOCK}
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
                                    
        moduleIsUp(threadID) == controllerStatus[threadID] = NotFailed 
        NoEntryTaggedWith(threadID, CID) == ~\E x \in rangeSeq(controllerThreadPoolIRQueue[CID]): x.tag = threadID 
        FirstUntaggedEntry(threadID, CID, num) == ~\E x \in DOMAIN controllerThreadPoolIRQueue[CID]: /\ controllerThreadPoolIRQueue[CID][x].tag = NO_TAG
                                                                                                     /\ x < num
        getFirstIRIndexToRead(threadID, CID) == CHOOSE x \in DOMAIN controllerThreadPoolIRQueue[CID]: \/ controllerThreadPoolIRQueue[CID][x].tag = threadID
                                                                                                      \/ /\ NoEntryTaggedWith(threadID, CID)
                                                                                                         /\ FirstUntaggedEntry(threadID, CID, x)
                                                                                                         /\ controllerThreadPoolIRQueue[CID][x].tag = NO_TAG
        getFirstIndexWith(RID, CID, threadID) == CHOOSE x \in DOMAIN controllerThreadPoolIRQueue[CID]: /\ controllerThreadPoolIRQueue[CID][x].tag = threadID
                                                                                                       /\ controllerThreadPoolIRQueue[CID][x].IR = RID                                    
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
        setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>, CID)
                                                              /\ controllerStatus[<<CID, y>>] = NotFailed}
        
        canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(controllerThreadPoolIRQueue[CID]): x.tag = threadID
                                                  \/ /\ \E x \in rangeSeq(controllerThreadPoolIRQueue[CID]): x.tag = NO_TAG 
                                                     /\ NoEntryTaggedWith(threadID, CID) 
                                                     /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
        setThreadsAttemptingForLock(CID, nIR) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(controllerThreadPoolIRQueue[CID]): y.IR = nIR
                                                                                             /\ pc[<<CID, x>>] = "ControllerThreadLockTheIRUsingSemaphore"}
        threadWithLowerIDGetsTheLock(CID, threadID, nIR) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setThreadsAttemptingForLock(CID, nIR)})                                             
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
        await controllerLock = <<NO_LOCK, NO_LOCK>>; 
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
        await controllerLock = <<NO_LOCK, NO_LOCK>>;
        await switchLock = <<NO_LOCK, NO_LOCK>>;
    end macro
    \* =================================
    
    \* ========= controller release Lock ==========
    macro controllerReleaseLock(prevLockHolder)
    begin
        await \/ controllerLock = prevLockHolder
              \/ controllerLock = <<NO_LOCK, NO_LOCK>>;
        await switchLock = <<NO_LOCK, NO_LOCK>>;
        controllerLock := <<NO_LOCK, NO_LOCK>>;
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
    
    macro controllerModuleFailOrNot()
    begin
        if (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE) then           
            either
                controllerStatus[self] := Failed;
                controllerInternalFailedTimes[self[1]] := controllerInternalFailedTimes[self[1]] + 1;
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
    end macro;
    
    macro modifiedEnqueue()
    begin
        controllerThreadPoolIRQueue[self[1]] := Append(controllerThreadPoolIRQueue[self[1]], [IR |-> nextIR, tag |-> NO_TAG]);
    end macro;
    
    macro modifiedRead()
    begin
        rowIndex := getFirstIRIndexToRead(self, self[1]);
        nextIRToSent := controllerThreadPoolIRQueue[self[1]][rowIndex].IR;
        controllerThreadPoolIRQueue[self[1]][rowIndex].tag := self;
    end macro;
    
    macro modifiedRemove()
    begin
        rowRemove := getFirstIndexWith(nextIRToSent, self[1], self);
        controllerThreadPoolIRQueue[self[1]] := removeFromSeq(controllerThreadPoolIRQueue[self[1]], rowRemove);
    end macro;
    
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
    
   (* procedure scheduleIRs(setIRs = {})
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
   *) 
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
    
    (* procedure resetStateWithRecoveredSW(switchIDToReset = 0)
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
    *)
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
        await ~isFinished;
        await failedTimes[self[2]] < MAX_NUM_SW_FAILURE;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
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
        await ~isFinished;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ switchLock = <<NO_LOCK, NO_LOCK>>;
        with elem \in failedSet do
            recoveredElem := elem;
        end with;
        
        if recoveredElem = "cpu" then resolveCpuFailure();
        elsif recoveredElem = "nicAsic" then resolveNicAsicFailure();
        elsif recoveredElem = "ofa" then resolveOfaFailure();
        elsif recoveredElem = "installer" then resolveInstallerFailure();
        else assert FALSE;
        end if;
        
        \*releaseLock(self);
    end while
    end process
    \* =================================
    
    \* ======== Ghost UNLOCK ===========
    fair process ghostUnlockProcess \in ({GHOST_UNLOCK_PROC} \X SW)
    begin
    ghostProc:
    while TRUE do
        await /\ switchLock # <<NO_LOCK, NO_LOCK>>
              /\ switchLock[2] = self[2]
              /\ controllerLock = <<NO_LOCK, NO_LOCK>>;
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
        releaseLock(switchLock);
    end while
    end process
    \* =================================
    
    \* ------------------------------------------------------------------
    \* -                   Controller (Modules)                         -
    \* ------------------------------------------------------------------
   
    \* ======= Sequencer ========
    fair process controllerSequencer \in ({c0} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}, nextIR = 0;
    begin
    ControllerSeqProc:
    while TRUE do
        \*await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        waitForLockFree();
        toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1]);
        await toBeScheduledIRs # {};
        SchedulerMechanism:
        while TRUE do \* while toBeScheduledIRs # {} do
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
            else
                goto ControllerSeqStateReconciliation;
            end if;
            SeqUpdateDBState1:
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then 
                    controllerDB[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
                else
                    goto ControllerSeqStateReconciliation;
                end if;
            AddToScheduleIRSet:
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then 
                    \*assert nextIR \notin SetScheduledIRs[self[1]][IR2SW[nextIR]];
                    SetScheduledIRs[self[1]][IR2SW[nextIR]] := SetScheduledIRs[self[1]][IR2SW[nextIR]] \cup {nextIR};
                else
                    goto ControllerSeqStateReconciliation;
                end if;
            ScheduleTheIR:
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then 
                    modifiedEnqueue();
                    toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                else
                    goto ControllerSeqStateReconciliation;
                end if;
            SeqClearDBState:
                waitForLockFree(); 
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then 
                    controllerDB[self] := [type |-> NO_STATUS];                    
                    if toBeScheduledIRs = {} then \* where while end *\
                        goto ControllerSeqProc;
                    end if;                    
                else       
                    goto ControllerSeqStateReconciliation;
                end if;
        end while;                                                
    end while;
    
    ControllerSeqStateReconciliation:
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        controllerReleaseLock(self);
        if(controllerDB[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[self[1]][IR2SW[controllerDB[self].next]] := SetScheduledIRs[self[1]][IR2SW[controllerDB[self].next]]\{controllerDB[self].next};
        end if;
        goto ControllerSeqProc;
    end process
    \* ==========================
    
    \* ====== Thread Pool ======= 
    fair process controllerWorkerThreads \in ({c0} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = 0, rowIndex = -1, rowRemove = -1; 
    begin
    ControllerThread:
    while TRUE do
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await controllerThreadPoolIRQueue[self[1]] # <<>>;
        await canWorkerThreadContinue(self[1], self);
        waitForLockFree();
        modifiedRead();
        ControllerThreadSaveToDB1:
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then 
                    controllerDB[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent];
                else
                    goto ControllerThreadStateReconciliation;
                end if;
        ControllerThreadLockTheIRUsingSemaphore:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                if idThreadWorkingOnIR[nextIRToSent] = IR_UNLOCK then
                    await threadWithLowerIDGetsTheLock(self[1], self, nextIRToSent); \* For Reducing Space
                    idThreadWorkingOnIR[nextIRToSent] := self[2]
                else
                    ControllerThreadRemoveQueue1: 
                        waitForLockFree();
                        modifiedRemove();
                        goto ControllerThread;    
                end if;
            else
                goto ControllerThreadStateReconciliation;
            end if;
        ControllerThreadSendIR:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                if ~isSwitchSuspended(IR2SW[nextIRToSent]) /\ IRStatus[nextIRToSent] = IR_NONE then 
                    IRStatus[nextIRToSent] := IR_SENT;
                    ControllerThreadForwardIR: 
                        waitForLockFree();
                        controllerModuleFailOrNot();
                        if (controllerStatus[self] = NotFailed) then
                           controllerSendIR(nextIRToSent); 
                        else
                           goto ControllerThreadStateReconciliation;
                        end if;
                        
                    ControllerThreadSaveToDB2:
                        waitForLockFree();
                        controllerModuleFailOrNot();
                        if (controllerStatus[self] = NotFailed) then 
                            controllerDB[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRToSent];
                        else
                            goto ControllerThreadStateReconciliation;
                        end if;
                end if;
            else
                goto ControllerThreadStateReconciliation;
            end if;
        
        WaitForIRToHaveCorrectStatus:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                await ~isSwitchSuspended(IR2SW[nextIRToSent]);
            else
                goto ControllerThreadStateReconciliation;
            end if;
        ReScheduleifIRNone:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                if IRStatus[nextIRToSent] = IR_NONE then
                    controllerDB[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent]; 
                    goto ControllerThreadSendIR;
                end if;
            else
                goto ControllerThreadStateReconciliation;
            end if;
        ControllerThreadUnlockSemaphore:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                if idThreadWorkingOnIR[nextIRToSent] = self[2] then
                    idThreadWorkingOnIR[nextIRToSent] := IR_UNLOCK;
                end if;
            else
                goto ControllerThreadStateReconciliation;
            end if;
        RemoveFromScheduledIRSet:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                \* assert nextIRToSent \in SetScheduledIRs[self[1]][IR2SW[nextIRToSent]];
                SetScheduledIRs[self[1]][IR2SW[nextIRToSent]] := SetScheduledIRs[self[1]][IR2SW[nextIRToSent]]\{nextIRToSent};
            else
                goto ControllerThreadStateReconciliation;
            end if;
        ControllerThreadClearDB:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then 
                controllerDB[self] := [type |-> NO_STATUS];
            else
                goto ControllerThreadStateReconciliation;
            end if;
        ControllerThreadRemoveQueue2: 
            waitForLockFree();
            modifiedRemove();
    end while;
    ControllerThreadStateReconciliation:
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await controllerThreadPoolIRQueue[self[1]] # <<>>;
        await canWorkerThreadContinue(self[1], self);
        controllerReleaseLock(self);
        if (controllerDB[self].type = STATUS_LOCKING) then
            if (IRStatus[controllerDB[self].next] = IR_SENT) then
                    IRStatus[controllerDB[self].next] := IR_NONE;
            end if;                 
            if (idThreadWorkingOnIR[controllerDB[self].next] = self[2]) then
                idThreadWorkingOnIR[controllerDB[self].next] := IR_UNLOCK;
            end if;        
        elsif (controllerDB[self].type = STATUS_SENT_DONE) then
            SetScheduledIRs[self[1]][IR2SW[controllerDB[self].next]] := SetScheduledIRs[self[1]][IR2SW[controllerDB[self].next]] \cup {controllerDB[self].next};          
            if (idThreadWorkingOnIR[controllerDB[self].next] = self[2]) then
                idThreadWorkingOnIR[controllerDB[self].next] := IR_UNLOCK;
            end if;
        end if;
        goto ControllerThread;
    end process
    \* ==========================
    
    \* ===== Event Handler ======
    fair process controllerEventHandler \in ({c0} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, resetIR = 0;
    begin
    ControllerEventHandlerProc:
    while TRUE do 
         await controllerIsMaster(self[1]);
         await moduleIsUp(self);   
         await swSeqChangedStatus # <<>>;
         waitForLockFree();
         monitoringEvent := Head(swSeqChangedStatus);
         if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
            ControllerSuspendSW: 
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then
                    SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;        
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            \*call suspendInSchedulingIRs(monitoringEvent.swID);
            
            ControllerEventHandlerSaveToDB1:
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then
                    controllerDB[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
            ControllerFreeSuspendedSW: 
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then
                    SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
            ControllerCheckIfThisIsLastEvent:
                waitForLockFree();
                controllerModuleFailOrNot();
                if (controllerStatus[self] = NotFailed) then
                    if ~existsMonitoringEventHigherNum(monitoringEvent) then
                        \* call reconcileStateWithRecoveredSW(monitoringEvent.swID);
                        getIRsToBeChecked:
                            waitForLockFree();
                            controllerModuleFailOrNot();
                            if (controllerStatus[self] = NotFailed) then
                                setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                                if (setIRsToReset = {}) then \* Do not do the operations in ResetAllIRs label if setIRsToReset is Empty *\
                                    goto ControllerEventHandlerClearDB;
                                end if;
                            else
                                goto ControllerEventHandlerStateReconciliation;
                            end if;
                        ResetAllIRs:
                            while TRUE do \* Initially: while setIRsToReset # {} do
                                waitForLockFree();
                                controllerModuleFailOrNot();
                                if (controllerStatus[self] = NotFailed) then
                                    resetIR := CHOOSE x \in setIRsToReset: TRUE;
                                    setIRsToReset := setIRsToReset \ {resetIR};
                                    \* assert IRStatus[resetIR] \notin {IR_NONE};
                                else
                                    goto ControllerEventHandlerStateReconciliation;
                                end if;
                                ControllerResetIRStatAfterRecovery: 
                                    waitForLockFree();
                                    controllerModuleFailOrNot();
                                    if (controllerStatus[self] = NotFailed) then
                                        if IRStatus[resetIR] # IR_DONE then
                                            IRStatus[resetIR] := IR_NONE;
                                        end if;
                                        if setIRsToReset = {} then \* End of while *\
                                            goto ControllerEventHandlerClearDB;
                                        end if;
                                    else
                                        goto ControllerEventHandlerStateReconciliation;
                                    end if;
                            end while;
                         ControllerEventHandlerClearDB:
                            waitForLockFree();
                            controllerModuleFailOrNot();
                            if (controllerStatus[self] = NotFailed) then
                                controllerDB[self] := [type |-> NO_STATUS]; 
                            else
                                goto ControllerEventHandlerStateReconciliation;
                            end if;
                    end if;
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
         end if;
         ControllerEvenHanlderRemoveEventFromQueue:
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                swSeqChangedStatus := Tail(swSeqChangedStatus);
            else
                goto ControllerEventHandlerStateReconciliation;
            end if;
    end while;
    ControllerEventHandlerStateReconciliation:    
         await controllerIsMaster(self[1]);
         await moduleIsUp(self);   
         await swSeqChangedStatus # <<>>;
         controllerReleaseLock(self);
         if (controllerDB[self].type = START_RESET_IR) then
            SwSuspensionStatus[controllerDB[self].sw] := SW_SUSPEND;
         end if;
        goto ControllerEventHandlerProc;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    fair process controllerMonitoringServer \in ({c0} \X {CONT_MONITOR})
    variable msg = [type |-> 0]
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await switch2Controller # <<>>;
        controllerReleaseLock(self);
        msg := Head(switch2Controller);
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
                    controllerModuleFailOrNot();
                    if (controllerStatus[self] = NotFailed) then
                        FirstInstall[msg.IR] := 1;
                        IRStatus[msg.IR] := IR_DONE; \* Should be done in one atomic operation
                    else
                        goto ControllerMonitorCheckIfMastr;
                    end if;
            else assert FALSE;
            end if;
        
        \*end if;
        MonitoringServerRemoveFromQueue: 
            waitForLockFree();
            controllerModuleFailOrNot();
            if (controllerStatus[self] = NotFailed) then
                switch2Controller := Tail(switch2Controller);
            else
                goto ControllerMonitorCheckIfMastr;
            end if; 
    end while
    end process
    
    fair process watchDog \in ({c0} \X {WATCH_DOG})
    variable controllerFailedModules = {};
    begin
    ControllerWatchDogProc:
    while TRUE do
        waitForLockFree();
        controllerFailedModules := returnControllerFailedModules(self[1]);
        await Cardinality(controllerFailedModules) > 0;
        with module \in controllerFailedModules do
            assert controllerStatus[module] = Failed;
            controllerLock := module;
            controllerStatus[module] := NotFailed;   
        end with;
        
    end while; 
    end process
    \* ==========================
       
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-85f5dd1791b28b973cf1c3f61daab23d
VARIABLES swSeqChangedStatus, switchStatus, installedIRs, failedTimes, 
          NicAsic2OfaBuff, Ofa2NicAsicBuff, Ofa2InstallerBuff, 
          Installer2OfaBuff, TCAM, controlMsgCounter, controller2Switch, 
          switch2Controller, controllerState, switchOrdering, IR2SW, 
          controllerThreadPoolIRQueue, IRStatus, SwSuspensionStatus, 
          lastScheduledThread, SetScheduledIRs, controllerInternalFailedTimes, 
          ContProcSet, SwProcSet, controllerStatus, idThreadWorkingOnIR, 
          controllerDB, dependencyGraph, workerThreadRanking, switchLock, 
          controllerLock, FirstInstall, pc

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
returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                           /\ controllerStatus[x] = Failed}
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
                                                          /\ x \notin SetScheduledIRs[CID][IR2SW[x]]
                                                          /\ idThreadWorkingOnIR[x] = IR_UNLOCK}
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

moduleIsUp(threadID) == controllerStatus[threadID] = NotFailed
NoEntryTaggedWith(threadID, CID) == ~\E x \in rangeSeq(controllerThreadPoolIRQueue[CID]): x.tag = threadID
FirstUntaggedEntry(threadID, CID, num) == ~\E x \in DOMAIN controllerThreadPoolIRQueue[CID]: /\ controllerThreadPoolIRQueue[CID][x].tag = NO_TAG
                                                                                             /\ x < num
getFirstIRIndexToRead(threadID, CID) == CHOOSE x \in DOMAIN controllerThreadPoolIRQueue[CID]: \/ controllerThreadPoolIRQueue[CID][x].tag = threadID
                                                                                              \/ /\ NoEntryTaggedWith(threadID, CID)
                                                                                                 /\ FirstUntaggedEntry(threadID, CID, x)
                                                                                                 /\ controllerThreadPoolIRQueue[CID][x].tag = NO_TAG
getFirstIndexWith(RID, CID, threadID) == CHOOSE x \in DOMAIN controllerThreadPoolIRQueue[CID]: /\ controllerThreadPoolIRQueue[CID][x].tag = threadID
                                                                                               /\ controllerThreadPoolIRQueue[CID][x].IR = RID
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]
setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>, CID)
                                                      /\ controllerStatus[<<CID, y>>] = NotFailed}

canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(controllerThreadPoolIRQueue[CID]): x.tag = threadID
                                          \/ /\ \E x \in rangeSeq(controllerThreadPoolIRQueue[CID]): x.tag = NO_TAG
                                             /\ NoEntryTaggedWith(threadID, CID)
                                             /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
setThreadsAttemptingForLock(CID, nIR) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(controllerThreadPoolIRQueue[CID]): y.IR = nIR
                                                                                     /\ pc[<<CID, x>>] = "ControllerThreadLockTheIRUsingSemaphore"}
threadWithLowerIDGetsTheLock(CID, threadID, nIR) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setThreadsAttemptingForLock(CID, nIR)})
whichSwitchModel(swID) == IF MAX_NUM_SW_FAILURE = 0
                             THEN SW_SIMPLE_MODEL
                             ELSE SW_COMPLEX_MODEL

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, failedSet, 
          statusResolveMsg, recoveredElem, toBeScheduledIRs, nextIR, 
          nextIRToSent, rowIndex, rowRemove, monitoringEvent, setIRsToReset, 
          resetIR, msg, controllerFailedModules

vars == << swSeqChangedStatus, switchStatus, installedIRs, failedTimes, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Ofa2InstallerBuff, 
           Installer2OfaBuff, TCAM, controlMsgCounter, controller2Switch, 
           switch2Controller, controllerState, switchOrdering, IR2SW, 
           controllerThreadPoolIRQueue, IRStatus, SwSuspensionStatus, 
           lastScheduledThread, SetScheduledIRs, 
           controllerInternalFailedTimes, ContProcSet, SwProcSet, 
           controllerStatus, idThreadWorkingOnIR, controllerDB, 
           dependencyGraph, workerThreadRanking, switchLock, controllerLock, 
           FirstInstall, pc, ingressPkt, ingressIR, egressMsg, ofaInMsg, 
           ofaOutConfirmation, installerInIR, statusMsg, notFailedSet, 
           failedElem, failedSet, statusResolveMsg, recoveredElem, 
           toBeScheduledIRs, nextIR, nextIRToSent, rowIndex, rowRemove, 
           monitoringEvent, setIRsToReset, resetIR, msg, 
           controllerFailedModules >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({c0} \X {CONT_SEQ})) \cup (({c0} \X CONTROLLER_THREAD_POOL)) \cup (({c0} \X {CONT_EVENT})) \cup (({c0} \X {CONT_MONITOR})) \cup (({c0} \X {WATCH_DOG}))

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
        /\ IR2SW = (CHOOSE x \in [1..MaxNumIRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z
                                                                              /\ switchOrdering[x[y]] =< switchOrdering[x[z]])
        /\ controllerThreadPoolIRQueue = [y \in {c0, c1} |-> <<>>]
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ lastScheduledThread = 0
        /\ SetScheduledIRs = [x \in {c0, c1} |-> [y \in SW |-> {}]]
        /\ controllerInternalFailedTimes = [x \in {c0, c1} |-> 0]
        /\ ContProcSet = ((({c0, c1} \X {CONT_SEQ})) \cup (({c0, c1} \X CONTROLLER_THREAD_POOL)) \cup (({c0, c1} \X {CONT_EVENT})) \cup (({c0, c1} \X {CONT_MONITOR})))
        /\ SwProcSet = ((({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)))
        /\ controllerStatus = [x \in ContProcSet |-> NotFailed]
        /\ idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK]
        /\ controllerDB = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
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
        /\ nextIR = [self \in ({c0} \X {CONT_SEQ}) |-> 0]
        (* Process controllerWorkerThreads *)
        /\ nextIRToSent = [self \in ({c0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ rowIndex = [self \in ({c0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ rowRemove = [self \in ({c0} \X CONTROLLER_THREAD_POOL) |-> -1]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({c0} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({c0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({c0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({c0} \X {CONT_MONITOR}) |-> [type |-> 0]]
        (* Process watchDog *)
        /\ controllerFailedModules = [self \in ({c0} \X {WATCH_DOG}) |-> {}]
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
                                        [] self \in ({c0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({c0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type = INSTALL_FLOW, 
                                       "Failure of assertion at line 639, column 9.")
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
                                             SetScheduledIRs, 
                                             controllerInternalFailedTimes, 
                                             ContProcSet, SwProcSet, 
                                             controllerStatus, 
                                             idThreadWorkingOnIR, controllerDB, 
                                             dependencyGraph, 
                                             workerThreadRanking, switchLock, 
                                             controllerLock, FirstInstall, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, 
                                             controllerFailedModules >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(\/ ingressIR'[self].type = RECONCILIATION_REQUEST
                                   \/ ingressIR'[self].type = INSTALL_FLOW, 
                                   "Failure of assertion at line 662, column 9.")
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                         controllerInternalFailedTimes, 
                                         ContProcSet, SwProcSet, 
                                         controllerStatus, idThreadWorkingOnIR, 
                                         controllerDB, dependencyGraph, 
                                         workerThreadRanking, controllerLock, 
                                         FirstInstall, ingressPkt, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         toBeScheduledIRs, nextIR, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, msg, controllerFailedModules >>

SwitchNicAsicInsertToOfaBuff(self) == /\ pc[self] = "SwitchNicAsicInsertToOfaBuff"
                                      /\ IF swCanReceivePackets(self[2])
                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
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
                                                      controllerInternalFailedTimes, 
                                                      ContProcSet, SwProcSet, 
                                                      controllerStatus, 
                                                      idThreadWorkingOnIR, 
                                                      controllerDB, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      controllerLock, 
                                                      FirstInstall, ingressPkt, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      msg, 
                                                      controllerFailedModules >>

swNicAsicProcPacketIn(self) == SwitchRcvPacket(self)
                                  \/ SwitchNicAsicInsertToOfaBuff(self)

SwitchFromOFAPacket(self) == /\ pc[self] = "SwitchFromOFAPacket"
                             /\ swCanReceivePackets(self[2])
                             /\ Len(Ofa2NicAsicBuff[self[2]]) > 0
                             /\ egressMsg' = [egressMsg EXCEPT ![self] = Head(Ofa2NicAsicBuff[self[2]])]
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ switchLock' = self
                             /\ Assert(\/ egressMsg'[self].type = INSTALLED_SUCCESSFULLY
                                       \/ egressMsg'[self].type = RECEIVED_SUCCESSFULLY
                                       \/ egressMsg'[self].type = RECONCILIATION_RESPONSE, 
                                       "Failure of assertion at line 687, column 9.")
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
                                             SetScheduledIRs, 
                                             controllerInternalFailedTimes, 
                                             ContProcSet, SwProcSet, 
                                             controllerStatus, 
                                             idThreadWorkingOnIR, controllerDB, 
                                             dependencyGraph, 
                                             workerThreadRanking, 
                                             controllerLock, FirstInstall, 
                                             ingressPkt, ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, 
                                             controllerFailedModules >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 392, column 9 of macro called at line 695, column 17.")
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
                                                 controllerInternalFailedTimes, 
                                                 ContProcSet, SwProcSet, 
                                                 controllerStatus, 
                                                 idThreadWorkingOnIR, 
                                                 controllerDB, dependencyGraph, 
                                                 workerThreadRanking, 
                                                 controllerLock, FirstInstall, 
                                                 ingressPkt, ingressIR, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, nextIR, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 controllerFailedModules >>

swNicAsicProcPacketOut(self) == SwitchFromOFAPacket(self)
                                   \/ SwitchNicAsicSendOutMsg(self)

SwitchOfaProcIn(self) == /\ pc[self] = "SwitchOfaProcIn"
                         /\ swOFACanProcessIRs(self[2])
                         /\ Len(NicAsic2OfaBuff[self[2]]) > 0
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = Head(NicAsic2OfaBuff[self[2]])]
                         /\ Assert(ofaInMsg'[self].to = self[2], 
                                   "Failure of assertion at line 716, column 9.")
                         /\ Assert(ofaInMsg'[self].IR  \in 1..MaxNumIRs, 
                                   "Failure of assertion at line 717, column 9.")
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
                                         controllerInternalFailedTimes, 
                                         ContProcSet, SwProcSet, 
                                         controllerStatus, idThreadWorkingOnIR, 
                                         controllerDB, dependencyGraph, 
                                         workerThreadRanking, controllerLock, 
                                         FirstInstall, ingressPkt, ingressIR, 
                                         egressMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         toBeScheduledIRs, nextIR, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, msg, controllerFailedModules >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                           /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           /\ switchLock' = <<INSTALLER, self[2]>>
                                           /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                                 THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], ofaInMsg[self].IR)]
                                                 ELSE /\ Assert(FALSE, 
                                                                "Failure of assertion at line 729, column 21.")
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
                                                controllerInternalFailedTimes, 
                                                ContProcSet, SwProcSet, 
                                                controllerStatus, 
                                                idThreadWorkingOnIR, 
                                                controllerDB, dependencyGraph, 
                                                workerThreadRanking, 
                                                controllerLock, FirstInstall, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIR, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, monitoringEvent, 
                                                setIRsToReset, resetIR, msg, 
                                                controllerFailedModules >>

ofaModuleProcPacketIn(self) == SwitchOfaProcIn(self)
                                  \/ SwitchOfaProcessPacket(self)

SwitchOfaProcOut(self) == /\ pc[self] = "SwitchOfaProcOut"
                          /\ swOFACanProcessIRs(self[2])
                          /\ Installer2OfaBuff[self[2]] # <<>>
                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                          /\ switchLock' = self
                          /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = Head(Installer2OfaBuff[self[2]])]
                          /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Tail(Installer2OfaBuff[self[2]])]
                          /\ Assert(ofaOutConfirmation'[self] \in 1..MaxNumIRs, 
                                    "Failure of assertion at line 748, column 9.")
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
                                          controllerInternalFailedTimes, 
                                          ContProcSet, SwProcSet, 
                                          controllerStatus, 
                                          idThreadWorkingOnIR, controllerDB, 
                                          dependencyGraph, workerThreadRanking, 
                                          controllerLock, FirstInstall, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, nextIR, 
                                          nextIRToSent, rowIndex, rowRemove, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, msg, 
                                          controllerFailedModules >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
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
                                                      controllerInternalFailedTimes, 
                                                      ContProcSet, SwProcSet, 
                                                      controllerStatus, 
                                                      idThreadWorkingOnIR, 
                                                      controllerDB, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      controllerLock, 
                                                      FirstInstall, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, installerInIR, 
                                                      statusMsg, notFailedSet, 
                                                      failedElem, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      msg, 
                                                      controllerFailedModules >>

ofaModuleProcPacketOut(self) == SwitchOfaProcOut(self)
                                   \/ SendInstallationConfirmation(self)

SwitchInstallerProc(self) == /\ pc[self] = "SwitchInstallerProc"
                             /\ swCanInstallIRs(self[2])
                             /\ Len(Ofa2InstallerBuff[self[2]]) > 0
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ switchLock' = self
                             /\ installerInIR' = [installerInIR EXCEPT ![self] = Head(Ofa2InstallerBuff[self[2]])]
                             /\ Assert(installerInIR'[self] \in 1..MaxNumIRs, 
                                       "Failure of assertion at line 776, column 8.")
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
                                             SetScheduledIRs, 
                                             controllerInternalFailedTimes, 
                                             ContProcSet, SwProcSet, 
                                             controllerStatus, 
                                             idThreadWorkingOnIR, controllerDB, 
                                             dependencyGraph, 
                                             workerThreadRanking, 
                                             controllerLock, FirstInstall, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, 
                                             controllerFailedModules >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                               /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
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
                                                    controllerInternalFailedTimes, 
                                                    ContProcSet, SwProcSet, 
                                                    controllerStatus, 
                                                    idThreadWorkingOnIR, 
                                                    controllerDB, 
                                                    dependencyGraph, 
                                                    workerThreadRanking, 
                                                    controllerLock, 
                                                    FirstInstall, ingressPkt, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, nextIR, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    msg, 
                                                    controllerFailedModules >>

SwitchInstallerSendConfirmation(self) == /\ pc[self] = "SwitchInstallerSendConfirmation"
                                         /\ IF swCanInstallIRs(self[2])
                                               THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                    /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
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
                                                         controllerInternalFailedTimes, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         controllerStatus, 
                                                         idThreadWorkingOnIR, 
                                                         controllerDB, 
                                                         dependencyGraph, 
                                                         workerThreadRanking, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, 
                                                         nextIR, nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, 
                                                         controllerFailedModules >>

installerModuleProc(self) == SwitchInstallerProc(self)
                                \/ SwitchInstallerInsert2TCAM(self)
                                \/ SwitchInstallerSendConfirmation(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ notFailedSet' = [notFailedSet EXCEPT ![self] = returnSwitchElementsNotFailed(self[2])]
                       /\ notFailedSet'[self] # {}
                       /\ ~isFinished
                       /\ failedTimes[self[2]] < MAX_NUM_SW_FAILURE
                       /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                             \/ switchLock[2] = self[2]
                       /\ \E elem \in notFailedSet'[self]:
                            failedElem' = [failedElem EXCEPT ![self] = elem]
                       /\ IF failedElem'[self] = "cpu"
                             THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                  /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                            "Failure of assertion at line 248, column 9 of macro called at line 820, column 17.")
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
                                                       "Failure of assertion at line 293, column 9 of macro called at line 823, column 17.")
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
                                                                  "Failure of assertion at line 331, column 9 of macro called at line 826, column 17.")
                                                        /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                        /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                                                        /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                              THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                             "Failure of assertion at line 335, column 13 of macro called at line 826, column 17.")
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
                                                                             "Failure of assertion at line 209, column 9 of macro called at line 829, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                   /\ failedTimes' = [failedTimes EXCEPT ![self[2]] = failedTimes[self[2]] + 1]
                                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]]]]
                                                                   /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                                              ELSE /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 830, column 14.")
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
                                 "Failure of assertion at line 392, column 9 of macro called at line 833, column 9.")
                       /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                       /\ UNCHANGED << installedIRs, TCAM, switch2Controller, 
                                       controllerState, switchOrdering, IR2SW, 
                                       controllerThreadPoolIRQueue, IRStatus, 
                                       SwSuspensionStatus, lastScheduledThread, 
                                       SetScheduledIRs, 
                                       controllerInternalFailedTimes, 
                                       ContProcSet, SwProcSet, 
                                       controllerStatus, idThreadWorkingOnIR, 
                                       controllerDB, dependencyGraph, 
                                       workerThreadRanking, controllerLock, 
                                       FirstInstall, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, failedSet, 
                                       statusResolveMsg, recoveredElem, 
                                       toBeScheduledIRs, nextIR, nextIRToSent, 
                                       rowIndex, rowRemove, monitoringEvent, 
                                       setIRsToReset, resetIR, msg, 
                                       controllerFailedModules >>

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ failedSet' = [failedSet EXCEPT ![self] = returnSwitchFailedElements(self[2])]
                              /\ Cardinality(failedSet'[self]) > 0
                              /\ ~isFinished
                              /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ \E elem \in failedSet'[self]:
                                   recoveredElem' = [recoveredElem EXCEPT ![self] = elem]
                              /\ IF recoveredElem'[self] = "cpu"
                                    THEN /\ ofaStartingMode(self[2]) /\ installerInStartingMode(self[2])
                                         /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                   "Failure of assertion at line 271, column 9 of macro called at line 853, column 39.")
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
                                                              "Failure of assertion at line 225, column 9 of macro called at line 854, column 46.")
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
                                                                         "Failure of assertion at line 312, column 9 of macro called at line 855, column 42.")
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
                                                                                    "Failure of assertion at line 350, column 9 of macro called at line 856, column 48.")
                                                                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                               "Failure of assertion at line 353, column 13 of macro called at line 856, column 48.")
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
                                                                                    "Failure of assertion at line 857, column 14.")
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
                                              SetScheduledIRs, 
                                              controllerInternalFailedTimes, 
                                              ContProcSet, SwProcSet, 
                                              controllerStatus, 
                                              idThreadWorkingOnIR, 
                                              controllerDB, dependencyGraph, 
                                              workerThreadRanking, switchLock, 
                                              controllerLock, FirstInstall, 
                                              ingressPkt, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              toBeScheduledIRs, nextIR, 
                                              nextIRToSent, rowIndex, 
                                              rowRemove, monitoringEvent, 
                                              setIRsToReset, resetIR, msg, 
                                              controllerFailedModules >>

swResolveFailure(self) == SwitchResolveFailure(self)

ghostProc(self) == /\ pc[self] = "ghostProc"
                   /\ /\ switchLock # <<NO_LOCK, NO_LOCK>>
                      /\ switchLock[2] = self[2]
                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                   /\ Assert(\/ switchLock[2] = switchLock[2]
                             \/ switchLock[2] = NO_LOCK, 
                             "Failure of assertion at line 392, column 9 of macro called at line 889, column 9.")
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
                                   SetScheduledIRs, 
                                   controllerInternalFailedTimes, ContProcSet, 
                                   SwProcSet, controllerStatus, 
                                   idThreadWorkingOnIR, controllerDB, 
                                   dependencyGraph, workerThreadRanking, 
                                   controllerLock, FirstInstall, ingressPkt, 
                                   ingressIR, egressMsg, ofaInMsg, 
                                   ofaOutConfirmation, installerInIR, 
                                   statusMsg, notFailedSet, failedElem, 
                                   failedSet, statusResolveMsg, recoveredElem, 
                                   toBeScheduledIRs, nextIR, nextIRToSent, 
                                   rowIndex, rowRemove, monitoringEvent, 
                                   setIRsToReset, resetIR, msg, 
                                   controllerFailedModules >>

ghostUnlockProcess(self) == ghostProc(self)

ControllerSeqProc(self) == /\ pc[self] = "ControllerSeqProc"
                           /\ moduleIsUp(self)
                           /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1])]
                           /\ toBeScheduledIRs'[self] # {}
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
                                           SetScheduledIRs, 
                                           controllerInternalFailedTimes, 
                                           ContProcSet, SwProcSet, 
                                           controllerStatus, 
                                           idThreadWorkingOnIR, controllerDB, 
                                           dependencyGraph, 
                                           workerThreadRanking, switchLock, 
                                           controllerLock, FirstInstall, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           nextIR, nextIRToSent, rowIndex, 
                                           rowRemove, monitoringEvent, 
                                           setIRsToReset, resetIR, msg, 
                                           controllerFailedModules >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                  THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                             /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << controllerInternalFailedTimes, 
                                                       controllerStatus >>
                            /\ IF (controllerStatus'[self] = NotFailed)
                                  THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                                       /\ pc' = [pc EXCEPT ![self] = "SeqUpdateDBState1"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                       /\ UNCHANGED nextIR
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
                                            SetScheduledIRs, ContProcSet, 
                                            SwProcSet, idThreadWorkingOnIR, 
                                            controllerDB, dependencyGraph, 
                                            workerThreadRanking, switchLock, 
                                            controllerLock, FirstInstall, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, toBeScheduledIRs, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, msg, 
                                            controllerFailedModules >>

SeqUpdateDBState1(self) == /\ pc[self] = "SeqUpdateDBState1"
                           /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                 THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                            /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                         \/ /\ TRUE
                                            /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << controllerInternalFailedTimes, 
                                                      controllerStatus >>
                           /\ IF (controllerStatus'[self] = NotFailed)
                                 THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> STATUS_START_SCHEDULING, next |-> nextIR[self]]]
                                      /\ pc' = [pc EXCEPT ![self] = "AddToScheduleIRSet"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                      /\ UNCHANGED controllerDB
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
                                           SetScheduledIRs, ContProcSet, 
                                           SwProcSet, idThreadWorkingOnIR, 
                                           dependencyGraph, 
                                           workerThreadRanking, switchLock, 
                                           controllerLock, FirstInstall, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           toBeScheduledIRs, nextIR, 
                                           nextIRToSent, rowIndex, rowRemove, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, msg, 
                                           controllerFailedModules >>

AddToScheduleIRSet(self) == /\ pc[self] = "AddToScheduleIRSet"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                  THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                             /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << controllerInternalFailedTimes, 
                                                       controllerStatus >>
                            /\ IF (controllerStatus'[self] = NotFailed)
                                  THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![self[1]][IR2SW[nextIR[self]]] = SetScheduledIRs[self[1]][IR2SW[nextIR[self]]] \cup {nextIR[self]}]
                                       /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                       /\ UNCHANGED SetScheduledIRs
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
                                            lastScheduledThread, ContProcSet, 
                                            SwProcSet, idThreadWorkingOnIR, 
                                            controllerDB, dependencyGraph, 
                                            workerThreadRanking, switchLock, 
                                            controllerLock, FirstInstall, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, toBeScheduledIRs, 
                                            nextIR, nextIRToSent, rowIndex, 
                                            rowRemove, monitoringEvent, 
                                            setIRsToReset, resetIR, msg, 
                                            controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                             THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                        /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                     \/ /\ TRUE
                                        /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                             ELSE /\ TRUE
                                  /\ UNCHANGED << controllerInternalFailedTimes, 
                                                  controllerStatus >>
                       /\ IF (controllerStatus'[self] = NotFailed)
                             THEN /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]] = Append(controllerThreadPoolIRQueue[self[1]], [IR |-> nextIR[self], tag |-> NO_TAG])]
                                  /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "SeqClearDBState"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                  /\ UNCHANGED << controllerThreadPoolIRQueue, 
                                                  toBeScheduledIRs >>
                       /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                       installedIRs, failedTimes, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Ofa2InstallerBuff, Installer2OfaBuff, 
                                       TCAM, controlMsgCounter, 
                                       controller2Switch, switch2Controller, 
                                       controllerState, switchOrdering, IR2SW, 
                                       IRStatus, SwSuspensionStatus, 
                                       lastScheduledThread, SetScheduledIRs, 
                                       ContProcSet, SwProcSet, 
                                       idThreadWorkingOnIR, controllerDB, 
                                       dependencyGraph, workerThreadRanking, 
                                       switchLock, controllerLock, 
                                       FirstInstall, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, failedSet, statusResolveMsg, 
                                       recoveredElem, nextIR, nextIRToSent, 
                                       rowIndex, rowRemove, monitoringEvent, 
                                       setIRsToReset, resetIR, msg, 
                                       controllerFailedModules >>

SeqClearDBState(self) == /\ pc[self] = "SeqClearDBState"
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                         /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                               THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                          /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                       \/ /\ TRUE
                                          /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                               ELSE /\ TRUE
                                    /\ UNCHANGED << controllerInternalFailedTimes, 
                                                    controllerStatus >>
                         /\ IF (controllerStatus'[self] = NotFailed)
                               THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> NO_STATUS]]
                                    /\ IF toBeScheduledIRs[self] = {}
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                    /\ UNCHANGED controllerDB
                         /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                         installedIRs, failedTimes, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Ofa2InstallerBuff, Installer2OfaBuff, 
                                         TCAM, controlMsgCounter, 
                                         controller2Switch, switch2Controller, 
                                         controllerState, switchOrdering, 
                                         IR2SW, controllerThreadPoolIRQueue, 
                                         IRStatus, SwSuspensionStatus, 
                                         lastScheduledThread, SetScheduledIRs, 
                                         ContProcSet, SwProcSet, 
                                         idThreadWorkingOnIR, dependencyGraph, 
                                         workerThreadRanking, switchLock, 
                                         controllerLock, FirstInstall, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         toBeScheduledIRs, nextIR, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, msg, controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ controllerIsMaster(self[1])
                                          /\ moduleIsUp(self)
                                          /\ \/ controllerLock = self
                                             \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (controllerDB[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![self[1]][IR2SW[controllerDB[self].next]] = SetScheduledIRs[self[1]][IR2SW[controllerDB[self].next]]\{controllerDB[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
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
                                                          controllerInternalFailedTimes, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          controllerStatus, 
                                                          idThreadWorkingOnIR, 
                                                          controllerDB, 
                                                          dependencyGraph, 
                                                          workerThreadRanking, 
                                                          switchLock, 
                                                          FirstInstall, 
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
                                                          nextIR, nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, 
                                                          controllerFailedModules >>

controllerSequencer(self) == ControllerSeqProc(self)
                                \/ SchedulerMechanism(self)
                                \/ SeqUpdateDBState1(self)
                                \/ AddToScheduleIRSet(self)
                                \/ ScheduleTheIR(self)
                                \/ SeqClearDBState(self)
                                \/ ControllerSeqStateReconciliation(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerIsMaster(self[1])
                          /\ moduleIsUp(self)
                          /\ controllerThreadPoolIRQueue[self[1]] # <<>>
                          /\ canWorkerThreadContinue(self[1], self)
                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead(self, self[1])]
                          /\ nextIRToSent' = [nextIRToSent EXCEPT ![self] = controllerThreadPoolIRQueue[self[1]][rowIndex'[self]].IR]
                          /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]][rowIndex'[self]].tag = self]
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSaveToDB1"]
                          /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                          installedIRs, failedTimes, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, Installer2OfaBuff, 
                                          TCAM, controlMsgCounter, 
                                          controller2Switch, switch2Controller, 
                                          controllerState, switchOrdering, 
                                          IR2SW, IRStatus, SwSuspensionStatus, 
                                          lastScheduledThread, SetScheduledIRs, 
                                          controllerInternalFailedTimes, 
                                          ContProcSet, SwProcSet, 
                                          controllerStatus, 
                                          idThreadWorkingOnIR, controllerDB, 
                                          dependencyGraph, workerThreadRanking, 
                                          switchLock, controllerLock, 
                                          FirstInstall, ingressPkt, ingressIR, 
                                          egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, toBeScheduledIRs, 
                                          nextIR, rowRemove, monitoringEvent, 
                                          setIRsToReset, resetIR, msg, 
                                          controllerFailedModules >>

ControllerThreadSaveToDB1(self) == /\ pc[self] = "ControllerThreadSaveToDB1"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                         THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                    /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                 \/ /\ TRUE
                                                    /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controllerInternalFailedTimes, 
                                                              controllerStatus >>
                                   /\ IF (controllerStatus'[self] = NotFailed)
                                         THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent[self]]]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThreadLockTheIRUsingSemaphore"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                              /\ UNCHANGED controllerDB
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
                                                   SwSuspensionStatus, 
                                                   lastScheduledThread, 
                                                   SetScheduledIRs, 
                                                   ContProcSet, SwProcSet, 
                                                   idThreadWorkingOnIR, 
                                                   dependencyGraph, 
                                                   workerThreadRanking, 
                                                   switchLock, controllerLock, 
                                                   FirstInstall, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, nextIR, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   controllerFailedModules >>

ControllerThreadLockTheIRUsingSemaphore(self) == /\ pc[self] = "ControllerThreadLockTheIRUsingSemaphore"
                                                 /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                                       THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                                  /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                               \/ /\ TRUE
                                                                  /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                            controllerStatus >>
                                                 /\ IF (controllerStatus'[self] = NotFailed)
                                                       THEN /\ IF idThreadWorkingOnIR[nextIRToSent[self]] = IR_UNLOCK
                                                                  THEN /\ threadWithLowerIDGetsTheLock(self[1], self, nextIRToSent[self])
                                                                       /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent[self]] = self[2]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveQueue1"]
                                                                       /\ UNCHANGED idThreadWorkingOnIR
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                            /\ UNCHANGED idThreadWorkingOnIR
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
                                                                 ContProcSet, 
                                                                 SwProcSet, 
                                                                 controllerDB, 
                                                                 dependencyGraph, 
                                                                 workerThreadRanking, 
                                                                 switchLock, 
                                                                 controllerLock, 
                                                                 FirstInstall, 
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
                                                                 nextIR, 
                                                                 nextIRToSent, 
                                                                 rowIndex, 
                                                                 rowRemove, 
                                                                 monitoringEvent, 
                                                                 setIRsToReset, 
                                                                 resetIR, msg, 
                                                                 controllerFailedModules >>

ControllerThreadRemoveQueue1(self) == /\ pc[self] = "ControllerThreadRemoveQueue1"
                                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self[1], self)]
                                      /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]] = removeFromSeq(controllerThreadPoolIRQueue[self[1]], rowRemove'[self])]
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
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
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      controllerInternalFailedTimes, 
                                                      ContProcSet, SwProcSet, 
                                                      controllerStatus, 
                                                      idThreadWorkingOnIR, 
                                                      controllerDB, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      nextIRToSent, rowIndex, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      msg, 
                                                      controllerFailedModules >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                      THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                 /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                              \/ /\ TRUE
                                                 /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << controllerInternalFailedTimes, 
                                                           controllerStatus >>
                                /\ IF (controllerStatus'[self] = NotFailed)
                                      THEN /\ IF ~isSwitchSuspended(IR2SW[nextIRToSent[self]]) /\ IRStatus[nextIRToSent[self]] = IR_NONE
                                                 THEN /\ IRStatus' = [IRStatus EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForIRToHaveCorrectStatus"]
                                                      /\ UNCHANGED IRStatus
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
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
                                                SetScheduledIRs, ContProcSet, 
                                                SwProcSet, idThreadWorkingOnIR, 
                                                controllerDB, dependencyGraph, 
                                                workerThreadRanking, 
                                                switchLock, controllerLock, 
                                                FirstInstall, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIR, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, monitoringEvent, 
                                                setIRsToReset, resetIR, msg, 
                                                controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                         THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                    /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                 \/ /\ TRUE
                                                    /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controllerInternalFailedTimes, 
                                                              controllerStatus >>
                                   /\ IF (controllerStatus'[self] = NotFailed)
                                         THEN /\ controller2Switch' = [controller2Switch EXCEPT ![IR2SW[nextIRToSent[self]]] = Append(controller2Switch[IR2SW[nextIRToSent[self]]], [type |-> INSTALL_FLOW,
                                                                                                                                                                                     to |-> IR2SW[nextIRToSent[self]],
                                                                                                                                                                                     IR |-> nextIRToSent[self]])]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSaveToDB2"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                              /\ UNCHANGED controller2Switch
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
                                                   ContProcSet, SwProcSet, 
                                                   idThreadWorkingOnIR, 
                                                   controllerDB, 
                                                   dependencyGraph, 
                                                   workerThreadRanking, 
                                                   switchLock, controllerLock, 
                                                   FirstInstall, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, nextIR, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   controllerFailedModules >>

ControllerThreadSaveToDB2(self) == /\ pc[self] = "ControllerThreadSaveToDB2"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                         THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                    /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                 \/ /\ TRUE
                                                    /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controllerInternalFailedTimes, 
                                                              controllerStatus >>
                                   /\ IF (controllerStatus'[self] = NotFailed)
                                         THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> STATUS_SENT_DONE, next |-> nextIRToSent[self]]]
                                              /\ pc' = [pc EXCEPT ![self] = "WaitForIRToHaveCorrectStatus"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                              /\ UNCHANGED controllerDB
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
                                                   SwSuspensionStatus, 
                                                   lastScheduledThread, 
                                                   SetScheduledIRs, 
                                                   ContProcSet, SwProcSet, 
                                                   idThreadWorkingOnIR, 
                                                   dependencyGraph, 
                                                   workerThreadRanking, 
                                                   switchLock, controllerLock, 
                                                   FirstInstall, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, nextIR, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   controllerFailedModules >>

WaitForIRToHaveCorrectStatus(self) == /\ pc[self] = "WaitForIRToHaveCorrectStatus"
                                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                            THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                       /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                    \/ /\ TRUE
                                                       /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                 controllerStatus >>
                                      /\ IF (controllerStatus'[self] = NotFailed)
                                            THEN /\ ~isSwitchSuspended(IR2SW[nextIRToSent[self]])
                                                 /\ pc' = [pc EXCEPT ![self] = "ReScheduleifIRNone"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
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
                                                      ContProcSet, SwProcSet, 
                                                      idThreadWorkingOnIR, 
                                                      controllerDB, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      msg, 
                                                      controllerFailedModules >>

ReScheduleifIRNone(self) == /\ pc[self] = "ReScheduleifIRNone"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                  THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                             /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << controllerInternalFailedTimes, 
                                                       controllerStatus >>
                            /\ IF (controllerStatus'[self] = NotFailed)
                                  THEN /\ IF IRStatus[nextIRToSent[self]] = IR_NONE
                                             THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent[self]]]
                                                  /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                                  /\ UNCHANGED controllerDB
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                       /\ UNCHANGED controllerDB
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
                                            SetScheduledIRs, ContProcSet, 
                                            SwProcSet, idThreadWorkingOnIR, 
                                            dependencyGraph, 
                                            workerThreadRanking, switchLock, 
                                            controllerLock, FirstInstall, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, toBeScheduledIRs, 
                                            nextIR, nextIRToSent, rowIndex, 
                                            rowRemove, monitoringEvent, 
                                            setIRsToReset, resetIR, msg, 
                                            controllerFailedModules >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
                                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                               THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                          /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                       \/ /\ TRUE
                                                          /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                    controllerStatus >>
                                         /\ IF (controllerStatus'[self] = NotFailed)
                                               THEN /\ IF idThreadWorkingOnIR[nextIRToSent[self]] = self[2]
                                                          THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent[self]] = IR_UNLOCK]
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED idThreadWorkingOnIR
                                                    /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                    /\ UNCHANGED idThreadWorkingOnIR
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
                                                         switchOrdering, IR2SW, 
                                                         controllerThreadPoolIRQueue, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         lastScheduledThread, 
                                                         SetScheduledIRs, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         controllerDB, 
                                                         dependencyGraph, 
                                                         workerThreadRanking, 
                                                         switchLock, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, 
                                                         nextIR, nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, 
                                                         controllerFailedModules >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                        THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                   /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                \/ /\ TRUE
                                                   /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << controllerInternalFailedTimes, 
                                                             controllerStatus >>
                                  /\ IF (controllerStatus'[self] = NotFailed)
                                        THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![self[1]][IR2SW[nextIRToSent[self]]] = SetScheduledIRs[self[1]][IR2SW[nextIRToSent[self]]]\{nextIRToSent[self]}]
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThreadClearDB"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                             /\ UNCHANGED SetScheduledIRs
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
                                                  ContProcSet, SwProcSet, 
                                                  idThreadWorkingOnIR, 
                                                  controllerDB, 
                                                  dependencyGraph, 
                                                  workerThreadRanking, 
                                                  switchLock, controllerLock, 
                                                  FirstInstall, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, 
                                                  toBeScheduledIRs, nextIR, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, monitoringEvent, 
                                                  setIRsToReset, resetIR, msg, 
                                                  controllerFailedModules >>

ControllerThreadClearDB(self) == /\ pc[self] = "ControllerThreadClearDB"
                                 /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                       THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                  /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                               \/ /\ TRUE
                                                  /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << controllerInternalFailedTimes, 
                                                            controllerStatus >>
                                 /\ IF (controllerStatus'[self] = NotFailed)
                                       THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> NO_STATUS]]
                                            /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveQueue2"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                            /\ UNCHANGED controllerDB
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
                                                 SetScheduledIRs, ContProcSet, 
                                                 SwProcSet, 
                                                 idThreadWorkingOnIR, 
                                                 dependencyGraph, 
                                                 workerThreadRanking, 
                                                 switchLock, controllerLock, 
                                                 FirstInstall, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, nextIR, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, monitoringEvent, 
                                                 setIRsToReset, resetIR, msg, 
                                                 controllerFailedModules >>

ControllerThreadRemoveQueue2(self) == /\ pc[self] = "ControllerThreadRemoveQueue2"
                                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self[1], self)]
                                      /\ controllerThreadPoolIRQueue' = [controllerThreadPoolIRQueue EXCEPT ![self[1]] = removeFromSeq(controllerThreadPoolIRQueue[self[1]], rowRemove'[self])]
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
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
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      lastScheduledThread, 
                                                      SetScheduledIRs, 
                                                      controllerInternalFailedTimes, 
                                                      ContProcSet, SwProcSet, 
                                                      controllerStatus, 
                                                      idThreadWorkingOnIR, 
                                                      controllerDB, 
                                                      dependencyGraph, 
                                                      workerThreadRanking, 
                                                      switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      nextIRToSent, rowIndex, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      msg, 
                                                      controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ controllerIsMaster(self[1])
                                             /\ moduleIsUp(self)
                                             /\ controllerThreadPoolIRQueue[self[1]] # <<>>
                                             /\ canWorkerThreadContinue(self[1], self)
                                             /\ \/ controllerLock = self
                                                \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (controllerDB[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (IRStatus[controllerDB[self].next] = IR_SENT)
                                                              THEN /\ IRStatus' = [IRStatus EXCEPT ![controllerDB[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED IRStatus
                                                        /\ IF (idThreadWorkingOnIR[controllerDB[self].next] = self[2])
                                                              THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![controllerDB[self].next] = IR_UNLOCK]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                        /\ UNCHANGED SetScheduledIRs
                                                   ELSE /\ IF (controllerDB[self].type = STATUS_SENT_DONE)
                                                              THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![self[1]][IR2SW[controllerDB[self].next]] = SetScheduledIRs[self[1]][IR2SW[controllerDB[self].next]] \cup {controllerDB[self].next}]
                                                                   /\ IF (idThreadWorkingOnIR[controllerDB[self].next] = self[2])
                                                                         THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![controllerDB[self].next] = IR_UNLOCK]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED idThreadWorkingOnIR
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << SetScheduledIRs, 
                                                                                   idThreadWorkingOnIR >>
                                                        /\ UNCHANGED IRStatus
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
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
                                                             controllerInternalFailedTimes, 
                                                             ContProcSet, 
                                                             SwProcSet, 
                                                             controllerStatus, 
                                                             controllerDB, 
                                                             dependencyGraph, 
                                                             workerThreadRanking, 
                                                             switchLock, 
                                                             FirstInstall, 
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
                                                             nextIR, 
                                                             nextIRToSent, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, msg, 
                                                             controllerFailedModules >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSaveToDB1(self)
                                    \/ ControllerThreadLockTheIRUsingSemaphore(self)
                                    \/ ControllerThreadRemoveQueue1(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadSaveToDB2(self)
                                    \/ WaitForIRToHaveCorrectStatus(self)
                                    \/ ReScheduleifIRNone(self)
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadClearDB(self)
                                    \/ ControllerThreadRemoveQueue2(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerIsMaster(self[1])
                                    /\ moduleIsUp(self)
                                    /\ swSeqChangedStatus # <<>>
                                    /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerSaveToDB1"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
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
                                                    SwSuspensionStatus, 
                                                    lastScheduledThread, 
                                                    SetScheduledIRs, 
                                                    controllerInternalFailedTimes, 
                                                    ContProcSet, SwProcSet, 
                                                    controllerStatus, 
                                                    idThreadWorkingOnIR, 
                                                    controllerDB, 
                                                    dependencyGraph, 
                                                    workerThreadRanking, 
                                                    switchLock, controllerLock, 
                                                    FirstInstall, ingressPkt, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, nextIR, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, setIRsToReset, 
                                                    resetIR, msg, 
                                                    controllerFailedModules >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                                         THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                                    /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                                 \/ /\ TRUE
                                                                    /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                              controllerStatus >>
                                                   /\ IF (controllerStatus'[self] = NotFailed)
                                                         THEN /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                              /\ UNCHANGED swSeqChangedStatus
                                                   /\ UNCHANGED << switchStatus, 
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
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   idThreadWorkingOnIR, 
                                                                   controllerDB, 
                                                                   dependencyGraph, 
                                                                   workerThreadRanking, 
                                                                   switchLock, 
                                                                   controllerLock, 
                                                                   FirstInstall, 
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
                                                                   nextIR, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, 
                                                                   controllerFailedModules >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                   THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                              /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                           \/ /\ TRUE
                                              /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << controllerInternalFailedTimes, 
                                                        controllerStatus >>
                             /\ IF (controllerStatus'[self] = NotFailed)
                                   THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED SwSuspensionStatus
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
                                             SetScheduledIRs, ContProcSet, 
                                             SwProcSet, idThreadWorkingOnIR, 
                                             controllerDB, dependencyGraph, 
                                             workerThreadRanking, switchLock, 
                                             controllerLock, FirstInstall, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, toBeScheduledIRs, 
                                             nextIR, nextIRToSent, rowIndex, 
                                             rowRemove, monitoringEvent, 
                                             setIRsToReset, resetIR, msg, 
                                             controllerFailedModules >>

ControllerEventHandlerSaveToDB1(self) == /\ pc[self] = "ControllerEventHandlerSaveToDB1"
                                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                               THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                          /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                       \/ /\ TRUE
                                                          /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                    controllerStatus >>
                                         /\ IF (controllerStatus'[self] = NotFailed)
                                               THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                    /\ UNCHANGED controllerDB
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
                                                         switchOrdering, IR2SW, 
                                                         controllerThreadPoolIRQueue, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         lastScheduledThread, 
                                                         SetScheduledIRs, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         idThreadWorkingOnIR, 
                                                         dependencyGraph, 
                                                         workerThreadRanking, 
                                                         switchLock, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, 
                                                         nextIR, nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, 
                                                         controllerFailedModules >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                         THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                    /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                 \/ /\ TRUE
                                                    /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controllerInternalFailedTimes, 
                                                              controllerStatus >>
                                   /\ IF (controllerStatus'[self] = NotFailed)
                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                              /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                              /\ UNCHANGED SwSuspensionStatus
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
                                                   ContProcSet, SwProcSet, 
                                                   idThreadWorkingOnIR, 
                                                   controllerDB, 
                                                   dependencyGraph, 
                                                   workerThreadRanking, 
                                                   switchLock, controllerLock, 
                                                   FirstInstall, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, nextIR, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   controllerFailedModules >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                                THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                           /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                        \/ /\ TRUE
                                                           /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                     controllerStatus >>
                                          /\ IF (controllerStatus'[self] = NotFailed)
                                                THEN /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                           THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
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
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          idThreadWorkingOnIR, 
                                                          controllerDB, 
                                                          dependencyGraph, 
                                                          workerThreadRanking, 
                                                          switchLock, 
                                                          controllerLock, 
                                                          FirstInstall, 
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
                                                          nextIR, nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, msg, 
                                                          controllerFailedModules >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                 THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                            /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                         \/ /\ TRUE
                                            /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << controllerInternalFailedTimes, 
                                                      controllerStatus >>
                           /\ IF (controllerStatus'[self] = NotFailed)
                                 THEN /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = getIRSetToReset(monitoringEvent[self].swID)]
                                      /\ IF (setIRsToReset'[self] = {})
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerClearDB"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                      /\ UNCHANGED setIRsToReset
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
                                           SetScheduledIRs, ContProcSet, 
                                           SwProcSet, idThreadWorkingOnIR, 
                                           controllerDB, dependencyGraph, 
                                           workerThreadRanking, switchLock, 
                                           controllerLock, FirstInstall, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           toBeScheduledIRs, nextIR, 
                                           nextIRToSent, rowIndex, rowRemove, 
                                           monitoringEvent, resetIR, msg, 
                                           controllerFailedModules >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                           THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                      /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                   \/ /\ TRUE
                                      /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                           ELSE /\ TRUE
                                /\ UNCHANGED << controllerInternalFailedTimes, 
                                                controllerStatus >>
                     /\ IF (controllerStatus'[self] = NotFailed)
                           THEN /\ resetIR' = [resetIR EXCEPT ![self] = CHOOSE x \in setIRsToReset[self]: TRUE]
                                /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR'[self]}]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerResetIRStatAfterRecovery"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                /\ UNCHANGED << setIRsToReset, resetIR >>
                     /\ UNCHANGED << swSeqChangedStatus, switchStatus, 
                                     installedIRs, failedTimes, 
                                     NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                     Ofa2InstallerBuff, Installer2OfaBuff, 
                                     TCAM, controlMsgCounter, 
                                     controller2Switch, switch2Controller, 
                                     controllerState, switchOrdering, IR2SW, 
                                     controllerThreadPoolIRQueue, IRStatus, 
                                     SwSuspensionStatus, lastScheduledThread, 
                                     SetScheduledIRs, ContProcSet, SwProcSet, 
                                     idThreadWorkingOnIR, controllerDB, 
                                     dependencyGraph, workerThreadRanking, 
                                     switchLock, controllerLock, FirstInstall, 
                                     ingressPkt, ingressIR, egressMsg, 
                                     ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, failedSet, statusResolveMsg, 
                                     recoveredElem, toBeScheduledIRs, nextIR, 
                                     nextIRToSent, rowIndex, rowRemove, 
                                     monitoringEvent, msg, 
                                     controllerFailedModules >>

ControllerResetIRStatAfterRecovery(self) == /\ pc[self] = "ControllerResetIRStatAfterRecovery"
                                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                                  THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                             /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                          \/ /\ TRUE
                                                             /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                       controllerStatus >>
                                            /\ IF (controllerStatus'[self] = NotFailed)
                                                  THEN /\ IF IRStatus[resetIR[self]] # IR_DONE
                                                             THEN /\ IRStatus' = [IRStatus EXCEPT ![resetIR[self]] = IR_NONE]
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED IRStatus
                                                       /\ IF setIRsToReset[self] = {}
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerClearDB"]
                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                       /\ UNCHANGED IRStatus
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
                                                            ContProcSet, 
                                                            SwProcSet, 
                                                            idThreadWorkingOnIR, 
                                                            controllerDB, 
                                                            dependencyGraph, 
                                                            workerThreadRanking, 
                                                            switchLock, 
                                                            controllerLock, 
                                                            FirstInstall, 
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
                                                            nextIR, 
                                                            nextIRToSent, 
                                                            rowIndex, 
                                                            rowRemove, 
                                                            monitoringEvent, 
                                                            setIRsToReset, 
                                                            resetIR, msg, 
                                                            controllerFailedModules >>

ControllerEventHandlerClearDB(self) == /\ pc[self] = "ControllerEventHandlerClearDB"
                                       /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                             THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                        /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                     \/ /\ TRUE
                                                        /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                  controllerStatus >>
                                       /\ IF (controllerStatus'[self] = NotFailed)
                                             THEN /\ controllerDB' = [controllerDB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                  /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                  /\ UNCHANGED controllerDB
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
                                                       ContProcSet, SwProcSet, 
                                                       idThreadWorkingOnIR, 
                                                       dependencyGraph, 
                                                       workerThreadRanking, 
                                                       switchLock, 
                                                       controllerLock, 
                                                       FirstInstall, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       toBeScheduledIRs, 
                                                       nextIR, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       msg, 
                                                       controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ controllerIsMaster(self[1])
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus # <<>>
                                                   /\ \/ controllerLock = self
                                                      \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (controllerDB[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![controllerDB[self].sw] = SW_SUSPEND]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED SwSuspensionStatus
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
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
                                                                   lastScheduledThread, 
                                                                   SetScheduledIRs, 
                                                                   controllerInternalFailedTimes, 
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   controllerStatus, 
                                                                   idThreadWorkingOnIR, 
                                                                   controllerDB, 
                                                                   dependencyGraph, 
                                                                   workerThreadRanking, 
                                                                   switchLock, 
                                                                   FirstInstall, 
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
                                                                   nextIR, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, 
                                                                   controllerFailedModules >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerEventHandlerSaveToDB1(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerResetIRStatAfterRecovery(self)
                                   \/ ControllerEventHandlerClearDB(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ controllerIsMaster(self[1])
                                       /\ moduleIsUp(self)
                                       /\ switch2Controller # <<>>
                                       /\ \/ controllerLock = self
                                          \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].from = IR2SW[msg'[self].IR], 
                                                 "Failure of assertion at line 1232, column 9.")
                                       /\ Assert(msg'[self].type \in {RECONCILIATION_RESPONSE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                 "Failure of assertion at line 1233, column 9.")
                                       /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIR2"]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 1261, column 18.")
                                                  /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
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
                                                       controllerInternalFailedTimes, 
                                                       ContProcSet, SwProcSet, 
                                                       controllerStatus, 
                                                       idThreadWorkingOnIR, 
                                                       controllerDB, 
                                                       dependencyGraph, 
                                                       workerThreadRanking, 
                                                       switchLock, 
                                                       FirstInstall, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       toBeScheduledIRs, 
                                                       nextIR, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       controllerFailedModules >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                               THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                                          /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                                       \/ /\ TRUE
                                                          /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << controllerInternalFailedTimes, 
                                                                    controllerStatus >>
                                         /\ IF (controllerStatus'[self] = NotFailed)
                                               THEN /\ switch2Controller' = Tail(switch2Controller)
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                    /\ UNCHANGED switch2Controller
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
                                                         controllerState, 
                                                         switchOrdering, IR2SW, 
                                                         controllerThreadPoolIRQueue, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         lastScheduledThread, 
                                                         SetScheduledIRs, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         idThreadWorkingOnIR, 
                                                         controllerDB, 
                                                         dependencyGraph, 
                                                         workerThreadRanking, 
                                                         switchLock, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, 
                                                         nextIR, nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, msg, 
                                                         controllerFailedModules >>

ControllerUpdateIR2(self) == /\ pc[self] = "ControllerUpdateIR2"
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ IF (controllerStatus[self] = NotFailed /\ controllerInternalFailedTimes[self[1]] < MAX_NUM_CONTROLLER_FAILURE)
                                   THEN /\ \/ /\ controllerStatus' = [controllerStatus EXCEPT ![self] = Failed]
                                              /\ controllerInternalFailedTimes' = [controllerInternalFailedTimes EXCEPT ![self[1]] = controllerInternalFailedTimes[self[1]] + 1]
                                           \/ /\ TRUE
                                              /\ UNCHANGED <<controllerInternalFailedTimes, controllerStatus>>
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << controllerInternalFailedTimes, 
                                                        controllerStatus >>
                             /\ IF (controllerStatus'[self] = NotFailed)
                                   THEN /\ FirstInstall' = [FirstInstall EXCEPT ![msg[self].IR] = 1]
                                        /\ IRStatus' = [IRStatus EXCEPT ![msg[self].IR] = IR_DONE]
                                        /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                        /\ UNCHANGED << IRStatus, FirstInstall >>
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
                                             SetScheduledIRs, ContProcSet, 
                                             SwProcSet, idThreadWorkingOnIR, 
                                             controllerDB, dependencyGraph, 
                                             workerThreadRanking, switchLock, 
                                             controllerLock, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, msg, 
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
                                     /\ Assert(controllerStatus[module] = Failed, 
                                               "Failure of assertion at line 1285, column 13.")
                                     /\ controllerLock' = module
                                     /\ controllerStatus' = [controllerStatus EXCEPT ![module] = NotFailed]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerWatchDogProc"]
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
                                                SetScheduledIRs, 
                                                controllerInternalFailedTimes, 
                                                ContProcSet, SwProcSet, 
                                                idThreadWorkingOnIR, 
                                                controllerDB, dependencyGraph, 
                                                workerThreadRanking, 
                                                switchLock, FirstInstall, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIR, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, monitoringEvent, 
                                                setIRsToReset, resetIR, msg >>

watchDog(self) == ControllerWatchDogProc(self)

Next == (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
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
           \/ (\E self \in ({c0} \X {WATCH_DOG}): watchDog(self))

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
        /\ \A self \in ({c0} \X {CONT_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({c0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({c0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({c0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in ({c0} \X {WATCH_DOG}) : WF_vars(watchDog(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-101c0216d6130b721738b3329fe062f3

\* Liveness Properties
AllInstalled == (\A x \in 1..MaxNumIRs: \E y \in DOMAIN installedIRs: installedIRs[y] = x)
AllDoneStatusController == (\A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE)
InstallationLivenessProp == <>[] (/\ AllInstalled 
                                  /\ AllDoneStatusController)
\* Safety Properties
IRCriticalSection == LET 
                        IRCriticalSet == {"ControllerThreadSendIR", "ControllerThreadForwardIR", "ControllerThreadSaveToDB2", "WaitForIRToHaveCorrectStatus", "ReScheduleifIRNone"}
                     IN   
                        \A x, y \in {c0} \X CONTROLLER_THREAD_POOL: \/ x = y
                                                                    \/ <<pc[x], pc[y]>> \notin IRCriticalSet \X IRCriticalSet
                                                                    \/ /\ <<pc[x], pc[y]>> \in IRCriticalSet \X IRCriticalSet
                                                                       /\ nextIRToSent[x] # nextIRToSent[y]

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
\* Last modified Sun Sep 20 17:35:08 UTC 2020 by root
\* Created Wed Sep 09 13:34:33 PDT 2020 by root

---------------------------- MODULE ScenarioIII ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
(***************************************************************************)
(***************************** Switch Model ********************************)
(* At the high level there are two models for the switch;                  *)
(*  - SWITCH_SIMPLE_MODEL: a single module that receives the IR, installs  *)
(*       the IR and sends back the ACK instantly (it does not fail)        *)
(*  - SWITCH_COMPLEX_MODEL: it consists of 4 modules;                      *)
(*          + NIC/ASIC                                                     *)
(*          + OFA                                                          *)
(*          + Installer                                                    *)
(*          + CPU                                                          *)
(*       each of these modules can fail independently                      *)
(***************************************************************************)
(***************************************************************************)
CONSTANTS SW,  \* set of switches
          SW_SIMPLE_MODEL, \* switch simple model thread identifier
          SW_COMPLEX_MODEL, \* switch complex model thread identifier
          WHICH_SWITCH_MODEL\*map from SW->{SW_SIMPLE_MODEL,SW_COMPLEX_MODEL}
          
(***************************************************************************)
(******************************** OFC Model ********************************)
(* At the high level OFC consists of 4 types of submodules;                *)
(*  + Worker Pool: a pool of worker processes responsible for preparing    *)
(*          and transmitting the instructions                              *)
(*  + Event Handler: responsible for handling events such as failure       *)
(*  + Monitoring Server: exchanges KEEP-ALIVE messages with switches and   *)
(*          takes care of received packets and also observed failures      *)
(*  + NIB Event handler:                                                   *)
(*       handle events from NIB                                            *)
(*  + Watchdog: in case of detecting failure in each of the above          *)
(*          processes, it restarts the process                             *)
(*       each of these modules execpt Watchdog can fail independently      *)
(***************************************************************************)
(***************************************************************************)
CONSTANTS ofc0 \* OFC thread identifiers

(***************************************************************************)
(******************************** RC Model *********************************)
(* At the high level RCS consists of 2 submodules;                         *)
(*  + Sequencer: it is responsible for sequencing the instructions given   *)
(*          the DAG as input                                               *)
(*  + Watchdog: same as Watchdog in OFC                                    *)
(*       each of these modules execpt Watchdog can fail independently      *)
(*  + NIB Event handler:                                                   *)
(*       handle events from NIB                                            *)
(***************************************************************************)
(***************************************************************************)
CONSTANTS rc0 \* RC thread identifiers
          
(***************************************************************************)
(************************ Switch Module identifiers ************************)
(***************************************************************************)
CONSTANTS NIC_ASIC_IN,
          NIC_ASIC_OUT,
          OFA_IN,
          OFA_OUT,
          INSTALLER, 
          SW_SIMPLE_ID

(***************************************************************************)
(************************ Ghost Process identifiers ************************)
(***************************************************************************)
\* these two process mimic the failure and recovery of switch
CONSTANTS SW_FAILURE_PROC,
          SW_RESOLVE_PROC,
          GHOST_UNLOCK_PROC
          
(***************************************************************************)
(**************************** RC    MODULES IDs ****************************)
(***************************************************************************)
CONSTANTS CONT_RC_NIB_EVENT
          \* id for event handler for NIB in OFC (type: model value) 
          
(***************************************************************************)
(*********************** CONTROLLER MODULES IDs ****************************)
(***************************************************************************)
CONSTANTS CONTROLLER_THREAD_POOL,
          \* set of worker threads (type: set of model values) 
          CONT_SEQ, 
          \* id for sequencer (type: model value)
          CONT_MONITOR,
          \* id for monitoring server (type: model value) 
          CONT_EVENT,
          \* id for event handler (type: model value)
          WATCH_DOG,
          \* id for watch dog (type: model value)
          CONT_OFC_NIB_EVENT
          \* id for event handler for NIB in OFC (type: model value)  

(***************************************************************************)
(*********************************** NIB model *****************************)
(* NIB contains only one moduel                                            *)
(*  + NIB event handler: used to hand read/write requests                  *)
(*                   from Apps (e.g. RC) and Orion core (e.g. OFC)         *)
(***************************************************************************)
CONSTANTS nib0

(***************************************************************************)
(*********************************** NIB tables ****************************)
CONSTANTS NIBT_CONTROLLER_STATE,
          NIBT_SET_SCHEDULED_IRS,
          NIBT_IR_QUEUE

(***************************************************************************)
(*********************** NIB MODULES IDs ****************************)
(***************************************************************************)
CONSTANTS CONT_NIB_OFC_EVENT,
          \* id for OFC event handler in NIB (type: model value) 
          CONT_NIB_RC_EVENT
          \* id for RC event handler in NIB (type: model value) 
          
          
(***************************************************************************)
(*********************** SW & IR state identifiers *************************)
(***************************************************************************)
CONSTANTS IR_NONE,
          IR_PENDING,
          IR_SENT,
          IR_RECONCILE,
          IR_DONE,
          SW_RUN,
          SW_SUSPEND,
          IR_UNLOCK
          
(***************************************************************************)
(*************************** Failure Status ********************************)
(***************************************************************************)
CONSTANTS NotFailed, 
          Failed           

(***************************************************************************)
(*********************** NIB notification semantics ************************)
(***************************************************************************)
\*CONSTANTS NIB_ADD,
\*          NIB_DELETE
                    
(***************************************************************************)
(*********************** Controller DB States ******************************)
(***************************************************************************)
\* for every control plane process an state is stored in the permanent DB
\* it helps to reconcile the state when internal failures happen           
CONSTANTS NO_STATUS, 
          STATUS_START_SCHEDULING, 
          STATUS_LOCKING, 
          STATUS_SENT_DONE,
          START_RESET_IR


(***************************************************************************)
(**************************** Tagged Buff **********************************)
(***************************************************************************)
CONSTANTS NO_TAG

        
(***************************************************************************)
(*********************** Message Types *************************************)
(***************************************************************************)
CONSTANTS INSTALL_FLOW,
          RECEIVED_SUCCESSFULLY, 
          INSTALLED_SUCCESSFULLY, 
          KEEP_ALIVE,
          RECONCILIATION_REQUEST, 
          RECONCILIATION_RESPONSE,
          STATUS_NONE 
\* {STATUS_NONE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY are the ones 
\* used to report to the controller on reconciliation request. (Currently not
\* in use)

(***************************************************************************)
(*********************** Status Msg Types **********************************)
(***************************************************************************)
CONSTANTS NIC_ASIC_DOWN, 
          OFA_DOWN, 
          INSTALLER_DOWN, 
          INSTALLER_UP
                         
(***************************************************************************)
(******************************** Others ***********************************)
(***************************************************************************)
CONSTANTS NO_LOCK
          
(***************************************************************************)
(**************************** INPUTS ***************************************)
(***************************************************************************)
\* these constants are only for checking if system works properly
\* should not implement these
CONSTANTS MAX_NUM_CONTROLLER_SUB_FAILURE, 
          MaxNumIRs,
          SW_FAIL_ORDERING


CONSTANTS SW_UP, SW_DOWN        
CONSTANTS NULL  
          
(* Assumption1: at most one instruction is associated with one switch *)
ASSUME Cardinality(SW) >= MaxNumIRs
(* Assumption3: MAX_NUM_CONTROLLER_SUB_FAILURE is a function from control plane *)
(* modules (e.g. OFC, RC) to maximum number of submodule failure each can face *)
ASSUME {"ofc0", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE
(* WHICH_SWITCH_MODEL should be a valid function with domain SW *)
ASSUME WHICH_SWITCH_MODEL \in [SW -> {SW_SIMPLE_MODEL, SW_COMPLEX_MODEL}]          

(*--fair algorithm stateConsistency
(************************* variables ***************************************)
    variables (*************** Some Auxiliary Vars ***********************)
              switchLock = <<NO_LOCK, NO_LOCK>>,
              controllerLock = <<NO_LOCK, NO_LOCK>>, 
              FirstInstall = [x \in 1..MaxNumIRs |-> 0],
              sw_fail_ordering_var = SW_FAIL_ORDERING,
              ContProcSet = (({rc0} \X {CONT_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) 
                            \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})),
              SwProcSet = (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) 
                            \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) 
                            \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) 
                            \cup (({SW_RESOLVE_PROC} \X SW)),
              (**************** Switch -- OFC Medium ***********************)
              \* For simplicity, instead of periodically exchanging KeepAlive
              \* messages between OFC's monitoring server and Switch's OFA,
              \* if switch changes its status (failure/recovery), it appends
              \* an status message to the swSeqChangedStatus variable and this
              \* is used by the OFC's event handler.  
              swSeqChangedStatus = <<>>,             
              
              \* controller2Switch used by OFC workers to send instructions
              \* to the switch
              controller2Switch = [x\in SW |-> <<>>],
              
              \* switch2controller used by switch to communicate with OFC
              \* (monitoring server)
              switch2Controller = <<>>,
              
              (******************** Switch Vars **************************)
              \* Initially all the modules are working properly
              switchStatus = [x\in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed, 
                              ofa |-> NotFailed, installer |-> NotFailed]],  
              
              \* installedIRs is an ordered set of all the IRs installed accross
              \* all the switches (used for checking consistency invariance
              installedIRs = <<>>,
              
              \* Buffers between different modules of the switch
              NicAsic2OfaBuff = [x \in SW |-> <<>>], 
              Ofa2NicAsicBuff = [x \in SW |-> <<>>],
              Installer2OfaBuff = [x \in SW |-> <<>>],
              Ofa2InstallerBuff = [x \in SW |-> <<>>],
              
              \* Caches in each switch (can be used for reconciliation
              \* OfaReceivedConfirmation = [x \in SW |-> <<>>],
              \* OfaCacheReceived = [x \in SW |-> {}],
              \* OfaCacheInstalled = [x \in SW |-> {}],
              
              \* TCAM 
              TCAM = [x \in SW |-> <<>>], 
              
              \* controlMsgCounter makes sure OFC receives statusMsg from each
              \* switch in the same order as they happened
              controlMsgCounter = [x \in SW |-> 0],
              
              (*********************** Controller *************************)
              controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0],
              controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed],
              
              (*********************** RC Vars ****************************)
              \**************** Dependency Graph Definition ***********
              \* DAG is normally an input to the sequencer, however, here
              \* we check for all the possible non-isomorphic DAGs to make
              \* sure it works for all combinations
              switchOrdering = CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z],
              \* dependencyGraph \in PlausibleDependencySet,
              dependencyGraph \in generateConnectedDAG(1..MaxNumIRs),              
              IR2SW = CHOOSE x \in [1..MaxNumIRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z 
                                                                                /\ switchOrdering[x[y]] =< switchOrdering[x[z]],
              
              (********************** OFC Vars ****************************)
              \************** Workers ********************
              \* idThreadWorkingOnIR is a logical semaphore used for 
              \* synchronization between IRs
              idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK],
              \* WorkerThreadRanking is an auxiliary variable used for 
              \* reducing the number of possible behaviours by applying
              \* the following rule; if two workers try to get the lock 
              \* for an IR, the one with lower ranking always gets it. 
              workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
              
              (********************* NIB Vars *****************************)
              (********************* Message format ***********************)
              (********************* NIB transactions *********************)
              (* <<[op |-> Read, key|-> IR, value|-> IR_DONE],  []>>      *)
              (************************************************************)
              \************** Message queues ****************
              \* used by OFC (NIB) to receive (send) messages
              NIB2OFC = <<>>,
              \* used by RC (NIB) to receive (send) messages
              NIB2RC = <<>>,
              \* used by NIB (OFC) to receive (send) messages
              OFC2NIB = <<>>,
              \* used by NIB (RC) to receive (send) messages
              RC2NIB = <<>>,
           
              \********************** Tables *************************************
              masterState = [ofc0 |-> "primary", rc0 |-> "primary"],
              controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]],
              IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
              SwSuspensionStatus = [x \in SW |-> SW_RUN],
              IRQueueNIB = <<>>,
              \* notificationNIB = [y \in {c0, c1} |-> [RCS |-> [IRQueueNIB |-> <<>>]]], 
              SetScheduledIRs = [y \in SW |-> {}] 
              \* @Pooria, consider moving this variable to RC
              
    define
        (********************* Auxiliary functions **********************)
        max(set) == CHOOSE x \in set: \A y \in set: x \geq y
        min(set) == CHOOSE x \in set: \A y \in set: x \leq y 
        rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
         
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
        (******************** Graph Auxiliary functions ******************)
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

                                        
        PlausibleDependencySet == UNION {GeneralSetSetUnion({generateConnectedDAG(((sum(allSizes, y-1) + 1)..(sum(allSizes, y)))): 
                                                                                        y \in 1..(Len(allSizes) - 1)}): 
                                                                                             allSizes \in AllPossibleSizes(MaxNumIRs, MaxNumIRs)} 
                
        (****************** Used by system logic *****************************)
        
        (***************************** Switch ********************************)                                  
        whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID] 
        \***************************** NIC/ASIC ******************************
        swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed 
        
        \***************************** OFA **********************************
        swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                                  /\ switchStatus[sw].ofa = NotFailed
        \**************************** Installer *****************************
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
                               
        \*************************** switch failure process *****************
        returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}
        \* getSetIRsForSwitch is for verification optimization reasons
        getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: IR2SW[x] = SID}
        
        \************************** switch failure recovery *****************
        returnSwitchFailedElements(sw) == {x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                                                          /\ \/ switchStatus[sw].cpu = NotFailed
                                                                             \/ x \notin {"ofa", "installer"}}
        installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerProc" 
        ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaProcIn"
                                 /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaProcOut"
        nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchRcvPacket"
                                     /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchFromOFAPacket"
        getInstallerStatus(stat) == IF stat = NotFailed 
                                    THEN INSTALLER_UP
                                    ELSE INSTALLER_DOWN                 
                                                      
        (************************* Controller ********************************)                              
        moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
        controllerIsMaster(controllerID) == CASE controllerID = rc0 -> masterState.rc0 = "primary"
                                              [] controllerID = ofc0 -> masterState.ofc0 = "primary"
        getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                                     [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0 
        (****************************** NIB **********************************)
        \* The following four expression help using tagged buffer in NIB
        \* Please see modifiedRead, modifiedWrite, modifiedRemove
        NoEntryTaggedWith(threadID) == ~\E x \in rangeSeq(IRQueueNIB): x.tag = threadID 
        FirstUntaggedEntry(threadID, num) == ~\E x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = NO_TAG
                                                                          /\ x < num
        getFirstIRIndexToRead(threadID) == CHOOSE x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                                           \/ /\ NoEntryTaggedWith(threadID)
                                                                              /\ FirstUntaggedEntry(threadID, x)
                                                                              /\ IRQueueNIB[x].tag = NO_TAG
        getFirstIndexWith(RID, threadID) == CHOOSE x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = threadID
                                                                            /\ IRQueueNIB[x].IR = RID
                                                                   
        (****************** RC (routing controller) **************************)
        \*************************** Sequencer *******************************
        isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                             /\ IRStatus[y] # IR_DONE
        getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                                  /\ isDependencySatisfied(x)
                                                                  /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRs[IR2SW[x]]}
                                                                  \*/\ idThreadWorkingOnIR[x] = IR_UNLOCK}
                                                                  
        (****************** OFC (openflow controller) ************************)
        \*************************** Workers *********************************
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        \* following four expressions used for verification optimization reasons
        \* between all the threads attempting to get the IR, the one with lowest 
        \* id always gets it. 
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
        
        \*************************** EventHandler ****************************       
        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                        /\ swSeqChangedStatus[x].num > monEvent.num
        shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                                     \/ monEvent.type = NIC_ASIC_DOWN
                                     \/ /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.status.installerStatus = INSTALLER_DOWN
        canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                           /\ monEvent.status.installerStatus = INSTALLER_UP
        
                                                               
        \* getIRSetToReconcile(SID) == {x \in 1..MaxNumIRs: /\ IR2SW[x] = SID
        \*                                                 /\ IRStatus[x] \notin {IR_DONE, IR_NONE, IR_SUSPEND}}
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ IR2SW[x] = SID
                                                     /\ IRStatus[x] \notin {IR_DONE, IR_NONE}}
        \* getIRSetToSuspend(CID, SID) == {x \in SetScheduledIRs[SID]: IRStatus[x] = IR_NONE}           
                                                                             
        \*************************** Monitoring Server **********************
        
        \*************************** Watchdog *******************************
        returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                                   /\ controllerSubmoduleFailStat[x] = Failed}
                                                                                                                                                                          
        (***************** SystemWide Check **********************************)        
        isFinished == \A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE
                                                                                                                
    end define
    
    (*******************************************************************)
    (*                       Utils (Macros)                            *)
    (*******************************************************************)
    macro removeFromSeqSet(SeqSet, obj)
    begin
        assert obj \in Head(SeqSet);
        if Cardinality(Head(SeqSet)) = 1 then
            SeqSet := Tail(SeqSet)
        else
            SeqSet := <<(Head(SeqSet)\{obj})>> \o Tail(SeqSet);
        end if; 
    end macro
    
    (*******************************************************************)
    (*                     Switches (Macros)                           *)
    (*******************************************************************)
    
    \* ======= NIC/ASIC Failure ========
    macro nicAsicFailure()
    begin
        \* when NIC/ASIC fails, we should;
        \* 1. change the status of NIC/ASIC to failed
        \* 2. discard all the packets in controller2switch medium
        \* 3. send a statusMsg to the event handler 
        assert switchStatus[self[2]].nicAsic = NotFailed;
        switchStatus[self[2]].nicAsic := Failed;
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
        \* when NIC/ASIC recovers, we should
        \* 1. Wait for the NIC/ASIC processes to be in their starting mode
        \* 2. Change the status of NIC/ASIC to not failed
        \* 3. send a status resolve message to the event handler
        \*      3.0. if OFA and installer are OK, switch should send
        \*                  a KEEP_ALIVE message with INSTALLER_UP
        \*      3.1. if OFA is in failure mode, switch should send
        \*                  a OFA_DOWN message.
        \*      3.2. if OFA is OK but installer is in failure mode, switch
        \*                  should send a KEEP_ALIVE message with INSTALLER_DOWN
        
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
        \* when CPU fails;
        \* 1. Change CPU, OFA, Installer status to failed
        \* 2. Clear all the buffers
        \* 3. If NIC/ASIC is OK, SW sends a OFA_DOWN message to the 
        \*          event handler. 
        assert switchStatus[self[2]].cpu = NotFailed;
        switchStatus[self[2]].cpu := Failed || switchStatus[self[2]].ofa := Failed || switchStatus[self[2]].installer := Failed;
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
        \* when CPU recovers;
        \* 1. Wait for OFA and Installer to be in their starting status
        \* 2. Change the status of CPU, OFA, Installer to not failed
        \* 3. Clear all the buffers to make sure nothing remains there
        \* 4. If NIC/ASIC is ok, SW can exchange KEEP_ALIVE messages with OFC
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
        \* When OFA fails;
        \* 1. Change the status of OFA to failed
        \* 2. If NIC/ASIC is OK, SW sends a OFA_DOWN message to event handler
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed;
        switchStatus[self[2]].ofa := Failed;       
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
        \* When OFA recovers;
        \* 1. Wait for OFA to be in its starting state
        \* 2. Change status of OFA to not failed
        \* 3. If NIC/ASIC is OK, OFA can exchange KEEP_ALIVE messages with OFC
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
        \* When Installer fails
        \* 1. Change the status of Installer to failed
        \* 2. IF OFA and NIC/ASIC are OK, SW exchanges KEEP_ALIVE messages with INSTALLER_DOWN status
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed;
        switchStatus[self[2]].installer := Failed;  
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
        \* When Installer recovers;
        \* 1. Wait for Installer to be in its starting mode
        \* 2. Change status of installer to not failed
        \* 3. if NIC/ASIC and OFA are OK, SW exchanges KEEP_ALIVE messages with INSTALLER_UP status
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
    
    (*******************************************************************)
    (*                     LOCK System (Macros)                        *)
    (*******************************************************************)
    \* Lock system is used to reduce the unnecessary interleavings and
    \* hence reduce the verification runtime. 
    \* at each time, only the module who owns the Lock can proceed
    
    \* ===========Wait for Lock==========
    macro switchWaitForLock()
    begin
        \* switch can only proceed if
        \* 1. controller does not own the Lock
        \* 2. either no other switch has the Lock or it self has the lock        
        await controllerLock = <<NO_LOCK, NO_LOCK>>; 
        await switchLock \in {<<NO_LOCK, NO_LOCK>>, self};
    end macro;
    \* =================================
    
    \* ===========Acquire Lock==========
    macro acquireLock()
    begin
        \* switch acquires the lock if switchWaitForLock conditions are 
        \* satisfied
        switchWaitForLock();
        switchLock := self;
    end macro;
    \* =================================
    
    
    \* ====== Acquire & Change Lock =====
    macro acquireAndChangeLock(nextLockHolder)
    begin
        \* Using this macro, processes can pass lock to another process        
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
    macro controllerWaitForLockFree()
    begin
        \* controller only proceeds when the following two conditions 
        \* are satified;
        await controllerLock = <<NO_LOCK, NO_LOCK>>;
        await switchLock = <<NO_LOCK, NO_LOCK>>;
    end macro
    \* =================================
    
    \* ========= controller release Lock ==========
    macro controllerReleaseLock(prevLockHolder)
    begin
        \* only the controller process itself can release the controller lock. 
        await \/ controllerLock = prevLockHolder
              \/ controllerLock = <<NO_LOCK, NO_LOCK>>;
        await switchLock = <<NO_LOCK, NO_LOCK>>;
        controllerLock := <<NO_LOCK, NO_LOCK>>;
    end macro
    \* =================================    
                  
    (*******************************************************************)
    (*                     Controller (Macros)                         *)
    (*******************************************************************)
        
    \* macro failover()
    \* begin
    \*    if (self = c0 /\ masterState.c0 = "primary")
    \*    then
    \*        either
    \*            masterState.c0 := "failed" || masterState.c1 := "primary";
    \*            goto EndCont;
    \*        or
    \*            skip;
    \*        end either;
    \*    end if; 
    \*end macro;
    
    
    \* === Controller Module Failure ===
    macro controllerModuleFails()
    begin
        \* When a controller submodule fails,
        \* 1. change its status to failed
        controllerSubmoduleFailStat[self] := Failed;
        controllerSubmoduleFailNum[self[1]] := controllerSubmoduleFailNum[self[1]] + 1;
    end macro;
    \* =================================
    
    \* == Controller Module FailOrNot ==
    macro controllerModuleFailOrNot()
    begin
        \* this macros should be used in every atomic step of the controller
        \* if the controller module is not failed and the number of internal failures
        \* have not exceeded the maximum possible size;
        \* We create two branches (one in which module fails and one in which it does not) 
        if (controllerSubmoduleFailStat[self] = NotFailed /\ 
                    controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])) then           
            either
                controllerModuleFails();
            or
                skip;
            end either;
        end if;
    end macro;
    \* =================================
    
    \* == failure inside one atomic ====
    macro whichStepToFail(numSteps)
    begin
        \* For optimization reasons, some steps of each module are grouped into
        \* one atomic action (the ones who does not affect the other modules).
        \* The module, however, can fail between any of these steps.
        \* This function creates all the possible branches each of which explore
        \* a different failure scenario. 
        \* 0 means there is no failure
        if (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1])) then
            with num \in 0..numSteps do
                stepOfFailure := num;
            end with;
        else
            stepOfFailure := 0;
        end if;
    end macro;
    \* =================================
    
    \* ===== Sending the entry =========
    macro controllerSendIR(s)
    begin
        \* this macro mimics all the sending function;
        \* 1. append the message to the OpenFlow channel between controller and switch
        \* 2. give the lock of the system to the switch. 
        controller2Switch[IR2SW[s]] := Append(controller2Switch[IR2SW[s]], [type |-> INSTALL_FLOW,
                                                                            to |-> IR2SW[s],
                                                                            IR |-> s]);
        if whichSwitchModel(IR2SW[s]) = SW_COMPLEX_MODEL then 
            switchLock := <<NIC_ASIC_IN, IR2SW[s]>>;
        else
            switchLock := <<SW_SIMPLE_ID, IR2SW[s]>>;
        end if;
    end macro;
    \* =================================
    
    
                  
    (*******************************************************************)
    (*                     NIB   (Macros)                              *)
    (*******************************************************************)
    \* ========= Tagged Buffer ==========
    macro modifiedEnqueue()
    begin
        IRQueueNIB := Append(IRQueueNIB, [IR |-> nextIR, tag |-> NO_TAG]);
    end macro;
    
    macro modifiedRead()
    begin
        rowIndex := getFirstIRIndexToRead(self);
        nextIRToSent := IRQueueNIB[rowIndex].IR;
        IRQueueNIB[rowIndex].tag := self;
    end macro;
    
    macro prepareIRTransaction()
    begin
        assert nextTrans.ops[1].table = NIBT_CONTROLLER_STATE;
        controllerStateNIB[nextTrans.ops[1].key] := nextTrans.ops[1].value;
        assert nextTrans.ops[2].table = NIBT_SET_SCHEDULED_IRS;
        SetScheduledIRs[nextTrans.ops[2].key] := nextTrans.ops[2].value;
    end macro;
    
    macro scheduleIRTransaction()
    begin
        assert nextTrans.ops[1].table = NIBT_IR_QUEUE;
        IRQueueNIB := Append(IRQueueNIB, nextTrans.ops[1].value);
        assert nextTrans.ops[2].table = NIBT_CONTROLLER_STATE;
        controllerStateNIB[nextTrans.ops[2].key] := nextTrans.ops[2].value;
    end macro;
    
    
    macro modifiedRemove()
    begin
        rowRemove := getFirstIndexWith(nextIRToSent, self);
        IRQueueNIB := removeFromSeq(IRQueueNIB, rowRemove);
        \*notificationNIB[self[1]].RCS.IRQueueNIB := Append(notificationNIB[self[1]].RCS.IRQueueNIB, 
        \*                                                    [type |-> NIB_DELETE, IR |-> nextIRToSent]);
    end macro;
    \* =================================
    
    
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
    
    (*******************************************************************)
    (*                     Switches SIMPLE Model                       *)
    (*******************************************************************)
    \* This is the simplest switch model that does all the following
    \* in one atomic operation
    \* 1. unpack the received packet
    \* 2. install the IR
    \* 3. send the confirmation to OFC
    fair process swProcess \in ({SW_SIMPLE_ID} \X SW)
    variables ingressPkt = [type |-> 0]
    begin
    SwitchSimpleProcess:
    while TRUE do
        await whichSwitchModel(self[2]) = SW_SIMPLE_MODEL;          
        await Len(controller2Switch[self[2]]) > 0;
        switchWaitForLock();
        ingressPkt := Head(controller2Switch[self[2]]);
        assert ingressPkt.type = INSTALL_FLOW;
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        installedIRs := Append(installedIRs, ingressPkt.IR);
        TCAM[self[2]] := Append(TCAM[self[2]], ingressPkt.IR);
        switch2Controller := Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                        from |-> self[2],
                                                        IR |-> ingressPkt.IR]);
        releaseLock(self);
    end while;
    end process;
    
    (*******************************************************************)
    (*                     Switches COMPLEX (Modules)                  *)
    (*******************************************************************)
    \* the switch complex model (each element can fail and recover independantly)
    
    \* ======== NIC/ASIC Module ========
    \* NIC/ASIC module consists of two processes; NIC/ASIC Downstream, Nic/Asic Upstream
    \* NIC/ASIC Downstream receives the packets from controller and other switches.
    \* NIC/ASIC Upstream sends the packets to controller and other switches
    
    fair process swNicAsicProcPacketIn \in ({NIC_ASIC_IN} \X SW)
    variables ingressIR = [type |-> 0]
    begin
    SwitchRcvPacket:
    while TRUE do
    
        \* Step 1: Pick the first packet from input buffer
        await whichSwitchModel(self[2]) = SW_COMPLEX_MODEL;
        await swCanReceivePackets(self[2]);
        await Len(controller2Switch[self[2]]) > 0;
        ingressIR := Head(controller2Switch[self[2]]);
        assert \/ ingressIR.type = RECONCILIATION_REQUEST
               \/ ingressIR.type = INSTALL_FLOW;
        acquireLock();
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        
        \* Step2: if it is a flow installation packet, append it to the OFA input buffer
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
    
        \* Step 1: Pick the first packet from Ofa to NIC/ASIC buffer 
        await swCanReceivePackets(self[2]);
        await  Len(Ofa2NicAsicBuff[self[2]]) > 0;
        egressMsg := Head(Ofa2NicAsicBuff[self[2]]);
        acquireLock();
        assert \/ egressMsg.type = INSTALLED_SUCCESSFULLY
               \/ egressMsg.type = RECEIVED_SUCCESSFULLY
               \/ egressMsg.type = RECONCILIATION_RESPONSE;
        Ofa2NicAsicBuff[self[2]] := Tail(Ofa2NicAsicBuff[self[2]]);
        
        \* Step 2: send the packet to the destination (controller)
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
    \* OFA consists of two processes; OFA Downstream, OFA Upstream
    \* OFA Downstream extracts the IR and sends it to the Installer
    \* OFA Upstream upon receiving the confirmation from Installer
    \* prepares a INSTALLATION_CONFIRMATION message and sends it to
    \* the controller
    
    fair process ofaModuleProcPacketIn \in ({OFA_IN} \X SW)
    variables ofaInMsg = [type |-> 0]
    begin
    SwitchOfaProcIn: 
    while TRUE do
        
        \* Step 1: Pick the first packet from buffer, process and extract the IR
        await swOFACanProcessIRs(self[2]);
        await Len(NicAsic2OfaBuff[self[2]]) > 0;
        acquireLock();
        ofaInMsg := Head(NicAsic2OfaBuff[self[2]]);           
        assert ofaInMsg.to = self[2];
        assert ofaInMsg.IR  \in 1..MaxNumIRs;
        NicAsic2OfaBuff[self[2]] := Tail(NicAsic2OfaBuff[self[2]]);
        
        \* Step 2: append the IR to the installer buffer
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
    
        \* Step 1: pick the first confirmation from installer
        await swOFACanProcessIRs(self[2]);
        await Installer2OfaBuff[self[2]] # <<>>;
        acquireLock();
        ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
        Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
        assert ofaOutConfirmation \in 1..MaxNumIRs;
        
        \* Step 2: prepare an installation confirmation message and send it to the controller
        \* through the NIC/ASIC
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
    \* installer only has one process that installs the IR and sends back the feedback to the OFC
    fair process installerModuleProc \in ({INSTALLER} \X SW)
    variables installerInIR = 0
    begin
    SwitchInstallerProc: 
    while TRUE do
       
       \* Step 1: pick the first instruction from the input buffer      
       await swCanInstallIRs(self[2]);
       await Len(Ofa2InstallerBuff[self[2]]) > 0;
       acquireLock();
       installerInIR := Head(Ofa2InstallerBuff[self[2]]);
       assert installerInIR \in 1..MaxNumIRs;
       Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);
       
       \* Step 2: install the IR to the TCAM
       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then
                acquireLock();   
                installedIRs := Append(installedIRs, installerInIR);
                TCAM[self[2]] := Append(TCAM[self[2]], installerInIR);
            else
                installerInIR := 0;
                goto SwitchInstallerProc;
            end if;
            
       \* Step 3: send the confirmation to the OFA
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
        \* retrieves all the possible elements to fail and creates a branch in each of which
        \* one the modules fail 
        notFailedSet := returnSwitchElementsNotFailed(self[2]);
        
        \* proceed only if 
        \* I. there is an element to fail
        \* II. the system has not finished installing all the IRs
        \* III. either lock is for its switch or no one has the lock
        \* IV. there is no difference if switch fails after the corresponding IR is in IR_DONE mode
        \* V. switches fail according to the order of sw_fail_ordering_var (input), so
        \*    this switch should be at the head of failure ordering sequence.  
        await notFailedSet # {};
        await ~isFinished;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                 \/ switchLock[2] = self[2];
        await \E x \in getSetIRsForSwitch(self[2]): IRStatus[x] # IR_DONE;
        await sw_fail_ordering_var # <<>>;
        await self[2] \in Head(sw_fail_ordering_var);
        removeFromSeqSet(sw_fail_ordering_var, self[2]);
        
        \* for each element that can possibly fail create a new branch.
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
        
\*        releaseLock(self);
    end while
    end process
    \* =================================
    
    \* ==== Failure Resolve Process ====
    fair process swResolveFailure \in ({SW_RESOLVE_PROC} \X SW)
    variable failedSet = {}, statusResolveMsg = <<>>, recoveredElem = "";
    begin
    SwitchResolveFailure:
    while TRUE do
        \* retrieves all the failed elements and create a branch in each of which
        \* a seperate element recovers
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
    \* this process makes sure deadlock does not happend
    \* and switch releases the lock even if it has been failed
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
    
    (*******************************************************************)
    (*                     RC (Route Controller)                       *)
    (*******************************************************************)
   
    \* ============ Old Sequencer ==========
    \* Sequencer periodically gets all the valid IRs (those with satisfied
    \* dependencies), run its scheduling mechanism to decide the order of
    \* scheduling and then, schedule the IR
\*    fair process controllerSequencer \in ({rc0} \X {CONT_SEQ})
\*    variables toBeScheduledIRs = {}, nextIR = 0, stepOfFailure = 0;
\*    begin
\*    ControllerSeqProc:
\*    while TRUE do
\*        
\*        \* ControlSeqProc consists of one operation;
\*        \* 1) Retrieving the set of valid IRs
\*        await controllerIsMaster(self[1]);
\*        await moduleIsUp(self);
\*        controllerWaitForLockFree();
\*        toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1]);
\*        await toBeScheduledIRs # {};
\*        
\*        \* SchedulerMechanism consists of three operations; 
\*        \* 1) choosing one IR from the set of valid IRs
\*        \* 2) updating the state of DB to start scheduling
\*        \* 3) add the IR to the scheduled Set (acts as a buffer 
\*        \*      for sequencer to make sure it does not unnecessarily
\*        \*      reschedules any IR) 
\*        \* (sequencer may fail between these Ops)
\*        SchedulerMechanism:
\*        while TRUE do \* while toBeScheduledIRs # {} do
\*            controllerWaitForLockFree();
\*            whichStepToFail(3);
\*            if (stepOfFailure # 1) then
\*                \* Step 1: choosing one IR from the valid set
\*                nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
\*                if (stepOfFailure # 2) then
\*                    \* Step 2: updating state on NIB
\*                    controllerStateNIB[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
\*                    if (stepOfFailure # 3) then  
\*                        \* Step 3: adding to scheduled set
\*                        SetScheduledIRs[IR2SW[nextIR]] := SetScheduledIRs[IR2SW[nextIR]] \cup {nextIR};                    
\*                    end if;
\*                end if;
\*            end if;
\*            
\*            if (stepOfFailure # 0) then    
\*                controllerModuleFails();
\*                goto ControllerSeqStateReconciliation; 
\*            end if;        
\*                
\*            \* ScheduleTheIR consists of two operations; 
\*            \* 1) Enqueueing the IR to the shared Queue
\*            \* 2) Clearing the state on DB 
\*            \* Sequencer may fail between these two Ops. 
\*            ScheduleTheIR: 
\*                controllerWaitForLockFree();
\*                whichStepToFail(2);
\*                if (stepOfFailure # 1) then
\*                    \* step 1: enqueue the IR 
\*                    modifiedEnqueue();
\*                    toBeScheduledIRs := toBeScheduledIRs\{nextIR};
\*                    if (stepOfFailure # 2) then
\*                        \* step 2: clear the state on NIB  
\*                        controllerStateNIB[self] := [type |-> NO_STATUS];    
\*                    end if;
\*                end if;
\*                
\*                if (stepOfFailure # 0) then    
\*                  controllerModuleFails();
\*                  goto ControllerSeqStateReconciliation; 
\*                elsif toBeScheduledIRs = {} then \* where while ends *\
\*                  goto ControllerSeqProc;
\*                end if;  
\*        end while;                                                
\*    end while;
\*    
\*    ControllerSeqStateReconciliation:
\*        \* After that the sequencer failed and the watchdog has restarted it.
\*        \* Sequencer starts by calling the reconciliation function in which
\*        \* it undoes some of the operations
\*        
\*        \* If the state of sequencer before failure is STATUS_START_SCHEDULING,
\*        \* there is no evidence whether the sequencer has scheduled the IR or not,
\*        \* therefore, it has to remove the IR from the Scheduled Set, so that 
\*        \* it would reschedule the IR in the next round.
\*        \* This may lead to redundant rescheduling. However, the workers in OFC
\*        \* handle the redundant rescheduling scenario.   
\*        await controllerIsMaster(self[1]);
\*        await moduleIsUp(self);
\*        controllerReleaseLock(self);
\*        if(controllerStateNIB[self].type = STATUS_START_SCHEDULING) then
\*            SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] := 
\*                        SetScheduledIRs[IR2SW[controllerStateNIB[self].next]]\{controllerStateNIB[self].next};
\*        end if;
\*        goto ControllerSeqProc;
\*    end process
\*    \* ========================== 
    
    
    \* ============ Sequencer ==========
    \* Sequencer periodically gets all the valid IRs (those with satisfied
    \* dependencies), run its scheduling mechanism to decide the order of
    \* scheduling and then, schedule the IR
    fair process controllerSequencer \in ({rc0} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}, key = "", op1 = [table |-> ""], op2 = [table |-> ""], transaction = <<>>, nextIR = 0, stepOfFailure = 0;
    begin
    ControllerSeqProc:
    while TRUE do
        
        \* ControlSeqProc consists of one operation;
        \* 1) Retrieving the set of valid IRs
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        controllerWaitForLockFree();
        toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1]);
        await toBeScheduledIRs # {};
        
        \* SchedulerMechanism consists of three operations; 
        \* 1) choosing one IR from the set of valid IRs
        \* 2) updating the state of DB to start scheduling
        \* 3) add the IR to the scheduled Set (acts as a buffer 
        \*      for sequencer to make sure it does not unnecessarily
        \*      reschedules any IR) 
        \* (sequencer may fail between these Ops)
        SchedulerMechanism:
        while TRUE do \* while toBeScheduledIRs # {} do
            controllerWaitForLockFree();
            whichStepToFail(2);
            if (stepOfFailure # 1) then
                \* Step 1: choosing one IR from the valid set
                nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                if (stepOfFailure # 2) then
                    \* Step 2: updating state on NIB
\*                    RCUpdateControllerStateNIB:    
                    op1 := [table |-> NIBT_CONTROLLER_STATE, key |-> self, value |-> [type |-> STATUS_START_SCHEDULING, next |-> nextIR]];
                    op2 := [table |-> NIBT_SET_SCHEDULED_IRS, key |-> IR2SW[nextIR], value |-> SetScheduledIRs[IR2SW[nextIR]] \cup {nextIR}];
                    transaction := [name |-> "PrepareIR", ops |-> <<op1, op2>>];
                    RC2NIB := RC2NIB \o <<transaction>>;
                end if;
            end if;
            
            RCModuleFail:
            if (stepOfFailure # 0) then    
                controllerModuleFails();
                goto ControllerSeqStateReconciliation; 
            end if;        
                
            \* ScheduleTheIR consists of two operations; 
            \* 1) Enqueueing the IR to the shared Queue
            \* 2) Clearing the state on DB 
            \* Sequencer may fail between these two Ops. 
            ScheduleTheIR: 
                controllerWaitForLockFree();
                whichStepToFail(2);
                if (stepOfFailure # 1) then
                    \* step 1: enqueue the IR 
                    toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                    if (stepOfFailure # 2) then
                        \* step 2: clear the state on NIB  
\*                        controllerStateNIB[self] := [type |-> NO_STATUS]; 
                        op1 := [table |-> NIBT_IR_QUEUE, key |-> NULL, value |-> [IR |-> nextIR, tag |-> NO_TAG]];
                        op2 := [table |-> NIBT_CONTROLLER_STATE, key |-> self, value |-> [type |-> NO_STATUS]];   
                        transaction := [name |-> "ScheduleIR", ops |-> <<op1, op2>>];
                        RC2NIB := RC2NIB \o <<transaction>>;
                    end if;
                end if;
                
                RCModuleFailAfterSendIR:
                if (stepOfFailure # 0) then    
                  controllerModuleFails();
                  goto ControllerSeqStateReconciliation; 
                elsif toBeScheduledIRs = {} then \* where while ends *\
                  goto ControllerSeqProc;
                end if;  
        end while;                                                
    end while;
    
    ControllerSeqStateReconciliation:
        \* After that the sequencer failed and the watchdog has restarted it.
        \* Sequencer starts by calling the reconciliation function in which
        \* it undoes some of the operations
        
        \* If the state of sequencer before failure is STATUS_START_SCHEDULING,
        \* there is no evidence whether the sequencer has scheduled the IR or not,
        \* therefore, it has to remove the IR from the Scheduled Set, so that 
        \* it would reschedule the IR in the next round.
        \* This may lead to redundant rescheduling. However, the workers in OFC
        \* handle the redundant rescheduling scenario.   
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        controllerReleaseLock(self);
        if(controllerStateNIB[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[IR2SW[controllerStateNIB[self].next]] := 
                        SetScheduledIRs[IR2SW[controllerStateNIB[self].next]]\{controllerStateNIB[self].next};
        end if;
        goto ControllerSeqProc;
    end process
    
    
    
    (*******************************************************************)
    (********************** Network Information Base *******************)
    (*******************************************************************)
    \* ============ NIB event handler for RC ==========
    fair process NIBRCEventHandler \in ({nib0} \X {CONT_NIB_RC_EVENT})
    variables nextTrans = [type |-> 0];
    begin
    NIBRCEventHandling:
    while TRUE do
        await RC2NIB # <<>>;
        nextTrans := Head(RC2NIB);
        \* transaction processing
        if (nextTrans.name = "PrepareIR") then \* submitted by the Sequencer in RC 
            prepareIRTransaction();
        elsif (nextTrans.name = "ScheduleIR") then \* submitted by the Sequencer in RC 
            scheduleIRTransaction();
        end if;
        RC2NIB := Tail(RC2NIB);
    end while;
    end process
    
    (*******************************************************************)
    (*                     OFC (OpenFlow Controller)                   *)
    (*******************************************************************)
    \* ====== Worker Pool ======= 
    \* Workers 
    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = 0, rowIndex = -1, rowRemove = -1, stepOfFailure = 0; 
    begin
    ControllerThread:
    while TRUE do
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await IRQueueNIB # <<>>;
        await canWorkerThreadContinue(self[1], self);
        controllerWaitForLockFree();
        \* Controller thread consists of 3 Ops: 
        \* 1. modified read from IRQueue in the NIB (which gives the 
        \*    next IR to install)
        \* 2. update the state of db to locking mode
        \* 3. try to lock the IR to avoid two workers working on the same IR
        \*      (Note that sequence may fail in the middle of scheduling and
        \*       may reschedule the IR wrongly)
        \* (worker may fail between these Ops)
        
        \* Step 1. modified read
        modifiedRead();
        
        whichStepToFail(2);
        if (stepOfFailure = 1) then
            \* Failed before Step 1
            controllerModuleFails();
            goto ControllerThreadStateReconciliation;
        else 
            \* Step 2: Worker Thread save state to NIB
            controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent];
            if (stepOfFailure = 2) then
                \* Failed before Step 2
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            else    
                \* Step 3: try to lock the IR and if it's already lock do ControllerThreadRemoveQueue1 Operation.
                \***** Step 3.1: lock the semaphore using CAS operation 
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
        
        \* ControllerThreadSendIR consist of 1 operation;
        \* 1. Check the necessary conditions on switch status and IR status,
        \*      then, change IR_STATUS to IR_SENT (Update-before-Action)
        ControllerThreadSendIR:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                \* Step 1: checks if the switch is not suspended and instruction is in its initial mode
                if ~isSwitchSuspended(IR2SW[nextIRToSent]) /\ IRStatus[nextIRToSent] = IR_NONE then
                    \**** Step 1.1: change the status of the switch to IR_SENT before actually sending
                    \**** the IR (Update-before-Action) 
                    IRStatus[nextIRToSent] := IR_SENT;
                    
                    \* ControllerThreadForwardIR consists of 2 operations;
                    \* 1. Forwarding the IR to the switch
                    \* 2. Updating the state on db to SENT_DONE
                    \* Worker may fail between these operations
                    ControllerThreadForwardIR:
                        controllerWaitForLockFree();
                        whichStepToFail(2);
                        if (stepOfFailure # 1) then
                            \* Step 1: forward the IR
                            controllerSendIR(nextIRToSent);
                            if (stepOfFailure # 2) then
                               \* Step 2: save the state on NIB
                               controllerStateNIB[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRToSent];
                            end if;
                        end if;                          
                        if (stepOfFailure # 0) then
                            controllerModuleFails();
                            goto ControllerThreadStateReconciliation;
                        end if;
                end if;
            else
                \* Failed even before begining of this operation
                goto ControllerThreadStateReconciliation;
            end if;
        
        \* Operations in the next two labels are for performance reasons
        \* since we have already dedicated this worker to a IR, if the switch
        \* is in suspended mode, worker waits for it to be recovered and then, 
        \* does the fast recovery by immediately starting to send the IR
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
            
        \* Simply unlock the IR which was locked at the begining
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
            
        \* RemoveFromScheduledIRSet consists of three operations;
        \* 1. Remove the IR from the scheduled set since worker is done with it. 
        \* 2. Clear the state on db
        \* 3. Remove the IR from the tagged buffer in NIB (Lazy removel strategy) 
        \* Worker may fail between any of these Ops
        RemoveFromScheduledIRSet:
            controllerWaitForLockFree();
            whichStepToFail(3);
            if (stepOfFailure # 1) then 
                \* Step 1: Remove from scheduled set
                \* assert nextIRToSent \in SetScheduledIRs[IR2SW[nextIRToSent]];
                SetScheduledIRs[IR2SW[nextIRToSent]] := SetScheduledIRs[IR2SW[nextIRToSent]]\{nextIRToSent};
                if (stepOfFailure # 2) then  
                    \* Step2: clear the state on NIB
                    controllerStateNIB[self] := [type |-> NO_STATUS];
                    if (stepOfFailure # 3) then
                        \* Step 3: remove from IRQueue
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
        \* After the worker failed and the watchdog has restarted it.
        \* Worker starts by calling the reconciliation function in which
        \* it undoes some of the operations
        
        \* If the state on db is LOCKING, worker has to unlock the semaphore if
        \* it owns the semaphore and also, if IRStatus is IR_SENT, thread should change it
        \* back to IR_NONE
        
        \* If the state on db is SENT_DONE, worker is sure that it has sent the IR,
        \* so, it has to unlock the semaphore if it owns the semaphore and also
        \* should add the IR to the scheduledSet. 
        await controllerIsMaster(self[1]);
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
    \* ==========================
    
    \* ===== Event Handler ======
    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, resetIR = 0, stepOfFailure = 0;
    begin
    ControllerEventHandlerProc:
    while TRUE do 
         await controllerIsMaster(self[1]);
         await moduleIsUp(self);   
         await swSeqChangedStatus # <<>>;
         controllerWaitForLockFree();
         
         \* Controller event handler process consists of two operations;
         \* 1. Picking the first event from the event queue
         \* 2. Check whether the event is a switch failure or a switch recovery
         monitoringEvent := Head(swSeqChangedStatus);
         if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
         
            \* ControllerSuspendSW only suspends the SW (so the rest of the system does not work on
            \* the tasks related to this switch anymore).
            \* Here, Due to performance reasons, we defere the task of resetting status of IRs to 
            \* the time that the switch is recovered (Lazy evaluation) because; First, it might not
            \* be necessary (for example, the switch may have installed the IR). Second, the switch
            \* may have faced a permanent failure in which these IRs are not valid anymore.                 
            ControllerSuspendSW: 
                controllerWaitForLockFree();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;        
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
                
         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            \*call suspendInSchedulingIRs(monitoringEvent.swID);
            
            \* ControllerFreeSuspendedSW consists of three operations; 
            \* 1. Save on db that it is going to reset the IRs
            \* 2. Change the SW status to SW_RUN (so all the corresponding IRs going to be scheduled immediately)
            \* (event handler may fail between any of these Ops.)
            ControllerFreeSuspendedSW: 
                controllerWaitForLockFree();
                whichStepToFail(2);
                if (stepOfFailure # 1) then 
                    \* Step 1: save state on NIB
                    controllerStateNIB[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                    if (stepOfFailure # 2) then
                        \* Step 2: change switch status to SW_RUN
                        SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;  
                    end if;
                end if;
                
                if (stepOfFailure # 0) then
                    controllerModuleFails();
                    goto ControllerEventHandlerStateReconciliation;
                end if;
            
            \* ControllerCheckIfThisIsLastEvent consists of 3 operations;
            \* 1. Check if this is the last event for the corresponding sw (if it is not, then, maybe the switch
            \*      has failed again and resetting the IRs is not necessary). Note that we have to process the 
            \*      event and change the status of SW anyway. Otherwise, it may result in discarding the subsequent
            \*      events (one of the failures!!!!)   
            \* 2. GetIRsToBeChecked 
            \* 3. ResetAllIRs
            ControllerCheckIfThisIsLastEvent:
                controllerWaitForLockFree();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    if ~existsMonitoringEventHigherNum(monitoringEvent) then
                        \* call reconcileStateWithRecoveredSW(monitoringEvent.swID);
                        
                        \* getIRsToBeChecked retrieves all the IRs need to reset
                        getIRsToBeChecked:
                            controllerWaitForLockFree();
                            controllerModuleFailOrNot();
                            if (controllerSubmoduleFailStat[self] = NotFailed) then
                                setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                                if (setIRsToReset = {}) then \* Do not do the operations in ResetAllIRs label if setIRsToReset is Empty *\
                                    goto ControllerEvenHanlderRemoveEventFromQueue;
                                end if;
                            else
                                goto ControllerEventHandlerStateReconciliation;
                            end if;
                            
                        \* ResetAllIRs reset all the IRs in IR_SENT mode to IR_NONE one by one
                        ResetAllIRs:
                            while TRUE do \* Initially: while setIRsToReset # {} do
                                controllerWaitForLockFree();
                                controllerModuleFailOrNot();
                                if (controllerSubmoduleFailStat[self] = NotFailed) then
                                    resetIR := CHOOSE x \in setIRsToReset: TRUE;
                                    setIRsToReset := setIRsToReset \ {resetIR};
                                    
                                    \* the following operation (if -- end if;) should be done atomically
                                    \* using CAS operation
                                    if IRStatus[resetIR] # IR_DONE then
                                        IRStatus[resetIR] := IR_NONE;
                                    end if;
                                    
                                    if setIRsToReset = {} then \* End of while *\
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
         
         \* ControllerEventHandlerRemoveEventFromQueue consists of 2 operations;
         \* 1. Clear the state on db
         \* 2. Remove the event from queue (Lazy removal procedure)
         \* event handler may fail between these Ops. 
         ControllerEvenHanlderRemoveEventFromQueue:
            controllerWaitForLockFree();
            whichStepToFail(2);
            if (stepOfFailure # 1) then 
                \* Step 1: clear state on NIB
                controllerStateNIB[self] := [type |-> NO_STATUS]; 
                if (stepOfFailure # 2) then
                    \* Step 2: remove from event queue
                    swSeqChangedStatus := Tail(swSeqChangedStatus);
                end if;
            end if;
            
            if (stepOfFailure # 0) then
                controllerModuleFails();
                goto ControllerEventHandlerStateReconciliation;
            end if;
    end while;
    
    
    \* After that the event handler failed and the watchdog has restarted it.
    \* Worker starts by calling the reconciliation function in which
    \* it undoes some of the operations.
    
    \* it is pretty straight forward here, if event handler is in START_RESET_IR
    \* status, it means we are not sure whether we have reset all the IRs or not
    \* so, event handler changes the SW status back to SW_SUSPEND and starts its
    \* normal execution in which it will first pick the first event in the queue.
    \* Note that due to lazy removal policy, the first event in the queu is exactly
    \* the sw recovery event. 
    ControllerEventHandlerStateReconciliation:
         await controllerIsMaster(self[1]);
         await moduleIsUp(self);   
         await swSeqChangedStatus # <<>>; 
         controllerReleaseLock(self);
         if (controllerStateNIB[self].type = START_RESET_IR) then
            SwSuspensionStatus[controllerStateNIB[self].sw] := SW_SUSPEND;
         end if;
        goto ControllerEventHandlerProc;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    \* monitroing server does not need a reconciliation phase. 
    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = [type |-> 0]
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        \* ControllerMonitor 
        \* 1. Picks the first packet from the packets received from the switches
        \* 2. Checks the message type;
        \***** 2.1. type = INSTALLED_SUCCESSFULLY -> sw has successfully installed the IR
        \***** 2.2. type = RECONCILIATION_RESPONCE -> sw's responce to the reconciliation 
        \*****              request. 
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
                \* If msg type is INSTALLED_SUCCESSFULLY, we have to change the IR status
                \* to IR_DONE. 
                ControllerUpdateIR2:
                    controllerWaitForLockFree(); 
                    controllerModuleFailOrNot();
                    if (controllerSubmoduleFailStat[self] = NotFailed) then
                        FirstInstall[msg.IR] := 1;
                        IRStatus[msg.IR] := IR_DONE; \* Should be done in one atomic operation
                    else
                        goto ControllerMonitorCheckIfMastr;
                    end if;
            else assert FALSE;
            end if;
        
        \*end if;
        
        \* MonitoringServerRemoveFromQueue lazily removes the msg from queue. 
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
    
    \* ==========================
    
    
    (*******************************************************************)
    (*                     Shared (OFC and RC)                         *)
    (*******************************************************************)
    \* there are two watchdogs, one in RC, the other in OFC
    \* ======== Watchdog ======== 
    fair process watchDog \in ({ofc0, rc0} \X {WATCH_DOG})
    \* Watchdog in each iteration finds all the failed submodules 
    \* and creates branches in each of which one of the failed 
    \* submodules is restarted. 
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
    \* ==========================
       
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9746e5736056805efb3f99c54c5dea55
\* Process variable stepOfFailure of process controllerSequencer at line 1480 col 124 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 1607 col 64 changed to stepOfFailure_c
VARIABLES switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
          ContProcSet, SwProcSet, swSeqChangedStatus, controller2Switch, 
          switch2Controller, switchStatus, installedIRs, NicAsic2OfaBuff, 
          Ofa2NicAsicBuff, Installer2OfaBuff, Ofa2InstallerBuff, TCAM, 
          controlMsgCounter, controllerSubmoduleFailNum, 
          controllerSubmoduleFailStat, switchOrdering, dependencyGraph, IR2SW, 
          idThreadWorkingOnIR, workerThreadRanking, NIB2OFC, NIB2RC, OFC2NIB, 
          RC2NIB, masterState, controllerStateNIB, IRStatus, 
          SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, pc

(* define statement *)
max(set) == CHOOSE x \in set: \A y \in set: x \geq y
min(set) == CHOOSE x \in set: \A y \in set: x \leq y
rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]

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


PlausibleDependencySet == UNION {GeneralSetSetUnion({generateConnectedDAG(((sum(allSizes, y-1) + 1)..(sum(allSizes, y)))):
                                                                                y \in 1..(Len(allSizes) - 1)}):
                                                                                     allSizes \in AllPossibleSizes(MaxNumIRs, MaxNumIRs)}




whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID]

swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed


swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed

swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed


returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}

getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: IR2SW[x] = SID}


returnSwitchFailedElements(sw) == {x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                                                  /\ \/ switchStatus[sw].cpu = NotFailed
                                                                     \/ x \notin {"ofa", "installer"}}
installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerProc"
ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaProcIn"
                         /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaProcOut"
nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchRcvPacket"
                             /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchFromOFAPacket"
getInstallerStatus(stat) == IF stat = NotFailed
                            THEN INSTALLER_UP
                            ELSE INSTALLER_DOWN


moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
controllerIsMaster(controllerID) == CASE controllerID = rc0 -> masterState.rc0 = "primary"
                                      [] controllerID = ofc0 -> masterState.ofc0 = "primary"
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

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, failedSet, 
          statusResolveMsg, recoveredElem, toBeScheduledIRs, key, op1, op2, 
          transaction, nextIR, stepOfFailure_, nextTrans, nextIRToSent, 
          rowIndex, rowRemove, stepOfFailure_c, monitoringEvent, 
          setIRsToReset, resetIR, stepOfFailure, msg, controllerFailedModules

vars == << switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
           ContProcSet, SwProcSet, swSeqChangedStatus, controller2Switch, 
           switch2Controller, switchStatus, installedIRs, NicAsic2OfaBuff, 
           Ofa2NicAsicBuff, Installer2OfaBuff, Ofa2InstallerBuff, TCAM, 
           controlMsgCounter, controllerSubmoduleFailNum, 
           controllerSubmoduleFailStat, switchOrdering, dependencyGraph, 
           IR2SW, idThreadWorkingOnIR, workerThreadRanking, NIB2OFC, NIB2RC, 
           OFC2NIB, RC2NIB, masterState, controllerStateNIB, IRStatus, 
           SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, pc, ingressPkt, 
           ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, installerInIR, 
           statusMsg, notFailedSet, failedElem, failedSet, statusResolveMsg, 
           recoveredElem, toBeScheduledIRs, key, op1, op2, transaction, 
           nextIR, stepOfFailure_, nextTrans, nextIRToSent, rowIndex, 
           rowRemove, stepOfFailure_c, monitoringEvent, setIRsToReset, 
           resetIR, stepOfFailure, msg, controllerFailedModules >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({rc0} \X {CONT_SEQ})) \cup (({nib0} \X {CONT_NIB_RC_EVENT})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})) \cup (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ ContProcSet = ((({rc0} \X {CONT_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL))
                          \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})))
        /\ SwProcSet = ((({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW))
                          \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW))
                          \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW))
                          \cup (({SW_RESOLVE_PROC} \X SW)))
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x\in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ switchStatus = [x\in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed,
                           ofa |-> NotFailed, installer |-> NotFailed]]
        /\ installedIRs = <<>>
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> <<>>]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ switchOrdering = (CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ IR2SW = (CHOOSE x \in [1..MaxNumIRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z
                                                                              /\ switchOrdering[x[y]] =< switchOrdering[x[z]])
        /\ idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK]
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ NIB2OFC = <<>>
        /\ NIB2RC = <<>>
        /\ OFC2NIB = <<>>
        /\ RC2NIB = <<>>
        /\ masterState = [ofc0 |-> "primary", rc0 |-> "primary"]
        /\ controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ SetScheduledIRs = [y \in SW |-> {}]
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
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ key = [self \in ({rc0} \X {CONT_SEQ}) |-> ""]
        /\ op1 = [self \in ({rc0} \X {CONT_SEQ}) |-> [table |-> ""]]
        /\ op2 = [self \in ({rc0} \X {CONT_SEQ}) |-> [table |-> ""]]
        /\ transaction = [self \in ({rc0} \X {CONT_SEQ}) |-> <<>>]
        /\ nextIR = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        (* Process NIBRCEventHandler *)
        /\ nextTrans = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> [type |-> 0]]
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
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({NIC_ASIC_IN} \X SW) -> "SwitchRcvPacket"
                                        [] self \in ({NIC_ASIC_OUT} \X SW) -> "SwitchFromOFAPacket"
                                        [] self \in ({OFA_IN} \X SW) -> "SwitchOfaProcIn"
                                        [] self \in ({OFA_OUT} \X SW) -> "SwitchOfaProcOut"
                                        [] self \in ({INSTALLER} \X SW) -> "SwitchInstallerProc"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({rc0} \X {CONT_SEQ}) -> "ControllerSeqProc"
                                        [] self \in ({nib0} \X {CONT_NIB_RC_EVENT}) -> "NIBRCEventHandling"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({ofc0, rc0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type = INSTALL_FLOW, 
                                       "Failure of assertion at line 1072, column 9.")
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ installedIRs' = Append(installedIRs, ingressPkt'[self].IR)
                             /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], ingressPkt'[self].IR)]
                             /\ switch2Controller' = Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                                                from |-> self[2],
                                                                                IR |-> ingressPkt'[self].IR])
                             /\ Assert(\/ switchLock[2] = self[2]
                                       \/ switchLock[2] = NO_LOCK, 
                                       "Failure of assertion at line 742, column 9 of macro called at line 1079, column 9.")
                             /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             switchStatus, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, 
                                             controlMsgCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, idThreadWorkingOnIR, 
                                             workerThreadRanking, NIB2OFC, 
                                             NIB2RC, OFC2NIB, RC2NIB, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, SwSuspensionStatus, 
                                             IRQueueNIB, SetScheduledIRs, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, key, op1, op2, 
                                             transaction, nextIR, 
                                             stepOfFailure_, nextTrans, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, 
                                             controllerFailedModules >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(\/ ingressIR'[self].type = RECONCILIATION_REQUEST
                                   \/ ingressIR'[self].type = INSTALL_FLOW, 
                                   "Failure of assertion at line 1104, column 9.")
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << controllerLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, swSeqChangedStatus, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, idThreadWorkingOnIR, 
                                         workerThreadRanking, NIB2OFC, NIB2RC, 
                                         OFC2NIB, RC2NIB, masterState, 
                                         controllerStateNIB, IRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, toBeScheduledIRs, key, 
                                         op1, op2, transaction, nextIR, 
                                         stepOfFailure_, nextTrans, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure_c, monitoringEvent, 
                                         setIRsToReset, resetIR, stepOfFailure, 
                                         msg, controllerFailedModules >>

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
                                                 /\ UNCHANGED << switchLock, 
                                                                 NicAsic2OfaBuff >>
                                      /\ UNCHANGED << controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      NIB2OFC, NIB2RC, OFC2NIB, 
                                                      RC2NIB, masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, key, 
                                                      op1, op2, transaction, 
                                                      nextIR, stepOfFailure_, 
                                                      nextTrans, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
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
                                       "Failure of assertion at line 1132, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, idThreadWorkingOnIR, 
                                             workerThreadRanking, NIB2OFC, 
                                             NIB2RC, OFC2NIB, RC2NIB, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, SwSuspensionStatus, 
                                             IRQueueNIB, SetScheduledIRs, 
                                             ingressPkt, ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, key, op1, op2, 
                                             transaction, nextIR, 
                                             stepOfFailure_, nextTrans, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, 
                                             controllerFailedModules >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 742, column 9 of macro called at line 1141, column 17.")
                                            /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ switch2Controller' = Append(switch2Controller, egressMsg[self])
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED egressMsg
                                       ELSE /\ egressMsg' = [egressMsg EXCEPT ![self] = [type |-> 0]]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED << switchLock, 
                                                            switch2Controller >>
                                 /\ UNCHANGED << controllerLock, FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, 
                                                 dependencyGraph, IR2SW, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, NIB2OFC, 
                                                 NIB2RC, OFC2NIB, RC2NIB, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, key, op1, 
                                                 op2, transaction, nextIR, 
                                                 stepOfFailure_, nextTrans, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, 
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
                                   "Failure of assertion at line 1169, column 9.")
                         /\ Assert(ofaInMsg'[self].IR  \in 1..MaxNumIRs, 
                                   "Failure of assertion at line 1170, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << controllerLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, idThreadWorkingOnIR, 
                                         workerThreadRanking, NIB2OFC, NIB2RC, 
                                         OFC2NIB, RC2NIB, masterState, 
                                         controllerStateNIB, IRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, toBeScheduledIRs, key, 
                                         op1, op2, transaction, nextIR, 
                                         stepOfFailure_, nextTrans, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure_c, monitoringEvent, 
                                         setIRsToReset, resetIR, stepOfFailure, 
                                         msg, controllerFailedModules >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                           /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           /\ switchLock' = <<INSTALLER, self[2]>>
                                           /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                                 THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], ofaInMsg[self].IR)]
                                                 ELSE /\ Assert(FALSE, 
                                                                "Failure of assertion at line 1183, column 21.")
                                                      /\ UNCHANGED Ofa2InstallerBuff
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED ofaInMsg
                                      ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED << switchLock, 
                                                           Ofa2InstallerBuff >>
                                /\ UNCHANGED << controllerLock, FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, NIB2OFC, 
                                                NIB2RC, OFC2NIB, RC2NIB, 
                                                masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, key, op1, 
                                                op2, transaction, nextIR, 
                                                stepOfFailure_, nextTrans, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
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
                                    "Failure of assertion at line 1204, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << controllerLock, FirstInstall, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, idThreadWorkingOnIR, 
                                          workerThreadRanking, NIB2OFC, NIB2RC, 
                                          OFC2NIB, RC2NIB, masterState, 
                                          controllerStateNIB, IRStatus, 
                                          SwSuspensionStatus, IRQueueNIB, 
                                          SetScheduledIRs, ingressPkt, 
                                          ingressIR, egressMsg, ofaInMsg, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, key, op1, op2, 
                                          transaction, nextIR, stepOfFailure_, 
                                          nextTrans, nextIRToSent, rowIndex, 
                                          rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, 
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
                                                 /\ UNCHANGED << switchLock, 
                                                                 Ofa2NicAsicBuff >>
                                      /\ UNCHANGED << controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      NicAsic2OfaBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      NIB2OFC, NIB2RC, OFC2NIB, 
                                                      RC2NIB, masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, key, 
                                                      op1, op2, transaction, 
                                                      nextIR, stepOfFailure_, 
                                                      nextTrans, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
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
                                       "Failure of assertion at line 1236, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, idThreadWorkingOnIR, 
                                             workerThreadRanking, NIB2OFC, 
                                             NIB2RC, OFC2NIB, RC2NIB, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, SwSuspensionStatus, 
                                             IRQueueNIB, SetScheduledIRs, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, key, op1, op2, 
                                             transaction, nextIR, 
                                             stepOfFailure_, nextTrans, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, 
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
                                               /\ UNCHANGED << switchLock, 
                                                               installedIRs, 
                                                               TCAM >>
                                    /\ UNCHANGED << controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, 
                                                    controlMsgCounter, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    NIB2OFC, NIB2RC, OFC2NIB, 
                                                    RC2NIB, masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, key, op1, 
                                                    op2, transaction, nextIR, 
                                                    stepOfFailure_, nextTrans, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, 
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
                                                    /\ UNCHANGED << switchLock, 
                                                                    Installer2OfaBuff >>
                                         /\ UNCHANGED << controllerLock, 
                                                         FirstInstall, 
                                                         sw_fail_ordering_var, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         switchStatus, 
                                                         installedIRs, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         controllerSubmoduleFailNum, 
                                                         controllerSubmoduleFailStat, 
                                                         switchOrdering, 
                                                         dependencyGraph, 
                                                         IR2SW, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         NIB2OFC, NIB2RC, 
                                                         OFC2NIB, RC2NIB, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, key, 
                                                         op1, op2, transaction, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         nextTrans, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         controllerFailedModules >>

installerModuleProc(self) == SwitchInstallerProc(self)
                                \/ SwitchInstallerInsert2TCAM(self)
                                \/ SwitchInstallerSendConfirmation(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ notFailedSet' = [notFailedSet EXCEPT ![self] = returnSwitchElementsNotFailed(self[2])]
                       /\ notFailedSet'[self] # {}
                       /\ ~isFinished
                       /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                             \/ switchLock[2] = self[2]
                       /\ \E x \in getSetIRsForSwitch(self[2]): IRStatus[x] # IR_DONE
                       /\ sw_fail_ordering_var # <<>>
                       /\ self[2] \in Head(sw_fail_ordering_var)
                       /\ Assert((self[2]) \in Head(sw_fail_ordering_var), 
                                 "Failure of assertion at line 496, column 9 of macro called at line 1288, column 9.")
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{(self[2])})>> \o Tail(sw_fail_ordering_var)
                       /\ \E elem \in notFailedSet'[self]:
                            failedElem' = [failedElem EXCEPT ![self] = elem]
                       /\ IF failedElem'[self] = "cpu"
                             THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                  /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                            "Failure of assertion at line 569, column 9 of macro called at line 1297, column 17.")
                                  /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = Failed,
                                                                          ![self[2]].ofa = Failed,
                                                                          ![self[2]].installer = Failed]
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
                                                       "Failure of assertion at line 621, column 9 of macro called at line 1300, column 17.")
                                             /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = Failed]
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
                                                                  "Failure of assertion at line 665, column 9 of macro called at line 1303, column 17.")
                                                        /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                        /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                              THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                             "Failure of assertion at line 668, column 13 of macro called at line 1303, column 17.")
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
                                                                             "Failure of assertion at line 515, column 9 of macro called at line 1306, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]]]]
                                                                   /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                                              ELSE /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 1307, column 14.")
                                                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                                                   controller2Switch, 
                                                                                   switchStatus, 
                                                                                   controlMsgCounter, 
                                                                                   statusMsg >>
                                  /\ UNCHANGED << NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff >>
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstall, ContProcSet, SwProcSet, 
                                       switch2Controller, installedIRs, TCAM, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, NIB2OFC, NIB2RC, 
                                       OFC2NIB, RC2NIB, masterState, 
                                       controllerStateNIB, IRStatus, 
                                       SwSuspensionStatus, IRQueueNIB, 
                                       SetScheduledIRs, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, failedSet, 
                                       statusResolveMsg, recoveredElem, 
                                       toBeScheduledIRs, key, op1, op2, 
                                       transaction, nextIR, stepOfFailure_, 
                                       nextTrans, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, 
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
                                                   "Failure of assertion at line 596, column 9 of macro called at line 1332, column 39.")
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
                                                              "Failure of assertion at line 541, column 9 of macro called at line 1333, column 46.")
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
                                                                         "Failure of assertion at line 643, column 9 of macro called at line 1334, column 42.")
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
                                                                                    "Failure of assertion at line 687, column 9 of macro called at line 1335, column 48.")
                                                                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                               "Failure of assertion at line 690, column 13 of macro called at line 1335, column 48.")
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
                                                                                    "Failure of assertion at line 1336, column 14.")
                                                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                                                          switchStatus, 
                                                                                          controlMsgCounter, 
                                                                                          statusResolveMsg >>
                                                    /\ UNCHANGED controller2Switch
                                         /\ UNCHANGED << NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Installer2OfaBuff, 
                                                         Ofa2InstallerBuff >>
                              /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              switch2Controller, installedIRs, 
                                              TCAM, controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, dependencyGraph, 
                                              IR2SW, idThreadWorkingOnIR, 
                                              workerThreadRanking, NIB2OFC, 
                                              NIB2RC, OFC2NIB, RC2NIB, 
                                              masterState, controllerStateNIB, 
                                              IRStatus, SwSuspensionStatus, 
                                              IRQueueNIB, SetScheduledIRs, 
                                              ingressPkt, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              toBeScheduledIRs, key, op1, op2, 
                                              transaction, nextIR, 
                                              stepOfFailure_, nextTrans, 
                                              nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure_c, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, stepOfFailure, msg, 
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
                             "Failure of assertion at line 742, column 9 of macro called at line 1370, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << controllerLock, FirstInstall, 
                                   sw_fail_ordering_var, ContProcSet, 
                                   SwProcSet, swSeqChangedStatus, 
                                   controller2Switch, switch2Controller, 
                                   switchStatus, installedIRs, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   dependencyGraph, IR2SW, idThreadWorkingOnIR, 
                                   workerThreadRanking, NIB2OFC, NIB2RC, 
                                   OFC2NIB, RC2NIB, masterState, 
                                   controllerStateNIB, IRStatus, 
                                   SwSuspensionStatus, IRQueueNIB, 
                                   SetScheduledIRs, ingressPkt, ingressIR, 
                                   egressMsg, ofaInMsg, ofaOutConfirmation, 
                                   installerInIR, statusMsg, notFailedSet, 
                                   failedElem, failedSet, statusResolveMsg, 
                                   recoveredElem, toBeScheduledIRs, key, op1, 
                                   op2, transaction, nextIR, stepOfFailure_, 
                                   nextTrans, nextIRToSent, rowIndex, 
                                   rowRemove, stepOfFailure_c, monitoringEvent, 
                                   setIRsToReset, resetIR, stepOfFailure, msg, 
                                   controllerFailedModules >>

ghostUnlockProcess(self) == ghostProc(self)

ControllerSeqProc(self) == /\ pc[self] = "ControllerSeqProc"
                           /\ controllerIsMaster(self[1])
                           /\ moduleIsUp(self)
                           /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1])]
                           /\ toBeScheduledIRs'[self] # {}
                           /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           IR2SW, idThreadWorkingOnIR, 
                                           workerThreadRanking, NIB2OFC, 
                                           NIB2RC, OFC2NIB, RC2NIB, 
                                           masterState, controllerStateNIB, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, SetScheduledIRs, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           key, op1, op2, transaction, nextIR, 
                                           stepOfFailure_, nextTrans, 
                                           nextIRToSent, rowIndex, rowRemove, 
                                           stepOfFailure_c, monitoringEvent, 
                                           setIRsToReset, resetIR, 
                                           stepOfFailure, msg, 
                                           controllerFailedModules >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                  THEN /\ \E num \in 0..2:
                                            stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                                  ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                            /\ IF (stepOfFailure_'[self] # 1)
                                  THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                                       /\ IF (stepOfFailure_'[self] # 2)
                                             THEN /\ op1' = [op1 EXCEPT ![self] = [table |-> NIBT_CONTROLLER_STATE, key |-> self, value |-> [type |-> STATUS_START_SCHEDULING, next |-> nextIR'[self]]]]
                                                  /\ op2' = [op2 EXCEPT ![self] = [table |-> NIBT_SET_SCHEDULED_IRS, key |-> IR2SW[nextIR'[self]], value |-> SetScheduledIRs[IR2SW[nextIR'[self]]] \cup {nextIR'[self]}]]
                                                  /\ transaction' = [transaction EXCEPT ![self] = [name |-> "PrepareIR", ops |-> <<op1'[self], op2'[self]>>]]
                                                  /\ RC2NIB' = RC2NIB \o <<transaction'[self]>>
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << RC2NIB, op1, 
                                                                  op2, 
                                                                  transaction >>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << RC2NIB, op1, op2, 
                                                       transaction, nextIR >>
                            /\ pc' = [pc EXCEPT ![self] = "RCModuleFail"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstall, sw_fail_ordering_var, 
                                            ContProcSet, SwProcSet, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, idThreadWorkingOnIR, 
                                            workerThreadRanking, NIB2OFC, 
                                            NIB2RC, OFC2NIB, masterState, 
                                            controllerStateNIB, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            SetScheduledIRs, ingressPkt, 
                                            ingressIR, egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            toBeScheduledIRs, key, nextTrans, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, 
                                            controllerFailedModules >>

RCModuleFail(self) == /\ pc[self] = "RCModuleFail"
                      /\ IF (stepOfFailure_[self] # 0)
                            THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                 /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                                 /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat >>
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, swSeqChangedStatus, 
                                      controller2Switch, switch2Controller, 
                                      switchStatus, installedIRs, 
                                      NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                      Installer2OfaBuff, Ofa2InstallerBuff, 
                                      TCAM, controlMsgCounter, switchOrdering, 
                                      dependencyGraph, IR2SW, 
                                      idThreadWorkingOnIR, workerThreadRanking, 
                                      NIB2OFC, NIB2RC, OFC2NIB, RC2NIB, 
                                      masterState, controllerStateNIB, 
                                      IRStatus, SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, failedSet, statusResolveMsg, 
                                      recoveredElem, toBeScheduledIRs, key, 
                                      op1, op2, transaction, nextIR, 
                                      stepOfFailure_, nextTrans, nextIRToSent, 
                                      rowIndex, rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
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
                             THEN /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
                                  /\ IF (stepOfFailure_'[self] # 2)
                                        THEN /\ op1' = [op1 EXCEPT ![self] = [table |-> NIBT_IR_QUEUE, key |-> NULL, value |-> [IR |-> nextIR[self], tag |-> NO_TAG]]]
                                             /\ op2' = [op2 EXCEPT ![self] = [table |-> NIBT_CONTROLLER_STATE, key |-> self, value |-> [type |-> NO_STATUS]]]
                                             /\ transaction' = [transaction EXCEPT ![self] = [name |-> "ScheduleIR", ops |-> <<op1'[self], op2'[self]>>]]
                                             /\ RC2NIB' = RC2NIB \o <<transaction'[self]>>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << RC2NIB, op1, op2, 
                                                             transaction >>
                             ELSE /\ TRUE
                                  /\ UNCHANGED << RC2NIB, toBeScheduledIRs, 
                                                  op1, op2, transaction >>
                       /\ pc' = [pc EXCEPT ![self] = "RCModuleFailAfterSendIR"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstall, sw_fail_ordering_var, 
                                       ContProcSet, SwProcSet, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, switchStatus, 
                                       installedIRs, NicAsic2OfaBuff, 
                                       Ofa2NicAsicBuff, Installer2OfaBuff, 
                                       Ofa2InstallerBuff, TCAM, 
                                       controlMsgCounter, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, NIB2OFC, NIB2RC, 
                                       OFC2NIB, masterState, 
                                       controllerStateNIB, IRStatus, 
                                       SwSuspensionStatus, IRQueueNIB, 
                                       SetScheduledIRs, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, failedSet, statusResolveMsg, 
                                       recoveredElem, key, nextIR, nextTrans, 
                                       nextIRToSent, rowIndex, rowRemove, 
                                       stepOfFailure_c, monitoringEvent, 
                                       setIRsToReset, resetIR, stepOfFailure, 
                                       msg, controllerFailedModules >>

RCModuleFailAfterSendIR(self) == /\ pc[self] = "RCModuleFailAfterSendIR"
                                 /\ IF (stepOfFailure_[self] # 0)
                                       THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                            /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                            /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                       ELSE /\ IF toBeScheduledIRs[self] = {}
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                            /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                            controllerSubmoduleFailStat >>
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 switchOrdering, 
                                                 dependencyGraph, IR2SW, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, NIB2OFC, 
                                                 NIB2RC, OFC2NIB, RC2NIB, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, key, op1, 
                                                 op2, transaction, nextIR, 
                                                 stepOfFailure_, nextTrans, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, 
                                                 controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ controllerIsMaster(self[1])
                                          /\ moduleIsUp(self)
                                          /\ \/ controllerLock = self
                                             \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (controllerStateNIB[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![IR2SW[controllerStateNIB[self].next]] = SetScheduledIRs[IR2SW[controllerStateNIB[self].next]]\{controllerStateNIB[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
                                          /\ UNCHANGED << switchLock, 
                                                          FirstInstall, 
                                                          sw_fail_ordering_var, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          switchStatus, 
                                                          installedIRs, 
                                                          NicAsic2OfaBuff, 
                                                          Ofa2NicAsicBuff, 
                                                          Installer2OfaBuff, 
                                                          Ofa2InstallerBuff, 
                                                          TCAM, 
                                                          controlMsgCounter, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          dependencyGraph, 
                                                          IR2SW, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          NIB2OFC, NIB2RC, 
                                                          OFC2NIB, RC2NIB, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
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
                                                          key, op1, op2, 
                                                          transaction, nextIR, 
                                                          stepOfFailure_, 
                                                          nextTrans, 
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
                                \/ RCModuleFail(self)
                                \/ ScheduleTheIR(self)
                                \/ RCModuleFailAfterSendIR(self)
                                \/ ControllerSeqStateReconciliation(self)

NIBRCEventHandling(self) == /\ pc[self] = "NIBRCEventHandling"
                            /\ RC2NIB # <<>>
                            /\ nextTrans' = [nextTrans EXCEPT ![self] = Head(RC2NIB)]
                            /\ IF (nextTrans'[self].name = "PrepareIR")
                                  THEN /\ Assert(nextTrans'[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                 "Failure of assertion at line 871, column 9 of macro called at line 1591, column 13.")
                                       /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans'[self].ops[1].key] = nextTrans'[self].ops[1].value]
                                       /\ Assert(nextTrans'[self].ops[2].table = NIBT_SET_SCHEDULED_IRS, 
                                                 "Failure of assertion at line 873, column 9 of macro called at line 1591, column 13.")
                                       /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans'[self].ops[2].key] = nextTrans'[self].ops[2].value]
                                       /\ UNCHANGED IRQueueNIB
                                  ELSE /\ IF (nextTrans'[self].name = "ScheduleIR")
                                             THEN /\ Assert(nextTrans'[self].ops[1].table = NIBT_IR_QUEUE, 
                                                            "Failure of assertion at line 879, column 9 of macro called at line 1593, column 13.")
                                                  /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans'[self].ops[1].value)
                                                  /\ Assert(nextTrans'[self].ops[2].table = NIBT_CONTROLLER_STATE, 
                                                            "Failure of assertion at line 881, column 9 of macro called at line 1593, column 13.")
                                                  /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans'[self].ops[2].key] = nextTrans'[self].ops[2].value]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << controllerStateNIB, 
                                                                  IRQueueNIB >>
                                       /\ UNCHANGED SetScheduledIRs
                            /\ RC2NIB' = Tail(RC2NIB)
                            /\ pc' = [pc EXCEPT ![self] = "NIBRCEventHandling"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstall, sw_fail_ordering_var, 
                                            ContProcSet, SwProcSet, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, idThreadWorkingOnIR, 
                                            workerThreadRanking, NIB2OFC, 
                                            NIB2RC, OFC2NIB, masterState, 
                                            IRStatus, SwSuspensionStatus, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, toBeScheduledIRs, 
                                            key, op1, op2, transaction, nextIR, 
                                            stepOfFailure_, nextIRToSent, 
                                            rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, 
                                            controllerFailedModules >>

NIBRCEventHandler(self) == NIBRCEventHandling(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerIsMaster(self[1])
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
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, workerThreadRanking, NIB2OFC, 
                                          NIB2RC, OFC2NIB, RC2NIB, masterState, 
                                          IRStatus, SwSuspensionStatus, 
                                          SetScheduledIRs, ingressPkt, 
                                          ingressIR, egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, toBeScheduledIRs, key, 
                                          op1, op2, transaction, nextIR, 
                                          stepOfFailure_, nextTrans, rowRemove, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, 
                                          controllerFailedModules >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                      THEN /\ IF ~isSwitchSuspended(IR2SW[nextIRToSent[self]]) /\ IRStatus[nextIRToSent[self]] = IR_NONE
                                                 THEN /\ IRStatus' = [IRStatus EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForIRToHaveCorrectStatus"]
                                                      /\ UNCHANGED IRStatus
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                           /\ UNCHANGED IRStatus
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, NIB2OFC, 
                                                NIB2RC, OFC2NIB, RC2NIB, 
                                                masterState, 
                                                controllerStateNIB, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, key, op1, 
                                                op2, transaction, nextIR, 
                                                stepOfFailure_, nextTrans, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
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
                                         THEN /\ controller2Switch' = [controller2Switch EXCEPT ![IR2SW[nextIRToSent[self]]] = Append(controller2Switch[IR2SW[nextIRToSent[self]]], [type |-> INSTALL_FLOW,
                                                                                                                                                                                     to |-> IR2SW[nextIRToSent[self]],
                                                                                                                                                                                     IR |-> nextIRToSent[self]])]
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
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switchOrdering, 
                                                   dependencyGraph, IR2SW, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   NIB2OFC, NIB2RC, OFC2NIB, 
                                                   RC2NIB, masterState, 
                                                   IRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, key, op1, 
                                                   op2, transaction, nextIR, 
                                                   stepOfFailure_, nextTrans, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, 
                                                   controllerFailedModules >>

WaitForIRToHaveCorrectStatus(self) == /\ pc[self] = "WaitForIRToHaveCorrectStatus"
                                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                            THEN /\ ~isSwitchSuspended(IR2SW[nextIRToSent[self]])
                                                 /\ pc' = [pc EXCEPT ![self] = "ReScheduleifIRNone"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      NicAsic2OfaBuff, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      NIB2OFC, NIB2RC, OFC2NIB, 
                                                      RC2NIB, masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, key, 
                                                      op1, op2, transaction, 
                                                      nextIR, stepOfFailure_, 
                                                      nextTrans, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
                                                      controllerFailedModules >>

ReScheduleifIRNone(self) == /\ pc[self] = "ReScheduleifIRNone"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                  THEN /\ IF IRStatus[nextIRToSent[self]] = IR_NONE
                                             THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent[self]]]
                                                  /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                                  /\ UNCHANGED controllerStateNIB
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                       /\ UNCHANGED controllerStateNIB
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstall, sw_fail_ordering_var, 
                                            ContProcSet, SwProcSet, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, switchOrdering, 
                                            dependencyGraph, IR2SW, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, NIB2OFC, 
                                            NIB2RC, OFC2NIB, RC2NIB, 
                                            masterState, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            SetScheduledIRs, ingressPkt, 
                                            ingressIR, egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            toBeScheduledIRs, key, op1, op2, 
                                            transaction, nextIR, 
                                            stepOfFailure_, nextTrans, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, 
                                            controllerFailedModules >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
                                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                                         FirstInstall, 
                                                         sw_fail_ordering_var, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         switchStatus, 
                                                         installedIRs, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Installer2OfaBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         switchOrdering, 
                                                         dependencyGraph, 
                                                         IR2SW, 
                                                         workerThreadRanking, 
                                                         NIB2OFC, NIB2RC, 
                                                         OFC2NIB, RC2NIB, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, key, 
                                                         op1, op2, transaction, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         nextTrans, 
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
                                                  FirstInstall, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  switchStatus, installedIRs, 
                                                  NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  switchOrdering, 
                                                  dependencyGraph, IR2SW, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, NIB2OFC, 
                                                  NIB2RC, OFC2NIB, RC2NIB, 
                                                  masterState, IRStatus, 
                                                  SwSuspensionStatus, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, 
                                                  toBeScheduledIRs, key, op1, 
                                                  op2, transaction, nextIR, 
                                                  stepOfFailure_, nextTrans, 
                                                  nextIRToSent, rowIndex, 
                                                  monitoringEvent, 
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
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      NicAsic2OfaBuff, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      NIB2OFC, NIB2RC, OFC2NIB, 
                                                      RC2NIB, masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, key, 
                                                      op1, op2, transaction, 
                                                      nextIR, stepOfFailure_, 
                                                      nextTrans, nextIRToSent, 
                                                      rowIndex, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
                                                      controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ controllerIsMaster(self[1])
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
                                                             FirstInstall, 
                                                             sw_fail_ordering_var, 
                                                             ContProcSet, 
                                                             SwProcSet, 
                                                             swSeqChangedStatus, 
                                                             controller2Switch, 
                                                             switch2Controller, 
                                                             switchStatus, 
                                                             installedIRs, 
                                                             NicAsic2OfaBuff, 
                                                             Ofa2NicAsicBuff, 
                                                             Installer2OfaBuff, 
                                                             Ofa2InstallerBuff, 
                                                             TCAM, 
                                                             controlMsgCounter, 
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             switchOrdering, 
                                                             dependencyGraph, 
                                                             IR2SW, 
                                                             workerThreadRanking, 
                                                             NIB2OFC, NIB2RC, 
                                                             OFC2NIB, RC2NIB, 
                                                             masterState, 
                                                             controllerStateNIB, 
                                                             SwSuspensionStatus, 
                                                             IRQueueNIB, 
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
                                                             key, op1, op2, 
                                                             transaction, 
                                                             nextIR, 
                                                             stepOfFailure_, 
                                                             nextTrans, 
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
                                    /\ controllerIsMaster(self[1])
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
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    NIB2OFC, NIB2RC, OFC2NIB, 
                                                    RC2NIB, masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, key, op1, 
                                                    op2, transaction, nextIR, 
                                                    stepOfFailure_, nextTrans, 
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
                                                                   FirstInstall, 
                                                                   sw_fail_ordering_var, 
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   switchStatus, 
                                                                   installedIRs, 
                                                                   NicAsic2OfaBuff, 
                                                                   Ofa2NicAsicBuff, 
                                                                   Installer2OfaBuff, 
                                                                   Ofa2InstallerBuff, 
                                                                   TCAM, 
                                                                   controlMsgCounter, 
                                                                   switchOrdering, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   NIB2OFC, 
                                                                   NIB2RC, 
                                                                   OFC2NIB, 
                                                                   RC2NIB, 
                                                                   masterState, 
                                                                   IRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
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
                                                                   key, op1, 
                                                                   op2, 
                                                                   transaction, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   nextTrans, 
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
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED SwSuspensionStatus
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, switchOrdering, 
                                             dependencyGraph, IR2SW, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, NIB2OFC, 
                                             NIB2RC, OFC2NIB, RC2NIB, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, key, op1, op2, 
                                             transaction, nextIR, 
                                             stepOfFailure_, nextTrans, 
                                             nextIRToSent, rowIndex, rowRemove, 
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
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switchOrdering, 
                                                   dependencyGraph, IR2SW, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   NIB2OFC, NIB2RC, OFC2NIB, 
                                                   RC2NIB, masterState, 
                                                   IRStatus, IRQueueNIB, 
                                                   SetScheduledIRs, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, key, op1, 
                                                   op2, transaction, nextIR, 
                                                   stepOfFailure_, nextTrans, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, msg, 
                                                   controllerFailedModules >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                                THEN /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self])
                                                           THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLock, 
                                                          FirstInstall, 
                                                          sw_fail_ordering_var, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          swSeqChangedStatus, 
                                                          controller2Switch, 
                                                          switch2Controller, 
                                                          switchStatus, 
                                                          installedIRs, 
                                                          NicAsic2OfaBuff, 
                                                          Ofa2NicAsicBuff, 
                                                          Installer2OfaBuff, 
                                                          Ofa2InstallerBuff, 
                                                          TCAM, 
                                                          controlMsgCounter, 
                                                          switchOrdering, 
                                                          dependencyGraph, 
                                                          IR2SW, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          NIB2OFC, NIB2RC, 
                                                          OFC2NIB, RC2NIB, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          SetScheduledIRs, 
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
                                                          key, op1, op2, 
                                                          transaction, nextIR, 
                                                          stepOfFailure_, 
                                                          nextTrans, 
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
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                      /\ UNCHANGED setIRsToReset
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, switchOrdering, 
                                           dependencyGraph, IR2SW, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, NIB2OFC, 
                                           NIB2RC, OFC2NIB, RC2NIB, 
                                           masterState, controllerStateNIB, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, SetScheduledIRs, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           toBeScheduledIRs, key, op1, op2, 
                                           transaction, nextIR, stepOfFailure_, 
                                           nextTrans, nextIRToSent, rowIndex, 
                                           rowRemove, stepOfFailure_c, 
                                           monitoringEvent, resetIR, 
                                           stepOfFailure, msg, 
                                           controllerFailedModules >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                     /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                     sw_fail_ordering_var, ContProcSet, 
                                     SwProcSet, swSeqChangedStatus, 
                                     controller2Switch, switch2Controller, 
                                     switchStatus, installedIRs, 
                                     NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                     Installer2OfaBuff, Ofa2InstallerBuff, 
                                     TCAM, controlMsgCounter, switchOrdering, 
                                     dependencyGraph, IR2SW, 
                                     idThreadWorkingOnIR, workerThreadRanking, 
                                     NIB2OFC, NIB2RC, OFC2NIB, RC2NIB, 
                                     masterState, controllerStateNIB, 
                                     SwSuspensionStatus, IRQueueNIB, 
                                     SetScheduledIRs, ingressPkt, ingressIR, 
                                     egressMsg, ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, failedSet, statusResolveMsg, 
                                     recoveredElem, toBeScheduledIRs, key, op1, 
                                     op2, transaction, nextIR, stepOfFailure_, 
                                     nextTrans, nextIRToSent, rowIndex, 
                                     rowRemove, stepOfFailure_c, 
                                     monitoringEvent, stepOfFailure, msg, 
                                     controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ controllerIsMaster(self[1])
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
                                                                   FirstInstall, 
                                                                   sw_fail_ordering_var, 
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   swSeqChangedStatus, 
                                                                   controller2Switch, 
                                                                   switch2Controller, 
                                                                   switchStatus, 
                                                                   installedIRs, 
                                                                   NicAsic2OfaBuff, 
                                                                   Ofa2NicAsicBuff, 
                                                                   Installer2OfaBuff, 
                                                                   Ofa2InstallerBuff, 
                                                                   TCAM, 
                                                                   controlMsgCounter, 
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   switchOrdering, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   NIB2OFC, 
                                                                   NIB2RC, 
                                                                   OFC2NIB, 
                                                                   RC2NIB, 
                                                                   masterState, 
                                                                   controllerStateNIB, 
                                                                   IRStatus, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
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
                                                                   key, op1, 
                                                                   op2, 
                                                                   transaction, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   nextTrans, 
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
                                       /\ controllerIsMaster(self[1])
                                       /\ moduleIsUp(self)
                                       /\ switch2Controller # <<>>
                                       /\ \/ controllerLock = self
                                          \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].from = IR2SW[msg'[self].IR], 
                                                 "Failure of assertion at line 1967, column 9.")
                                       /\ Assert(msg'[self].type \in {RECONCILIATION_RESPONSE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                 "Failure of assertion at line 1968, column 9.")
                                       /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIR2"]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 1998, column 18.")
                                                  /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                       /\ UNCHANGED << switchLock, 
                                                       FirstInstall, 
                                                       sw_fail_ordering_var, 
                                                       ContProcSet, SwProcSet, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       switchStatus, 
                                                       installedIRs, 
                                                       NicAsic2OfaBuff, 
                                                       Ofa2NicAsicBuff, 
                                                       Installer2OfaBuff, 
                                                       Ofa2InstallerBuff, TCAM, 
                                                       controlMsgCounter, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       switchOrdering, 
                                                       dependencyGraph, IR2SW, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       NIB2OFC, NIB2RC, 
                                                       OFC2NIB, RC2NIB, 
                                                       masterState, 
                                                       controllerStateNIB, 
                                                       IRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       toBeScheduledIRs, key, 
                                                       op1, op2, transaction, 
                                                       nextIR, stepOfFailure_, 
                                                       nextTrans, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, 
                                                       controllerFailedModules >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
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
                                               THEN /\ switch2Controller' = Tail(switch2Controller)
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                    /\ UNCHANGED switch2Controller
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         sw_fail_ordering_var, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         swSeqChangedStatus, 
                                                         controller2Switch, 
                                                         switchStatus, 
                                                         installedIRs, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Installer2OfaBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         switchOrdering, 
                                                         dependencyGraph, 
                                                         IR2SW, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         NIB2OFC, NIB2RC, 
                                                         OFC2NIB, RC2NIB, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, key, 
                                                         op1, op2, transaction, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         nextTrans, 
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
                                   THEN /\ FirstInstall' = [FirstInstall EXCEPT ![msg[self].IR] = 1]
                                        /\ IRStatus' = [IRStatus EXCEPT ![msg[self].IR] = IR_DONE]
                                        /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                        /\ UNCHANGED << FirstInstall, IRStatus >>
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, switchOrdering, 
                                             dependencyGraph, IR2SW, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, NIB2OFC, 
                                             NIB2RC, OFC2NIB, RC2NIB, 
                                             masterState, controllerStateNIB, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, key, op1, op2, 
                                             transaction, nextIR, 
                                             stepOfFailure_, nextTrans, 
                                             nextIRToSent, rowIndex, rowRemove, 
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
                                               "Failure of assertion at line 2035, column 13.")
                                     /\ controllerLock' = module
                                     /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![module] = NotFailed]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerWatchDogProc"]
                                /\ UNCHANGED << switchLock, FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                controllerSubmoduleFailNum, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, NIB2OFC, 
                                                NIB2RC, OFC2NIB, RC2NIB, 
                                                masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, key, op1, 
                                                op2, transaction, nextIR, 
                                                stepOfFailure_, nextTrans, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg >>

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
           \/ (\E self \in ({rc0} \X {CONT_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({nib0} \X {CONT_NIB_RC_EVENT}): NIBRCEventHandler(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))
           \/ (\E self \in ({ofc0, rc0} \X {WATCH_DOG}): watchDog(self))

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
        /\ \A self \in ({rc0} \X {CONT_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({nib0} \X {CONT_NIB_RC_EVENT}) : WF_vars(NIBRCEventHandler(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in ({ofc0, rc0} \X {WATCH_DOG}) : WF_vars(watchDog(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-453dc512c648f0a26be05b7d01ea061b
OperationsRanking == <<"ControllerSeqProc",
                      "SchedulerMechanism",
                      "SeqUpdateDBState1",
                      "AddToScheduleIRSet",
                      "ScheduleTheIR",
                      "SeqClearDBState",
                      "ControllerSeqStateReconciliation",
                      "ControllerThread",
                      "ControllerThreadSaveToDB1",
                      "ControllerThreadLockTheIRUsingSemaphore",
                      "ControllerThreadRemoveQueue1",
                      "ControllerThreadSendIR",
                      "ControllerThreadForwardIR",
                      "ControllerThreadSaveToDB2",
                      "WaitForIRToHaveCorrectStatus",
                      "ReScheduleifIRNone",
                      "ControllerThreadUnlockSemaphore",
                      "RemoveFromScheduledIRSet",
                      "ControllerThreadClearDB",
                      "ControllerThreadRemoveQueue2",
                      "ControllerThreadStateReconciliation",
                      "ControllerEventHandlerProc",
                      "ControllerSuspendSW",
                      "ControllerEventHandlerSaveToDB1",
                      "ControllerFreeSuspendedSW",
                      "ControllerCheckIfThisIsLastEvent",
                      "getIRsToBeChecked",
                      "ResetAllIRs",
                      "ControllerResetIRStatAfterRecovery",
                      "ControllerEventHandlerClearDB",
                      "ControllerEvenHanlderRemoveEventFromQueue",
                      "ControllerEventHandlerStateReconciliation",
                      "ControllerMonitorCheckIfMastr",
                      "ControllerUpdateIR2",
                      "MonitoringServerRemoveFromQueue",
                      "ControllerWatchDogProc">>
OperationIndex(name) == CHOOSE x \in 1..Len(OperationsRanking): OperationsRanking[x] = name
                      
OperationsVariableSet == [ControllerSeqProc |-> {"IRStatus", 
                                                 "SwSuspensionStatus", 
                                                 "SetScheduledIRs", 
                                                 "idThreadWorkingOnIR"}, 
                           SchedulerMechanism |-> {},
                           SeqUpdateDBState1 |-> {},
                           AddToScheduleIRSet |-> {"SetScheduledIRs"},
                           ScheduleTheIR |-> {"controllerThreadPoolIRQueue"},
                           SeqClearDBState |-> {},
                           ControllerSeqStateReconciliation |-> {"SetScheduledIRs"},
                           \*************************************************************************
                           ControllerThread |-> {"controllerThreadPoolIRQueue"},
                           ControllerThreadSaveToDB1 |-> {},
                           ControllerThreadLockTheIRUsingSemaphore |-> {"idThreadWorkingOnIR"},
                           ControllerThreadRemoveQueue1 |-> {"controllerThreadPoolIRQueue"},
                           ControllerThreadSendIR |-> {"SwSuspensionStatus",
                                                      "IRStatus"},
                           ControllerThreadForwardIR |-> {"controller2Switch"},
                           ControllerThreadSaveToDB2 |-> {},
                           WaitForIRToHaveCorrectStatus |-> {"SwSuspensionStatus"},
                           ReScheduleifIRNone |-> {"IRStatus"},
                           ControllerThreadUnlockSemaphore |-> {"idThreadWorkingOnIR"},
                           RemoveFromScheduledIRSet |-> {"SetScheduledIRs"},
                           ControllerThreadClearDB |-> {},
                           ControllerThreadRemoveQueue2 |-> {"controllerThreadPoolIRQueue"},
                           ControllerThreadStateReconciliation |-> {"IRStatus",
                                                                    "idThreadWorkingOnIR",
                                                                    "SetScheduledIRs"},
                           \*************************************************************************
                           ControllerEventHandlerProc |-> {"SwSuspensionStatus",
                                                           "swSeqChangedStatus"},
                           ControllerSuspendSW |-> {"SwSuspensionStatus"},
                           ControllerEventHandlerSaveToDB1 |-> {},
                           ControllerFreeSuspendedSW |-> {"SwSuspensionStatus"},
                           ControllerCheckIfThisIsLastEvent |-> {"swSeqChangedStatus"},
                           getIRsToBeChecked |-> {"IRStatus"},
                           ResetAllIRs |-> {},
                           ControllerResetIRStatAfterRecovery |-> {"IRStatus"},
                           ControllerEventHandlerClearDB |-> {},
                           ControllerEvenHanlderRemoveEventFromQueue |-> {"swSeqChangedStatus"},
                           ControllerEventHandlerStateReconciliation |-> {"SwSuspensionStatus"},
                           \*************************************************************************
                           ControllerMonitorCheckIfMastr |-> {"switch2Controller"},
                           ControllerUpdateIR2 |-> {"IRStatus"},
                           MonitoringServerRemoveFromQueue |-> {"switch2Controller"},
                           ControllerWatchDogProc |-> {"controllerStatus",
                                                       "controllerLock"}]

\* Liveness Properties
AllInstalled == (\A x \in 1..MaxNumIRs: \E y \in DOMAIN installedIRs: installedIRs[y] = x)
AllDoneStatusController == (\A x \in 1..MaxNumIRs: IRStatus[x] = IR_DONE)
InstallationLivenessProp == <>[] (/\ AllInstalled 
                                  /\ AllDoneStatusController)
\* Safety Properties
IRCriticalSection == LET 
                        IRCriticalSet == {"ControllerThreadSendIR", "ControllerThreadForwardIR", "ControllerThreadSaveToDB2", "WaitForIRToHaveCorrectStatus", "ReScheduleifIRNone"}
                     IN   
                        \A x, y \in {ofc0} \X CONTROLLER_THREAD_POOL: \/ x = y
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
\* Last modified Sun Feb 21 23:36:21 PST 2021 by zmy
\* Last modified Sun Feb 14 21:50:09 PST 2021 by root
\* Created Thu Nov 19 19:02:15 PST 2020 by root

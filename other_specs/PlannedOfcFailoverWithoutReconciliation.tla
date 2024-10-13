-------------- MODULE PlannedOfcFailoverWithoutReconciliation --------------
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
(*  + NIB Event Handler: responsible for handling notifications fron NIB   *)
(*          and making necessary changes to NIB (including failover)       *)
(*  + Watchdog: in case of detecting failure in each of the above          *)
(*          processes, it restarts the process                             *)
(*       each of these modules execpt Watchdog can fail independently      *)
(***************************************************************************)
(***************************************************************************)
CONSTANTS ofc0, \* OFC thread identifiers
          ofc1
          
(***************************************************************************)
(******************************** RC Model *********************************)
(* At the high level RCS consists of 2 submodules;                         *)
(*  + Sequencer: it is responsible for sequencing the instructions given   *)
(*          the DAG as input                                               *)
(*  + Watchdog: same as Watchdog in OFC                                    *)
(*       each of these modules execpt Watchdog can fail independently      *)
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
          NIB_EVENT_HANDLER
          \* id for NIB event handler (type: model value)
          
(***************************************************************************)
(************************ OFC Failver **************************************)
(***************************************************************************)
CONSTANTS OFC_FAILOVER,
          \* id for ofc failover (type: model value)
          SHOULD_FAILOVER,
          \* 0-1 value to decide whether failover must happend or not
          FAILOVER_INIT,
          FAILOVER_READY,
          FAILOVER_TERMINATE,
          TERMINATE_NONE,
          TERMINATE_INIT,
          TERMINATE_DONE, 
          FAILOVER_TERMINATE_DONE,
          FAILOVER_NONE
          
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
          INSTALLED_SUCCESSFULLY, 
          KEEP_ALIVE,
          STATUS_NONE,
          BAD_REQUEST,
          ROLE_REQ,
          ROLE_TYPE, 
          ROLE_REPLY,
          FLOW_STAT_REQ 
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
(************************** CONTROLLER ROLE STATUS *************************)
(***************************************************************************)
CONSTANTS ROLE_SLAVE,   
          ROLE_MASTER,
          ROLE_EQUAL
                                   
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
          MAX_NUM_IRs,
          MAX_NUM_SW_FAILURE,
          SW_FAIL_ORDERING

    
CONSTANTS SW_UP, SW_DOWN          
          
(* Assumption1: at most one instruction is associated with one switch *)
ASSUME Cardinality(SW) >= MAX_NUM_IRs          
(* Assumption2: all the switches appear in the failure ordering *)
ASSUME \A x \in SW: \E y \in DOMAIN SW_FAIL_ORDERING: x \in SW_FAIL_ORDERING[y]
(* Assumption3: MAX_NUM_CONTROLLER_SUB_FAILURE is a function from control plane *)
(* modules (e.g. OFC, RC) to maximum number of submodule failure each can face *)
ASSUME {"ofc0", "ofc1", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE          
(* SHOULD_FAILOVER should be either 0 or 1 *)
ASSUME SHOULD_FAILOVER \in {0, 1}
(* WHICH_SWITCH_MODEL should be a valid function with domain SW *)
ASSUME WHICH_SWITCH_MODEL \in [SW -> {SW_SIMPLE_MODEL, SW_COMPLEX_MODEL}]

(*--fair algorithm stateConsistency
(************************* variables ***************************************)
    variables (*************** Some Auxiliary Vars ***********************)
              switchLock = <<NO_LOCK, NO_LOCK>>,
              controllerLock = <<NO_LOCK, NO_LOCK>>, 
              FirstInstall = [x \in 1..MAX_NUM_IRs |-> 0],
              sw_fail_ordering_var = SW_FAIL_ORDERING,
              ContProcSet = (({rc0} \X {CONT_SEQ})) \cup (({ofc0, ofc1} \X CONTROLLER_THREAD_POOL)) 
                            \cup (({ofc0, ofc1} \X {CONT_EVENT})) \cup (({ofc0, ofc1} \X {CONT_MONITOR})),
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
              swSeqChangedStatus = [x \in {ofc0, ofc1} |-> <<>>],             
              
              \* controller2Switch used by OFC workers to send instructions
              \* to the switch
              controller2Switch = [x\in SW |-> <<>>],
              
              \* switch2controller used by switch to communicate with OFC
              \* (monitoring server)
              switch2Controller = [x \in {ofc0, ofc1} |-> <<>>],
              
              (******************** Switch Vars **************************)
              \* Initially all the modules are working properly
              switchStatus = [x\in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed, 
                              ofa |-> NotFailed, installer |-> NotFailed]],  
              
              \* installedIRs is an ordered set of all the IRs installed accross
              \* all the switches (used for checking consistency invariance)
              installedIRs = <<>>,
              
              \* installedBy is a mapping from IR to the OFC who installed the 
              \* IR, used for checking the invariance (each IR should be 
              \* installed by at most one OFC)
              installedBy = [x \in 1..MAX_NUM_IRs |-> {}],
              
              \* auxiliary variable to make sure each switch fails at most
              \* MAX_NUM_SW_FAILURE times
              swFailedNum = [x \in SW |-> 0],
              
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
              
              \* controller status in switch
              switchControllerRoleStatus = [x \in SW |-> (ofc0 :> ROLE_MASTER @@ ofc1 :> ROLE_SLAVE)],
              
              (*********************** Controller *************************)
              controllerSubmoduleFailNum = [x \in ({ofc0, ofc1} \cup {rc0}) |-> 0],
              controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed],
              
              (*********************** RC Vars ****************************)
              \**************** Dependency Graph Definition ***********
              \* DAG is normally an input to the sequencer, however, here
              \* we check for all the possible non-isomorphic DAGs to make
              \* sure it works for all combinations
              switchOrdering = CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z],
              \* dependencyGraph \in PlausibleDependencySet,
              dependencyGraph \in generateConnectedDAG(1..MAX_NUM_IRs),              
              IR2SW = CHOOSE x \in [1..MAX_NUM_IRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z 
                                                                                /\ switchOrdering[x[y]] =< switchOrdering[x[z]],
              
              (********************** OFC Vars ****************************)
              \************** Workers ******************** 
              \* irCounter is an indexing method used to synchronization
              \* between workers. Each IR is assigned an index and based
              \* on this index each worker would know whether the IR is 
              \* locked by another worker or not. 
              irCounter = 0, 
              MAX_IR_COUNTER = 15, 
              \* idThreadWorkingOnIR is a logical semaphore used for 
              \* synchronization between IRs
              idThreadWorkingOnIR = [y \in {ofc0, ofc1} |-> [x \in 1..MAX_IR_COUNTER |-> IR_UNLOCK]],
              \* WorkerThreadRanking is an auxiliary variable used for 
              \* reducing the number of possible behaviours by applying
              \* the following rule; if two workers try to get the lock 
              \* for an IR, the one with lower ranking always gets it.
              workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
              \* local IR Queue for workers
              workerLocalQueue = [x \in {ofc0, ofc1} |-> <<>>],
              
              \************* NIB Event Handler ************
              \* this is what OFC thinks its role is in the switch 
              controllerRoleInSW = (ofc0 :> [x \in SW |-> ROLE_MASTER]) @@ (ofc1 :> [x \in SW |-> ROLE_SLAVE]),
              \* queue of notifications received from NIB
              nibEventQueue = [x \in {ofc0, ofc1} |-> <<>>],
              \* keeps track of role update messages' cycle
              roleUpdateStatus = [x \in {ofc0, ofc1} |-> [y \in SW |-> IR_NONE]],
              \* each OFC module except NIB event handler starts working when isOfcEnabled is TRUE
              isOfcEnabled = [x \in {ofc0} |-> TRUE] @@ [x \in {ofc1} |-> FALSE],
              \* used for synchronization between NIB event handler scheduled role update msg and workers
              setScheduledRoleUpdates = [x \in {ofc0, ofc1} |-> {}],
              \* ofcModuleTerminationStatus used for graceful termination of OFC modules
              ofcModuleTerminationStatus = [x \in {ofc0, ofc1} |-> 
                                                [y \in ({CONT_MONITOR, CONT_EVENT} \cup CONTROLLER_THREAD_POOL) |-> TERMINATE_NONE]],
              
              (********************* NIB Vars *****************************)
              \* indicates which module is elected as the holder of the lock 
              masterState = (ofc0 :> ROLE_MASTER @@ ofc1 :> ROLE_SLAVE @@ rc0 :> ROLE_MASTER),
              \* used for reconciliation after module failure (controller partial failure)
              controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]],
              \* keeps track of IR cycle
              IRStatus = [x \in 1..MAX_NUM_IRs |-> IR_NONE],
              \* used by topology event handler to inform rest of system about topology change  
              SwSuspensionStatus = [x \in SW |-> SW_RUN],
              \* IR Queue filled by the sequencer in OFC
              IRQueueNIB = <<>>,
              \* list of subscribers of NIB
              subscribeList = [IRQueueNIB |-> {ofc0}], 
              \* used for synchronization between sequencer and workers
              SetScheduledIRs = [y \in SW |-> {}],\* @Pooria, consider moving this variable to RC
              \* status of OFC failover in NIB
              ofcFailoverStateNIB = [y \in {ofc0, ofc1} |-> FAILOVER_NONE]
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
                                                                                             allSizes \in AllPossibleSizes(MAX_NUM_IRs, MAX_NUM_IRs)} 
                
        (****************** Used by system logic *****************************)
        
        (***************************** Switch ********************************)                                  
        whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID]
        
        \***************************** NIC/ASIC ******************************
        swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed 
        
        \***************************** OFA **********************************
        swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                                  /\ switchStatus[sw].ofa = NotFailed
        getMasterController(swID) == CHOOSE x \in DOMAIN switchControllerRoleStatus[swID]:
                                                        switchControllerRoleStatus[swID][x] = ROLE_MASTER
        isControllerMaster(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_MASTER
        isControllerSlave(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_SLAVE
        hasModificationAccess(swID, cid) == ~isControllerSlave(swID, cid)
        \**************************** Installer *****************************
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
                               
        \*************************** switch failure process *****************
        returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}
        \* getSetIRsForSwitch is for verification optimization reasons
        getSetIRsForSwitch(SID) == {x \in 1..MAX_NUM_IRs: IR2SW[x] = SID}
        
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
        controllerIsMaster(controllerID) == masterState[controllerID] = ROLE_MASTER
        getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                                     [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0 
                                                     [] controllerID = ofc1 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc1
        
        (************************** Tagged Buff *****************************)
        \* The following four expression help using tagged buffer
        \* Please see modifiedRead, modifiedWrite, modifiedRemove
        isIdenticalElement(itemA, itemB) == \A x \in DOMAIN itemA: /\ x \in DOMAIN itemB
                                                                   /\ itemA[x] = itemB[x]
        NoEntryTaggedWith(buff, threadID) == ~\E x \in rangeSeq(buff): x.tag = threadID 
        FirstUntaggedEntry(buff, num) == ~\E x \in DOMAIN buff: /\ buff[x].tag = NO_TAG
                                                                /\ x < num
        getFirstIRIndexToRead(buff, threadID) == CHOOSE x \in DOMAIN buff: \/ buff[x].tag = threadID
                                                                           \/ /\ NoEntryTaggedWith(buff, threadID)
                                                                              /\ FirstUntaggedEntry(buff, x)
                                                                              /\ buff[x].tag = NO_TAG
        getFirstIndexWith(buff, item, threadID) == CHOOSE x \in DOMAIN buff: /\ buff[x].tag = threadID
                                                                             /\ isIdenticalElement(buff[x].item, item)
        existEquivalentItemWithID(buff, item) == \E x \in rangeSeq(buff): /\ isIdenticalElement(item, x)
                                                                          /\ x.id # -1 
        existsEquivalentItem(buff, item) == \E x \in rangeSeq(buff): isIdenticalElement(item, x)
        setEquivalentItems(buff, item) == {y \in rangeSeq(buff): isIdenticalElement(y, item)} 
        getIdOfEquivalentItem(buff, item) == CHOOSE i \in {x.id: x \in setEquivalentItems(buff, item)}:TRUE
                                                                   
        (****************** RC (routing controller) **************************)
        \*************************** Sequencer *******************************
        isDependencySatisfied(ir) == ~\E y \in 1..MAX_NUM_IRs: /\ <<y, ir>> \in dependencyGraph
                                                             /\ IRStatus[y] # IR_DONE
        getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MAX_NUM_IRs: /\ IRStatus[x] = IR_NONE
                                                                  /\ isDependencySatisfied(x)
                                                                  /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRs[IR2SW[x]]}
                                                                  \*/\ idThreadWorkingOnIR[x] = IR_UNLOCK}
                                                                  
        (****************** OFC (openflow controller) ************************)
        shouldWorkerTerminate(CID, TID) == ofcModuleTerminationStatus[CID][TID] = TERMINATE_INIT 
        shouldEventHandlerTerminate(CID) == ofcModuleTerminationStatus[CID][CONT_EVENT] = TERMINATE_INIT
        shouldMonitoringServerTerminate(CID) == /\ ofcModuleTerminationStatus[CID][CONT_MONITOR] = TERMINATE_INIT
                                                /\ ~\E x \in 1..MAX_NUM_IRs: IRStatus[x] = IR_SENT
        \********************** NIB Event Handler ****************************
        allSwitchInEqualRole(CID) == \A x \in SW: controllerRoleInSW[CID][x] = ROLE_EQUAL
        getSetSwitchInSlaveRole(CID) == {x \in SW: controllerRoleInSW[CID][x] = ROLE_SLAVE}
        getSetSwitchInEqualRole(CID) == {x \in SW: /\ controllerRoleInSW[CID][x] = ROLE_EQUAL
                                                   /\ x \notin setScheduledRoleUpdates[CID]}
        allModulesTerminated(CID) == \A x \in DOMAIN ofcModuleTerminationStatus[CID]: 
                                                        ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE
        allWorkersTerminated(CID) == \A x \in CONTROLLER_THREAD_POOL: 
                                                        ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE
                                                        
        \*************************** Workers *********************************
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        \* following expressions used for verification optimization reasons
        \* between all the threads attempting to get the IR, the one with lowest 
        \* id always gets it. 
        setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(workerLocalQueue[CID], <<CID, y>>)
                                                              /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}        
        canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(workerLocalQueue[CID]): x.tag = threadID
                                                  \/ /\ \E x \in rangeSeq(workerLocalQueue[CID]): x.tag = NO_TAG 
                                                     /\ NoEntryTaggedWith(workerLocalQueue[CID], threadID) 
                                                     /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
        setThreadsAttemptingForLock(CID, item, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ isIdenticalElement(y.item, item)
                                                                                                                         /\ y.tag = <<CID, x>>
                                                                                          /\ pc[<<CID, x>>] = "ControllerThread"}
        threadWithLowerIDGetsTheLock(CID, threadID, item, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: 
                                                                                                                z \in setThreadsAttemptingForLock(CID, item, IRQueue)}) 
        workerCanSendTheIR(CID, nextToSent) == /\ ~isSwitchSuspended(nextToSent.to)
                                               /\ \/ /\ nextToSent.type = ROLE_REQ
                                                     /\ roleUpdateStatus[CID][nextToSent.to] = IR_NONE
                                                  \/ /\ nextToSent.type = INSTALL_FLOW
                                                     /\ IRStatus[nextToSent.IR] = IR_NONE
        workerShouldFastRecovery(CID, nextToSent) == \/ /\ nextToSent.type = ROLE_REQ
                                                        /\ roleUpdateStatus[CID][nextToSent.to] = IR_NONE
                                                     \/ /\ nextToSent.type = INSTALL_FLOW
                                                        /\ IRStatus[nextToSent.IR] = IR_NONE
        
        \*************************** EventHandler ****************************       
        existsMonitoringEventHigherNum(monEvent, tid) == \E x \in DOMAIN swSeqChangedStatus[tid]: /\ swSeqChangedStatus[tid][x].swID = monEvent.swID
                                                                                                 /\ swSeqChangedStatus[tid][x].num > monEvent.num
        shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                                     \/ monEvent.type = NIC_ASIC_DOWN
                                     \/ /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.status.installerStatus = INSTALLER_DOWN
        canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                        /\ monEvent.status.installerStatus = INSTALLER_UP
        \* getIRSetToReconcile(SID) == {x \in 1..MAX_NUM_IRs: /\ IR2SW[x] = SID
        \*                                                 /\ IRStatus[x] \notin {IR_DONE, IR_NONE, IR_SUSPEND}}
        getIRSetToReset(SID) == {x \in 1..MAX_NUM_IRs: /\ IR2SW[x] = SID
                                                     /\ IRStatus[x] \notin {IR_DONE, IR_NONE}}
        \* getIRSetToSuspend(CID, SID) == {x \in SetScheduledIRs[SID]: IRStatus[x] = IR_NONE}           
                                                                             
        \*************************** Monitoring Server **********************
        
        \*************************** Watchdog *******************************
        returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                                   /\ controllerSubmoduleFailStat[x] = Failed}
                                                                                                                                                                          
        (***************** SystemWide Check **********************************)        
        isFinished == \A x \in 1..MAX_NUM_IRs: IRStatus[x] = IR_DONE
                                                                                                                
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
    
    macro increment(value, mod)
    begin
        value := (value + 1) % mod;
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
        swFailedNum[self[2]] := swFailedNum[self[2]] + 1;
        controller2Switch[self[2]] := <<>>;
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
        statusMsg := [type |-> NIC_ASIC_DOWN, 
                      swID |-> self[2],
                      num |-> controlMsgCounter[self[2]]];
        swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);              
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
        swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);            
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
        swFailedNum[self[2]] := swFailedNum[self[2]] + 1;
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
            swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);
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
            swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);    
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
        swFailedNum[self[2]] := swFailedNum[self[2]] + 1;       
        \*OfaCacheReceived[self[2]] := {};
        \*OfaCacheInstalled[self[2]] := {};
        if switchStatus[self[2]].nicAsic = NotFailed then  
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
            statusMsg := [type |-> OFA_DOWN, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]]];
            swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);    
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
            
            swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);             
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
        swFailedNum[self[2]] := swFailedNum[self[2]] + 1;        
        if switchStatus[self[2]].nicAsic = NotFailed /\ switchStatus[self[2]].ofa = NotFailed then
            assert switchStatus[self[2]].installer = Failed;
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;    
            statusMsg := [type |-> KEEP_ALIVE, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]],
                          status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)]];
            swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);
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
            swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);    
        end if;
    end macro
    \* =================================
    
    \* === Send BAD REQUEST ERROR ======
    \* this is when switch receives a flow mod pkt from slave controller
    macro sendBadReqError(controllerID, irID)
    begin
        Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> BAD_REQUEST,
                                                                      from |-> self[2],
                                                                      to |-> controllerID, 
                                                                      IR |-> irID]);
    end macro
    \* =================================
    
    \* === SEND ROLE REPLY Msg =========
    \* when switch successfully updates the status of the controller
    macro sendRoleReply(controllerID, newRole)
    begin
        Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> ROLE_REPLY,
                                                                      from |-> self[2],
                                                                      roletype |-> newRole,
                                                                      to |-> controllerID]);    
    end macro
    \* =================================
    
    \* ==== UPDATE ROLE ================
    macro updateRole(controllerID, newRole)
    begin
        if newRole = ROLE_MASTER then
            if getMasterController(self[2]) # controllerID then
                switchControllerRoleStatus[self[2]][getMasterController(self[2])] := ROLE_SLAVE ||
                    switchControllerRoleStatus[self[2]][controllerID] := ROLE_MASTER        
            end if;
        else
            switchControllerRoleStatus[self[2]][controllerID] := newRole
        end if;
    end macro
    \* =================================
    
    \* ==== Install IR to TCAM =========
    macro installToTCAM(controllerID, newIR)
    begin
        installedIRs := Append(installedIRs, newIR);
        installedBy[newIR] := installedBy[newIR] \cup {controllerID}; 
        TCAM[self[2]] := Append(TCAM[self[2]], newIR);
    end macro
    \* =================================
           
    \* == Acknowledge the Installaiton =
    macro sendConfirmation(controllerID, irID)
    begin
        Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                      from |-> self[2],
                                                                      to |-> controllerID,
                                                                      IR |-> irID]);
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
        await \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
              \/ switchLock[2] = self[2];
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
    
    \* ===== Controller Acquire Lock ===
    macro controllerAcquireLock(newLockHolder)
    begin
        controllerWaitForLockFree();
        controllerLock := newLockHolder;
    end macro
    \* =================================
    
    \* ==== controller release Lock ====
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
    macro controllerSendIR(nextIR)
    begin
        \* this macro mimics all the sending function;
        \* 1. append the message to the OpenFlow channel between controller and switch
        \* 2. give the lock of the system to the switch. 
        if nextIR.type = INSTALL_FLOW then 
            controller2Switch[nextIR.to] := Append(controller2Switch[nextIR.to], [type |-> INSTALL_FLOW,
                                                                                  from |-> self[1],
                                                                                  to |-> nextIR.to,
                                                                                  IR |-> nextIR.IR]);
        elsif nextIR.type = ROLE_REQ then
            controller2Switch[nextIR.to] := Append(controller2Switch[nextIR.to], [type |-> ROLE_REQ,
                                                                                  from |-> self[1],
                                                                                  to |-> nextIR.to,
                                                                                  roletype |-> nextIR.roletype]); 
        end if;
        if whichSwitchModel(nextIR.to) = SW_COMPLEX_MODEL then 
            switchLock := <<NIC_ASIC_IN, nextIR.to>>;
        else
            switchLock := <<SW_SIMPLE_ID, nextIR.to>>;
        end if;
    end macro;
    \* =================================
    
    \* ===== OFC module terminate =====
    macro ofcModuleTerminate()
    begin 
        ofcModuleTerminationStatus[self[1]][self[2]] := TERMINATE_DONE;
        goto Done;
    end macro;
    \* ================================
                  
    \* ========= Tagged Buffer ==========
    macro getIdForNewItem(buff, item, id)
    begin
        if existEquivalentItemWithID(buff, item) then
            id := getIdOfEquivalentItem(buff, item);        
        else
            increment(irCounter, MAX_IR_COUNTER);
            id := irCounter;
        end if;
    end macro
                                        
    macro modifiedEnqueue(buff, item)
    begin
        buff := Append(buff, [item |-> item, id |-> -1, tag |-> NO_TAG]);
    end macro;
    
    macro modifiedRead(buff, output, entryIndex)
    begin
        rowIndex := getFirstIRIndexToRead(buff, self);
        output := buff[rowIndex].item;
        getIdForNewItem(buff, output, entryIndex);
        buff[rowIndex].tag := self || buff[rowIndex].id := entryIndex;
    end macro;
    
    macro modifiedRemove(buff, item)
    begin
        rowRemove := getFirstIndexWith(buff, item, self);
        buff := removeFromSeq(buff, rowRemove);
    end macro;
    \* =================================
    
    \* ======== Normal Buffer ==========
    macro enqueue(buff, item)
    begin
        buff := Append(buff, item);    
    end macro
    
    macro read(buff, output)
    begin
        output := Head(buff);
    end macro
    
    macro dequeue(buff, output)
    begin
        output := Head(buff);
        buff := Tail(buff);
    end macro
    
    macro remove(buff)
    begin
        buff := Tail(buff);
    end macro
    
    macro removeItem(buff, item)
    begin
        if existsEquivalentItem(buff, item) then
            removeRow := CHOOSE x \in DOMAIN buff: isIdenticalElement(buff[x], item);
            buff := removeFromSeq(buff, rowRemove);
        end if;
    end macro
    \* ================================
    
    (*******************************************************************)
    (*                     Switches SIMPLE Model                       *)
    (*******************************************************************)
    \* This is the simplest switch model that does all the following
    \* in one atomic operation
    \* 1. unpack the received packet
    \*      1.1. install the IR if INSTALL_FLOW from a non-slave controller
    \*      1.2. update the role if ROLE_REQ
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
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        assert ingressPkt.type \in {INSTALL_FLOW, ROLE_REQ, FLOW_STAT_REQ};
        if ingressPkt.type = INSTALL_FLOW then 
            if hasModificationAccess(self[2], ingressPkt.from) then
                installToTCAM(ingressPkt.from, ingressPkt.IR);
                sendConfirmation(getMasterController(self[2]), ingressPkt.IR); 
            else 
                sendBadReqError(ofaInMsg.from, ofaInMsg.IR);     
            end if;
        elsif ingressPkt.type = ROLE_REQ then
            \* when role request is received
            assert ingressPkt.roletype \in {ROLE_MASTER, ROLE_SLAVE, ROLE_EQUAL};
            updateRole(ingressPkt.from, ingressPkt.roletype);
            sendRoleReply(ingressPkt.from, ingressPkt.roletype)
            
        elsif ingressPkt.type = FLOW_STAT_REQ then
            \* TODO(@Pooria)
            skip; 
        end if;
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
        assert ingressIR.type \in {ROLE_REQ, INSTALL_FLOW};
        
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
        assert egressMsg.type \in {INSTALLED_SUCCESSFULLY, ROLE_REPLY, BAD_REQUEST};
        Ofa2NicAsicBuff[self[2]] := Tail(Ofa2NicAsicBuff[self[2]]);
        
        \* Step 2: send the packet to the destination (controller)
        SwitchNicAsicSendOutMsg:
            if swCanReceivePackets(self[2]) then
                switchWaitForLock();
                releaseLock(self);
                switch2Controller[egressMsg.to] := Append(switch2Controller[egressMsg.to], egressMsg);
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
        \* TODO(@Pooria): switch should not necessarily process the packet in order
        \* Step 1: Pick the first packet from buffer, process and extract the IR
        await swOFACanProcessIRs(self[2]);
        await Len(NicAsic2OfaBuff[self[2]]) > 0;
        acquireLock();
        ofaInMsg := Head(NicAsic2OfaBuff[self[2]]);           
        assert ofaInMsg.to = self[2];
        assert \/ /\ ofaInMsg.type = ROLE_REQ
                  /\ ofaInMsg.roletype \in {ROLE_SLAVE, ROLE_MASTER, ROLE_EQUAL}
               \/ /\ ofaInMsg.type = INSTALL_FLOW
                  /\ ofaInMsg.IR  \in 1..MAX_NUM_IRs;
        assert ofaInMsg.from \in {ofc0, ofc1};
        NicAsic2OfaBuff[self[2]] := Tail(NicAsic2OfaBuff[self[2]]);
        
        \* Step 2: 
        \*   2.1. if it is INSTALL_FLOW from master controller, append it to the switch
        \*   2.2. if it is INSTALL_FLOW from slave controller, return an error
        \*   2.3. if it is ROLE_UPDATE_REQ msg, update the role and send necessary role update message
        \*   2.4. if it is FLOW_STAT_REQ msg, 
        SwitchOfaProcessPacket:
           if swOFACanProcessIRs(self[2]) then
                
                assert ofaInMsg.type \in {INSTALL_FLOW, ROLE_REQ};
                
                if ofaInMsg.type = INSTALL_FLOW then
                    if hasModificationAccess(self[2], ofaInMsg.from) then 
                        \* 2.1. When IR from master
                        acquireAndChangeLock(<<INSTALLER, self[2]>>);
                    
                        Ofa2InstallerBuff[self[2]] := Append(Ofa2InstallerBuff[self[2]], 
                                                                  [IR |-> ofaInMsg.IR, 
                                                                  from |-> ofaInMsg.from]);
                    else 
                        \* 2.2. when IR from slave
                        acquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                        sendBadReqError(ofaInMsg.from, ofaInMsg.IR);        
                    end if;
                    
                elsif ofaInMsg.type = ROLE_REQ then
                    \* 2.3. Switch upon receiving ROLE_REQ massage must change the role of the controller to the 
                    \* desired role. After successfully changing the role, it should reply with ROLE_REPLY and 
                    \* if status of other controllers has changed, switch should inform them with ROLE_STATUS msg.
                    \* One example for such a situation is where a controller which was previously
                    \* the master is now an slave as a result of another controller changing its role to master
                    
                    \* TODO(Pooria) skipped the ROLE_STATUS part
                    assert ofaInMsg.roletype \in {ROLE_MASTER, ROLE_SLAVE, ROLE_EQUAL};
                    acquireLock();
                    updateRole(ofaInMsg.from, ofaInMsg.roletype);
                        
                    SwitchSendRoleReply:
                        acquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                        sendRoleReply(ofaInMsg.from, ofaInMsg.roletype); 
                       
                elsif ofaInMsg.type = FLOW_STAT_REQ then
                    \* 2.4. @TODO(Pooria) should complete this.  
                    skip;
                end if;
           else
                ofaInMsg := [type |-> 0];
                goto SwitchOfaProcIn;
           end if;
    end while    
    end process
    
    fair process ofaModuleProcPacketOut \in ({OFA_OUT} \X SW)
    variables ofaOutConfirmation = [type |-> 0]
    begin
    SwitchOfaProcOut:
    while TRUE do
    
        \* Step 1: pick the first confirmation from installer
        await swOFACanProcessIRs(self[2]);
        await Installer2OfaBuff[self[2]] # <<>>;
        acquireLock();
        ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
        Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
        assert ofaOutConfirmation.IR \in 1..MAX_NUM_IRs;
        
        \* Step 2: prepare an installation confirmation message and send it to the controller
        \* through the NIC/ASIC
        SendInstallationConfirmation:
            if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                \* Should only send back confirmation if IR is from the controller 
                \* who is currently  the master or equal role. otherwise, should send BadRequest.
                \* This is a simplification of Barrier in OpenFlow.
                if hasModificationAccess(self[2], ofaOutConfirmation.from) then 
                    sendConfirmation(ofaOutConfirmation.from, ofaOutConfirmation.IR); 
                else
                    sendBadReqError(ofaOutConfirmation.from, ofaOutConfirmation.IR);        
                end if;      
            else 
                ofaOutConfirmation := [type |-> 0];
                goto SwitchOfaProcOut;
            end if;                                                              
    end while;                                                                      
    end process
    \* =================================
    
    \* ======= Installer Module ========
    \* installer only has one process that installs the IR and sends back the feedback to the OFC
    fair process installerModuleProc \in ({INSTALLER} \X SW)
    variables installerInIR = [type |-> 0]
    begin
    SwitchInstallerProc: 
    while TRUE do
       
       \* Step 1: pick the first instruction from the input buffer      
       await swCanInstallIRs(self[2]);
       await Len(Ofa2InstallerBuff[self[2]]) > 0;
       acquireLock();
       installerInIR := Head(Ofa2InstallerBuff[self[2]]);
       assert installerInIR.IR \in 1..MAX_NUM_IRs;
       Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);
       
       \* Step 2: install the IR to the TCAM
       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then
                acquireLock();
                installToTCAM(installerInIR.from, installerInIR.IR);   
            else
                installerInIR := [type |-> 0];
                goto SwitchInstallerProc;
            end if;
            
       \* Step 3: send the confirmation to the OFA
       SwitchInstallerSendConfirmation:
            if swCanInstallIRs(self[2]) then
                acquireAndChangeLock(<<OFA_OUT, self[2]>>);
                Installer2OfaBuff[self[2]] := Append(Installer2OfaBuff[self[2]], installerInIR);
            else
                installerInIR := [type |-> 0];
                goto SwitchInstallerProc;
            end if;
    end while;
    end process
    \* =================================
    
    \* ======= Failure Proccess=========
    fair process swFailureProc \in ({SW_FAILURE_PROC} \X SW)
    variable statusMsg = [type |-> 0], notFailedSet = {}, failedElem = "";
    \* TODO(@Pooria): should send status msg to every switch
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
        await swFailedNum[self[2]] < MAX_NUM_SW_FAILURE;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                 \/ switchLock[2] = self[2];
        await \E x \in getSetIRsForSwitch(self[2]): IRStatus[x] # IR_DONE;
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
    variable failedSet = {}, statusResolveMsg = [type |-> 0], recoveredElem = "";
    \* TODO(@Pooria): should send status msg to every switch
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
   
    \* ============ Sequencer ==========
    \* Sequencer periodically gets all the valid IRs (those with satisfied
    \* dependencies), run its scheduling mechanism to decide the order of
    \* scheduling and then, schedule the IR
    fair process controllerSequencer \in ({rc0} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}, nextIR = 0, stepOfFailure = 0, 
              subscriberOfcSet = {}, ofcID = 0;
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
            whichStepToFail(3);
            if (stepOfFailure # 1) then
                \* Step 1: choosing one IR from the valid set
                nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                if (stepOfFailure # 2) then
                    \* Step 2: updating state on NIB
                    controllerStateNIB[self] := [type |-> STATUS_START_SCHEDULING, next |-> nextIR];
                    if (stepOfFailure # 3) then  
                        \* Step 3: adding to scheduled set
                        SetScheduledIRs[IR2SW[nextIR]] := SetScheduledIRs[IR2SW[nextIR]] \cup {nextIR};                    
                    end if;
                end if;
            end if;
            
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
                    enqueue(IRQueueNIB, [type |-> INSTALL_FLOW, to |-> IR2SW[nextIR], IR |-> nextIR]);
                    \* Instead of NIB generating notification for change in IRQueueNIB
                    \* for simplicity, Sequencer generates the notification
                    subscriberOfcSet := subscribeList.IRQueueNIB; 
                    sendIRQueueModNotification: \* TODO(@Pooria): Optimize here. Unnecessary labeling.
                        while subscriberOfcSet # {} do
                            ofcID := CHOOSE x \in subscriberOfcSet: TRUE;
                            subscriberOfcSet := subscriberOfcSet \ {ofcID};                            
                            enqueue(nibEventQueue[ofcID], [type |-> INSTALL_FLOW, 
                                                           to |-> IR2SW[nextIR], 
                                                           IR |-> nextIR]);
                        end while;
                    
                    toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                    if (stepOfFailure # 2) then
                        \* step 2: clear the state on NIB  
                        controllerStateNIB[self] := [type |-> NO_STATUS];    
                    end if;
                end if;
                
                sequencerApplyFailure: \* TODO(@Pooria): Optimize here. Unnecessary labeling.
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
    \* ========================== 
    
    (*******************************************************************)
    (*                     OFC (OpenFlow Controller)                   *)
    (*******************************************************************)
    \* === NIB Event Handler ====
    \* TODO (@Pooria): consider NIB event handler failure (watch dog)
    fair process nibEventHandler \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER})
    variables event=[type |-> 0], swSet = {}, currSW = 0, 
              IRQueueEntries = [type |-> 0], entry = [type |-> 0];
    begin
    NibEventHandlerProc:
        while TRUE do
            await \/ ofcFailoverStateNIB[self[1]] \in {FAILOVER_INIT, FAILOVER_TERMINATE}
                  \/ /\ masterState[self[1]] = ROLE_MASTER
                     /\ nibEventQueue[self[1]] # <<>>
                  \/ /\ masterState[self[1]] = ROLE_MASTER
                     /\ getSetSwitchInEqualRole(self[1]) # {};
            
            \* if NIB event handler receives notification about its failover status FAILOVER_INIT
            \* it should perform necessary actions to be ready to takeover the OFC reponsibilities;
            \* 1) update its role to ROLE_EQUAL in all the switches
            \* 2) reconcile its local worker queue with NIB IR queue
            \* 3) subscribe to NIB IR Queue
            \* 4) change its failover status to FAILOVER_READY
            if ofcFailoverStateNIB[self[1]] = FAILOVER_INIT then 
                \* Step 1. update role to ROLE_EQUAL in all the switches
            
                \* controllerAcquireLock(self);
                isOfcEnabled[self[1]] := TRUE; \* This is for optimization
                swSet := getSetSwitchInSlaveRole(self[1]);
            
                ScheduleRoleUpdateEqual:
                    while TRUE do
                
                        currSW := CHOOSE x \in swSet: TRUE;
                        modifiedEnqueue(workerLocalQueue[self[1]], 
                                           [type |-> ROLE_REQ, roletype |-> ROLE_EQUAL, to |-> currSW]);
                        swSet := swSet \ {currSW};
                        
                        if swSet = {} then
                            goto WaitForSwitchUpdateRoleACK;
                        end if;
                    end while;
               
               WaitForSwitchUpdateRoleACK: 
                    \* Step 2: (1) wait for receiving confirmation from all switches regarding 
                    \* role update. (2) subscribe to IR Queue in NIB
                    await allSwitchInEqualRole(self[1]); 
                    subscribeList.IRQueueNIB := subscribeList.IRQueueNIB \cup {self[1]};
                    IRQueueEntries := IRQueueNIB; 
                    
                    
               QueryIRQueueNIB:
                    \* Step 3: (1) Pull IRQueue and add to worker queue
                    \* (2) notify failover module that OFC is ready to take over
                    while IRQueueEntries # <<>> do
                        entry := Head(IRQueueEntries);
                        IRQueueEntries := Tail(IRQueueEntries);
                        modifiedEnqueue(workerLocalQueue[self[1]], entry);
                    end while;
                    ofcFailoverStateNIB[self[1]] := FAILOVER_READY;
               
               WaitForRoleMaster:
                    await masterState[self[1]] = ROLE_MASTER; 
               
            \* if NIB event handler receives notification about failover status FAILOVER_TERMINATE
            \* it should gracefully terminate and respond with FAILOVER_TERMINATE_DONE;
            \* 1) send termination signal to workers and wait for them to terminate
            \* 2) send termination signal to topology event handler and monitoring server and wait
            \* for them to terminate
            \* 3) change its failover status to FAILOVER_TERMINATE_DONE       
            elsif ofcFailoverStateNIB[self[1]] = FAILOVER_TERMINATE then
                
              subscribeList.IRQueueNIB := subscribeList.IRQueueNIB \ {self[1]}; 
              ofcModuleTerminationStatus[self[1]] := [y \in CONTROLLER_THREAD_POOL |-> TERMINATE_INIT] 
                                                                        @@ ofcModuleTerminationStatus[self[1]];
              
              WaitForWorkersTermination:
                    await allWorkersTerminated(self[1]);
                    ofcModuleTerminationStatus[self[1]] := [y \in {CONT_MONITOR, CONT_EVENT} |-> TERMINATE_INIT] 
                                                                                @@ ofcModuleTerminationStatus[self[1]];
              
              
              WaitForAllModulesTermination:
                    await allModulesTerminated(self[1]);
                    ofcFailoverStateNIB[self[1]] := FAILOVER_TERMINATE_DONE;
            
            \* NIB event handler should pass the IRs to the worker's local queue. 
            elsif nibEventQueue[self[1]] # <<>> then
                
                read(nibEventQueue[self[1]], event);
                if event.type = INSTALL_FLOW then
                    modifiedEnqueue(workerLocalQueue[self[1]], event);
                end if;
                remove(nibEventQueue[self[1]]);
            
            \* NIB event handler should asynchronously update its role to ROLE_MASTER in all the switches
            else
                
                currSW := CHOOSE x \in getSetSwitchInEqualRole(self[1]): TRUE;
                roleUpdateStatus[self[1]][currSW] := IR_NONE; 
                modifiedEnqueue(workerLocalQueue[self[1]], [type |-> ROLE_REQ, roletype |-> ROLE_MASTER, to |-> currSW]);
                setScheduledRoleUpdates[self[1]] := setScheduledRoleUpdates[self[1]] \cup {currSW};
                \* TODO (@Pooria) should consider failure case
            
            end if; 
        end while;
    end process
    \* ==========================
    
    \* ====== Worker Pool ======= 
    \* Workers 
    fair process controllerWorkerThreads \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL)
    variables nextToSent=[type |-> 0], entryIndex=-1, rowIndex=-1, rowRemove=-1, 
              removeRow=-1, stepOfFailure=0; 
    begin
    ControllerThread:
    while ~shouldWorkerTerminate(self[1], self[2]) do
        \* await controllerIsMaster(self[1]);
        await isOfcEnabled[self[1]];
        await moduleIsUp(self);
        await workerLocalQueue # <<>>; 
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
        modifiedRead(workerLocalQueue[self[1]], nextToSent, entryIndex);
        
        whichStepToFail(2);
        if (stepOfFailure = 1) then
            \* Failed before Step 1
            controllerModuleFails();
            goto ControllerThreadStateReconciliation;
        else 
            \* Step 2: Worker Thread save state to NIB
            controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextToSent, index |-> entryIndex];
            if (stepOfFailure = 2) then
                \* Failed before Step 2
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            else    
                \* Step 3: try to lock the IR and if it's already lock do ControllerThreadRemoveQueue1 Operation.
                \***** Step 3.1: lock the semaphore using CAS operation 
                if idThreadWorkingOnIR[self[1]][entryIndex] = IR_UNLOCK then
                    await threadWithLowerIDGetsTheLock(self[1], self, nextToSent, workerLocalQueue[self[1]]); \* For Reducing Space
                    idThreadWorkingOnIR[self[1]][entryIndex] := self[2];
                else
                    ControllerThreadRemoveQueue1: 
                        controllerWaitForLockFree();
                        modifiedRemove(workerLocalQueue[self[1]], nextToSent);
                        if nextToSent.type = INSTALL_FLOW then
                            removeItem(IRQueueNIB, nextToSent);
                        end if;
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
                if workerCanSendTheIR(self[1], nextToSent) then
                    \**** Step 1.1: change the status of the IR to IR_SENT before actually sending
                    \**** the IR (Update-before-Action)
                    assert nextToSent.type \in {INSTALL_FLOW, ROLE_REQ};
                    if nextToSent.type = INSTALL_FLOW then
                        IRStatus[nextToSent.IR] := IR_SENT;
                    elsif nextToSent.type = ROLE_REQ then
                        roleUpdateStatus[self[1]][nextToSent.to] := IR_SENT;
                    end if;
                    
                    \* ControllerThreadForwardIR consists of 2 operations;
                    \* 1. Forwarding the IR to the switch
                    \* 2. Updating the state on db to SENT_DONE
                    \* Worker may fail between these operations
                    ControllerThreadForwardIR:
                        \* controllerWaitForLockFree(); \* Pooria commented this to enables concurrency on the switch side
                        whichStepToFail(2);
                        if (stepOfFailure # 1) then
                            \* Step 1: forward the IR
                            controllerSendIR(nextToSent);
                            if (stepOfFailure # 2) then
                               \* Step 2: save the state on NIB
                               controllerStateNIB[self] := [type |-> STATUS_SENT_DONE, 
                                                            next |-> nextToSent, 
                                                            index |-> entryIndex];
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
        \* TODO (@Pooria): below should be added again 
        \*WaitForIRToHaveCorrectStatus:  
        \*    controllerWaitForLockFree();
        \*    controllerModuleFailOrNot();
        \*    if (controllerSubmoduleFailStat[self] = NotFailed) then 
        \*        await ~isSwitchSuspended(nextToSent.to);
        \*    else
        \*        goto ControllerThreadStateReconciliation;
        \*    end if;
            
        \*ReScheduleifIRNone:
        \*    controllerWaitForLockFree();
        \*    controllerModuleFailOrNot();
        \*    if (controllerSubmoduleFailStat[self] = NotFailed) then
        \*        if workerShouldFastRecovery(self[1], nextToSent) then
        \*            controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextToSent, index |-> entryIndex]; 
        \*            goto ControllerThreadSendIR;
        \*        end if;
        \*    else
        \*        goto ControllerThreadStateReconciliation;
        \*    end if;
            
        \* Simply unlock the IR which was locked at the begining
        ControllerThreadUnlockSemaphore:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                if idThreadWorkingOnIR[self[1]][entryIndex] = self[2] then
                    idThreadWorkingOnIR[self[1]][entryIndex] := IR_UNLOCK;
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
                \* assert nextToSent \in SetScheduledIRs[IR2SW[nextIRToSent]];
                if nextToSent.type = INSTALL_FLOW then
                    SetScheduledIRs[nextToSent.to] := SetScheduledIRs[nextToSent.to]\{nextToSent.IR};
                end if;
                
                if (stepOfFailure # 2) then  
                    \* Step2: clear the state on NIB
                    controllerStateNIB[self] := [type |-> NO_STATUS];
                    if (stepOfFailure # 3) then
                        \* Step 3: remove from IRQueue
                        modifiedRemove(workerLocalQueue[self[1]], nextToSent);
                        if nextToSent.type = INSTALL_FLOW then
                            removeItem(IRQueueNIB, nextToSent);
                        end if;
                    
                    end if;
                end if;
            end if;
            
            if (stepOfFailure # 0) then
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            end if;
    end while;
    
    \* Terminate done
    ofcModuleTerminate();
    
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
        
        \* await controllerIsMaster(self[1]);
        await isOfcEnabled[self[1]];
        await moduleIsUp(self);
        await IRQueueNIB # <<>>;
        await canWorkerThreadContinue(self[1], self);
        controllerReleaseLock(self);
        if (controllerStateNIB[self].type = STATUS_LOCKING) then
            if (controllerStateNIB[self].next.type = INSTALL_FLOW) then
                if (IRStatus[controllerStateNIB[self].next.IR] = IR_SENT) then
                        IRStatus[controllerStateNIB[self].next.IR] := IR_NONE;
                end if;
            elsif (controllerStateNIB[self].next.type = ROLE_REQ) then
                if (roleUpdateStatus[self[1]][controllerStateNIB[self].next.to] = IR_SENT) then
                    roleUpdateStatus[self[1]][controllerStateNIB[self].next.to] := IR_NONE;
                end if;
            end if;                 
            if (idThreadWorkingOnIR[self[1]][controllerStateNIB[self].index] = self[2]) then
                idThreadWorkingOnIR[self[1]][controllerStateNIB[self].index] := IR_UNLOCK;
            end if;        
        elsif (controllerStateNIB[self].type = STATUS_SENT_DONE) then
            SetScheduledIRs[controllerStateNIB[self].next.to] := 
                    SetScheduledIRs[controllerStateNIB[self].next.to] \cup {controllerStateNIB[self].next.IR};          
            if (idThreadWorkingOnIR[self[1]][controllerStateNIB[self].index] = self[2]) then
                idThreadWorkingOnIR[self[1]][controllerStateNIB[self].index] := IR_UNLOCK;
            end if;
        end if;
        goto ControllerThread;
    end process
    \* ==========================
    
    \* ===== Event Handler ======
    fair process controllerEventHandler \in ({ofc0, ofc1} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, resetIR = 0, stepOfFailure = 0;
    begin
    ControllerEventHandlerProc:
    while ~shouldEventHandlerTerminate(self[1]) do 
         \* await controllerIsMaster(self[1]);
         await isOfcEnabled[self[1]];
         await moduleIsUp(self);   
         await swSeqChangedStatus[self[1]] # <<>>;
         controllerWaitForLockFree();
         
         \* Controller event handler process consists of two operations;
         \* 1. Picking the first event from the event queue
         \* 2. Check whether the event is a switch failure or a switch recovery
         monitoringEvent := Head(swSeqChangedStatus[self[1]]);
         \* TODO (@Pooria): failure will happen here: each should have their seperate 
         \* local SwSuspensionStatus because otherwise an OFC may miss an event
         \* Also, only one OFC has to have the write access to NIB, others should only
         \* be able to read.  
         if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
         
            \* ControllerSuspendSW only suspends the SW (so the rest of the system does not work on
            \* the tasks related to this switch anymore).
            \* Here, Due to performance reasons, we defere the task of resetting status of IRs to 
            \* the time that the switch is recovered (Lazy evaluation) because; First, it might not
            \* be necessary (for example, the switch may have installed the IR). Second, the switch
            \* may have faced a permanent failure in which these IRs are not valid anymore.                 
            \* only write to NIB if you are master
            \* if masterState[self[1]] = ROLE_MASTER then
                ControllerSuspendSW: 
                    controllerWaitForLockFree();
                    controllerModuleFailOrNot();
                    if (controllerSubmoduleFailStat[self] = NotFailed) then
                        SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;        
                    else
                        goto ControllerEventHandlerStateReconciliation;
                    end if;
            \* end if;
                
         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            \*call suspendInSchedulingIRs(monitoringEvent.swID);
            
            \* ControllerFreeSuspendedSW consists of three operations; 
            \* 1. Save on db that it is going to reset the IRs
            \* 2. Change the SW status to SW_RUN (so all the corresponding IRs going to be scheduled immediately)
            \* (event handler may fail between any of these Ops.)
            \* only write to NIB if you are master
            \*if masterState[self[1]] = ROLE_MASTER then 
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
            \*end if;
            
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
                    if ~existsMonitoringEventHigherNum(monitoringEvent, self[1]) then
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
                    swSeqChangedStatus[self[1]] := Tail(swSeqChangedStatus[self[1]]);
                end if;
            end if;
            
            if (stepOfFailure # 0) then
                controllerModuleFails();
                goto ControllerEventHandlerStateReconciliation;
            end if;
    end while;
    
    \* Terminate
    ofcModuleTerminate();
    
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
         \* await controllerIsMaster(self[1]);
         await isOfcEnabled[self[1]];
         await moduleIsUp(self);   
         await swSeqChangedStatus[self[1]] # <<>>; 
         controllerReleaseLock(self);
         if (controllerStateNIB[self].type = START_RESET_IR) then
            SwSuspensionStatus[controllerStateNIB[self].sw] := SW_SUSPEND;
         end if;
        goto ControllerEventHandlerProc;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    \* monitroing server does not need a reconciliation phase. 
    fair process controllerMonitoringServer \in ({ofc0, ofc1} \X {CONT_MONITOR})
    variable msg = [type |-> 0]
    begin
    ControllerMonitorCheckIfMastr:
    while ~shouldMonitoringServerTerminate(self[1]) do
        \* ControllerMonitor 
        \* 1. Picks the first packet from the packets received from the switches
        \* 2. Checks the message type;
        \***** 2.1. type = INSTALLED_SUCCESSFULLY -> sw has successfully installed the IR
        \***** 2.2. type = RECONCILIATION_RESPONCE -> sw's responce to the reconciliation 
        \*****              request. 
        
        \* await controllerIsMaster(self[1]);
        await isOfcEnabled[self[1]];
        await moduleIsUp(self);
        await switch2Controller[self[1]] # <<>>;
        controllerReleaseLock(self);
        msg := Head(switch2Controller[self[1]]);
        assert \/ /\ msg.type = INSTALLED_SUCCESSFULLY
                  /\ msg.from = IR2SW[msg.IR]
               \/ msg.type \in {ROLE_REPLY, BAD_REQUEST};
                  
               
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
                        IRStatus[msg.IR] := IR_DONE;
                    else
                        goto ControllerMonitorCheckIfMastr;
                    end if;
            
            elsif msg.type = ROLE_REPLY then
                
                ControllerUpdateRole:
                    controllerWaitForLockFree(); 
                    controllerModuleFailOrNot();
                    if (controllerSubmoduleFailStat[self] = NotFailed) then
                        roleUpdateStatus[self[1]][msg.from] := IR_DONE;
                        controllerRoleInSW[self[1]][msg.from] := msg.roletype; 
                    else
                        goto ControllerMonitorCheckIfMastr;
                    end if;
                    
            elsif msg.type = BAD_REQUEST then
                \* If msg type is BAD_REQUEST, it means this OFC is not the master for the switch
                \* for now we do nothing; Todo(@Pooria)
                skip; 
            else assert FALSE;
            end if;
        
        \*end if;
        
        \* MonitoringServerRemoveFromQueue lazily removes the msg from queue. 
        MonitoringServerRemoveFromQueue:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                switch2Controller[self[1]] := Tail(switch2Controller[self[1]]);
            else
                goto ControllerMonitorCheckIfMastr;
            end if; 
    end while;
    
    \* Terminate
    ofcModuleTerminate();
    
    end process
    
    \* ==========================
    
    (*******************************************************************)
    (*                     Shared (OFC and RC)                         *)
    (*******************************************************************)
    \* there are two watchdogs, one in RC, the other in OFC
    \* ======== Watchdog ======== 
    fair process watchDog \in (({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG})
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
    
    (*******************************************************************)
    (*                          Failover                               *)
    (*******************************************************************)
    \* this module handles the failover request and initiates the failover
    \* process
    \* ======== OFC failover =====
    fair process failoverProc \in ( {"proc"} \X {OFC_FAILOVER})
    \* consists of 3 steps; 
    \* 1) TODO(@Pooria) Complete comments
    begin 
    OfcFailoverNewMasterInitialization:
        await SHOULD_FAILOVER = 1;
        ofcFailoverStateNIB[ofc1] := FAILOVER_INIT;
    ofcFailoverCurrMasterTerminate:
        await ofcFailoverStateNIB[ofc1] = FAILOVER_READY;
        ofcFailoverStateNIB[ofc0] := FAILOVER_TERMINATE;
    ofcFailoverChangeRoles:
        await ofcFailoverStateNIB[ofc0] = FAILOVER_TERMINATE_DONE;
        masterState[ofc0] := ROLE_SLAVE || masterState[ofc1] := ROLE_MASTER;
    end process    
    \* ==========================
       
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b7947cf31d89ce2e2cbaf52c8bebb401
\* Process variable stepOfFailure of process controllerSequencer at line 1430 col 50 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 1647 col 29 changed to stepOfFailure_c
VARIABLES switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
          ContProcSet, SwProcSet, swSeqChangedStatus, controller2Switch, 
          switch2Controller, switchStatus, installedIRs, installedBy, 
          swFailedNum, NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
          Ofa2InstallerBuff, TCAM, controlMsgCounter, 
          switchControllerRoleStatus, controllerSubmoduleFailNum, 
          controllerSubmoduleFailStat, switchOrdering, dependencyGraph, IR2SW, 
          irCounter, MAX_IR_COUNTER, idThreadWorkingOnIR, workerThreadRanking, 
          workerLocalQueue, controllerRoleInSW, nibEventQueue, 
          roleUpdateStatus, isOfcEnabled, setScheduledRoleUpdates, 
          ofcModuleTerminationStatus, masterState, controllerStateNIB, 
          IRStatus, SwSuspensionStatus, IRQueueNIB, subscribeList, 
          SetScheduledIRs, ofcFailoverStateNIB, pc

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
                                                                                     allSizes \in AllPossibleSizes(MAX_NUM_IRs, MAX_NUM_IRs)}




whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID]


swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed


swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed
getMasterController(swID) == CHOOSE x \in DOMAIN switchControllerRoleStatus[swID]:
                                                switchControllerRoleStatus[swID][x] = ROLE_MASTER
isControllerMaster(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_MASTER
isControllerSlave(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_SLAVE
hasModificationAccess(swID, cid) == ~isControllerSlave(swID, cid)

swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed


returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}

getSetIRsForSwitch(SID) == {x \in 1..MAX_NUM_IRs: IR2SW[x] = SID}


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
controllerIsMaster(controllerID) == masterState[controllerID] = ROLE_MASTER
getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                             [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0
                                             [] controllerID = ofc1 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc1




isIdenticalElement(itemA, itemB) == \A x \in DOMAIN itemA: /\ x \in DOMAIN itemB
                                                           /\ itemA[x] = itemB[x]
NoEntryTaggedWith(buff, threadID) == ~\E x \in rangeSeq(buff): x.tag = threadID
FirstUntaggedEntry(buff, num) == ~\E x \in DOMAIN buff: /\ buff[x].tag = NO_TAG
                                                        /\ x < num
getFirstIRIndexToRead(buff, threadID) == CHOOSE x \in DOMAIN buff: \/ buff[x].tag = threadID
                                                                   \/ /\ NoEntryTaggedWith(buff, threadID)
                                                                      /\ FirstUntaggedEntry(buff, x)
                                                                      /\ buff[x].tag = NO_TAG
getFirstIndexWith(buff, item, threadID) == CHOOSE x \in DOMAIN buff: /\ buff[x].tag = threadID
                                                                     /\ isIdenticalElement(buff[x].item, item)
existEquivalentItemWithID(buff, item) == \E x \in rangeSeq(buff): /\ isIdenticalElement(item, x)
                                                                  /\ x.id # -1
existsEquivalentItem(buff, item) == \E x \in rangeSeq(buff): isIdenticalElement(item, x)
setEquivalentItems(buff, item) == {y \in rangeSeq(buff): isIdenticalElement(y, item)}
getIdOfEquivalentItem(buff, item) == CHOOSE i \in {x.id: x \in setEquivalentItems(buff, item)}:TRUE



isDependencySatisfied(ir) == ~\E y \in 1..MAX_NUM_IRs: /\ <<y, ir>> \in dependencyGraph
                                                     /\ IRStatus[y] # IR_DONE
getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MAX_NUM_IRs: /\ IRStatus[x] = IR_NONE
                                                          /\ isDependencySatisfied(x)
                                                          /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                          /\ x \notin SetScheduledIRs[IR2SW[x]]}



shouldWorkerTerminate(CID, TID) == ofcModuleTerminationStatus[CID][TID] = TERMINATE_INIT
shouldEventHandlerTerminate(CID) == ofcModuleTerminationStatus[CID][CONT_EVENT] = TERMINATE_INIT
shouldMonitoringServerTerminate(CID) == /\ ofcModuleTerminationStatus[CID][CONT_MONITOR] = TERMINATE_INIT
                                        /\ ~\E x \in 1..MAX_NUM_IRs: IRStatus[x] = IR_SENT

allSwitchInEqualRole(CID) == \A x \in SW: controllerRoleInSW[CID][x] = ROLE_EQUAL
getSetSwitchInSlaveRole(CID) == {x \in SW: controllerRoleInSW[CID][x] = ROLE_SLAVE}
getSetSwitchInEqualRole(CID) == {x \in SW: /\ controllerRoleInSW[CID][x] = ROLE_EQUAL
                                           /\ x \notin setScheduledRoleUpdates[CID]}
allModulesTerminated(CID) == \A x \in DOMAIN ofcModuleTerminationStatus[CID]:
                                                ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE
allWorkersTerminated(CID) == \A x \in CONTROLLER_THREAD_POOL:
                                                ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE


isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND



setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(workerLocalQueue[CID], <<CID, y>>)
                                                      /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}
canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(workerLocalQueue[CID]): x.tag = threadID
                                          \/ /\ \E x \in rangeSeq(workerLocalQueue[CID]): x.tag = NO_TAG
                                             /\ NoEntryTaggedWith(workerLocalQueue[CID], threadID)
                                             /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
setThreadsAttemptingForLock(CID, item, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ isIdenticalElement(y.item, item)
                                                                                                                 /\ y.tag = <<CID, x>>
                                                                                  /\ pc[<<CID, x>>] = "ControllerThread"}
threadWithLowerIDGetsTheLock(CID, threadID, item, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]:
                                                                                                        z \in setThreadsAttemptingForLock(CID, item, IRQueue)})
workerCanSendTheIR(CID, nextToSent) == /\ ~isSwitchSuspended(nextToSent.to)
                                       /\ \/ /\ nextToSent.type = ROLE_REQ
                                             /\ roleUpdateStatus[CID][nextToSent.to] = IR_NONE
                                          \/ /\ nextToSent.type = INSTALL_FLOW
                                             /\ IRStatus[nextToSent.IR] = IR_NONE
workerShouldFastRecovery(CID, nextToSent) == \/ /\ nextToSent.type = ROLE_REQ
                                                /\ roleUpdateStatus[CID][nextToSent.to] = IR_NONE
                                             \/ /\ nextToSent.type = INSTALL_FLOW
                                                /\ IRStatus[nextToSent.IR] = IR_NONE


existsMonitoringEventHigherNum(monEvent, tid) == \E x \in DOMAIN swSeqChangedStatus[tid]: /\ swSeqChangedStatus[tid][x].swID = monEvent.swID
                                                                                         /\ swSeqChangedStatus[tid][x].num > monEvent.num
shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                             \/ monEvent.type = NIC_ASIC_DOWN
                             \/ /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.status.installerStatus = INSTALLER_DOWN
canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.status.installerStatus = INSTALLER_UP


getIRSetToReset(SID) == {x \in 1..MAX_NUM_IRs: /\ IR2SW[x] = SID
                                             /\ IRStatus[x] \notin {IR_DONE, IR_NONE}}





returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                           /\ controllerSubmoduleFailStat[x] = Failed}


isFinished == \A x \in 1..MAX_NUM_IRs: IRStatus[x] = IR_DONE

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, failedSet, 
          statusResolveMsg, recoveredElem, toBeScheduledIRs, nextIR, 
          stepOfFailure_, subscriberOfcSet, ofcID, event, swSet, currSW, 
          IRQueueEntries, entry, nextToSent, entryIndex, rowIndex, rowRemove, 
          removeRow, stepOfFailure_c, monitoringEvent, setIRsToReset, resetIR, 
          stepOfFailure, msg, controllerFailedModules

vars == << switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
           ContProcSet, SwProcSet, swSeqChangedStatus, controller2Switch, 
           switch2Controller, switchStatus, installedIRs, installedBy, 
           swFailedNum, NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
           Ofa2InstallerBuff, TCAM, controlMsgCounter, 
           switchControllerRoleStatus, controllerSubmoduleFailNum, 
           controllerSubmoduleFailStat, switchOrdering, dependencyGraph, 
           IR2SW, irCounter, MAX_IR_COUNTER, idThreadWorkingOnIR, 
           workerThreadRanking, workerLocalQueue, controllerRoleInSW, 
           nibEventQueue, roleUpdateStatus, isOfcEnabled, 
           setScheduledRoleUpdates, ofcModuleTerminationStatus, masterState, 
           controllerStateNIB, IRStatus, SwSuspensionStatus, IRQueueNIB, 
           subscribeList, SetScheduledIRs, ofcFailoverStateNIB, pc, 
           ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
           installerInIR, statusMsg, notFailedSet, failedElem, failedSet, 
           statusResolveMsg, recoveredElem, toBeScheduledIRs, nextIR, 
           stepOfFailure_, subscriberOfcSet, ofcID, event, swSet, currSW, 
           IRQueueEntries, entry, nextToSent, entryIndex, rowIndex, rowRemove, 
           removeRow, stepOfFailure_c, monitoringEvent, setIRsToReset, 
           resetIR, stepOfFailure, msg, controllerFailedModules >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({rc0} \X {CONT_SEQ})) \cup (({ofc0, ofc1} \X {NIB_EVENT_HANDLER})) \cup (({ofc0, ofc1} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0, ofc1} \X {CONT_EVENT})) \cup (({ofc0, ofc1} \X {CONT_MONITOR})) \cup ((({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG})) \cup (( {"proc"} \X {OFC_FAILOVER}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..MAX_NUM_IRs |-> 0]
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ ContProcSet = ((({rc0} \X {CONT_SEQ})) \cup (({ofc0, ofc1} \X CONTROLLER_THREAD_POOL))
                          \cup (({ofc0, ofc1} \X {CONT_EVENT})) \cup (({ofc0, ofc1} \X {CONT_MONITOR})))
        /\ SwProcSet = ((({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW))
                          \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW))
                          \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW))
                          \cup (({SW_RESOLVE_PROC} \X SW)))
        /\ swSeqChangedStatus = [x \in {ofc0, ofc1} |-> <<>>]
        /\ controller2Switch = [x\in SW |-> <<>>]
        /\ switch2Controller = [x \in {ofc0, ofc1} |-> <<>>]
        /\ switchStatus = [x\in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed,
                           ofa |-> NotFailed, installer |-> NotFailed]]
        /\ installedIRs = <<>>
        /\ installedBy = [x \in 1..MAX_NUM_IRs |-> {}]
        /\ swFailedNum = [x \in SW |-> 0]
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> <<>>]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ switchControllerRoleStatus = [x \in SW |-> (ofc0 :> ROLE_MASTER @@ ofc1 :> ROLE_SLAVE)]
        /\ controllerSubmoduleFailNum = [x \in ({ofc0, ofc1} \cup {rc0}) |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ switchOrdering = (CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ dependencyGraph \in generateConnectedDAG(1..MAX_NUM_IRs)
        /\ IR2SW = (CHOOSE x \in [1..MAX_NUM_IRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z
                                                                              /\ switchOrdering[x[y]] =< switchOrdering[x[z]])
        /\ irCounter = 0
        /\ MAX_IR_COUNTER = 15
        /\ idThreadWorkingOnIR = [y \in {ofc0, ofc1} |-> [x \in 1..MAX_IR_COUNTER |-> IR_UNLOCK]]
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ workerLocalQueue = [x \in {ofc0, ofc1} |-> <<>>]
        /\ controllerRoleInSW = (ofc0 :> [x \in SW |-> ROLE_MASTER]) @@ (ofc1 :> [x \in SW |-> ROLE_SLAVE])
        /\ nibEventQueue = [x \in {ofc0, ofc1} |-> <<>>]
        /\ roleUpdateStatus = [x \in {ofc0, ofc1} |-> [y \in SW |-> IR_NONE]]
        /\ isOfcEnabled = [x \in {ofc0} |-> TRUE] @@ [x \in {ofc1} |-> FALSE]
        /\ setScheduledRoleUpdates = [x \in {ofc0, ofc1} |-> {}]
        /\ ofcModuleTerminationStatus = [x \in {ofc0, ofc1} |->
                                             [y \in ({CONT_MONITOR, CONT_EVENT} \cup CONTROLLER_THREAD_POOL) |-> TERMINATE_NONE]]
        /\ masterState = (ofc0 :> ROLE_MASTER @@ ofc1 :> ROLE_SLAVE @@ rc0 :> ROLE_MASTER)
        /\ controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatus = [x \in 1..MAX_NUM_IRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ subscribeList = [IRQueueNIB |-> {ofc0}]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ ofcFailoverStateNIB = [y \in {ofc0, ofc1} |-> FAILOVER_NONE]
        (* Process swProcess *)
        /\ ingressPkt = [self \in ({SW_SIMPLE_ID} \X SW) |-> [type |-> 0]]
        (* Process swNicAsicProcPacketIn *)
        /\ ingressIR = [self \in ({NIC_ASIC_IN} \X SW) |-> [type |-> 0]]
        (* Process swNicAsicProcPacketOut *)
        /\ egressMsg = [self \in ({NIC_ASIC_OUT} \X SW) |-> [type |-> 0]]
        (* Process ofaModuleProcPacketIn *)
        /\ ofaInMsg = [self \in ({OFA_IN} \X SW) |-> [type |-> 0]]
        (* Process ofaModuleProcPacketOut *)
        /\ ofaOutConfirmation = [self \in ({OFA_OUT} \X SW) |-> [type |-> 0]]
        (* Process installerModuleProc *)
        /\ installerInIR = [self \in ({INSTALLER} \X SW) |-> [type |-> 0]]
        (* Process swFailureProc *)
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> [type |-> 0]]
        /\ notFailedSet = [self \in ({SW_FAILURE_PROC} \X SW) |-> {}]
        /\ failedElem = [self \in ({SW_FAILURE_PROC} \X SW) |-> ""]
        (* Process swResolveFailure *)
        /\ failedSet = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> [type |-> 0]]
        /\ recoveredElem = [self \in ({SW_RESOLVE_PROC} \X SW) |-> ""]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ subscriberOfcSet = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ ofcID = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        (* Process nibEventHandler *)
        /\ event = [self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) |-> [type |-> 0]]
        /\ swSet = [self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) |-> {}]
        /\ currSW = [self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) |-> 0]
        /\ IRQueueEntries = [self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) |-> [type |-> 0]]
        /\ entry = [self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) |-> [type |-> 0]]
        (* Process controllerWorkerThreads *)
        /\ nextToSent = [self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) |-> [type |-> 0]]
        /\ entryIndex = [self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ rowIndex = [self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ rowRemove = [self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ removeRow = [self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ stepOfFailure_c = [self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0, ofc1} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({ofc0, ofc1} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0, ofc1} \X {CONT_EVENT}) |-> 0]
        /\ stepOfFailure = [self \in ({ofc0, ofc1} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0, ofc1} \X {CONT_MONITOR}) |-> [type |-> 0]]
        (* Process watchDog *)
        /\ controllerFailedModules = [self \in (({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG}) |-> {}]
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
                                        [] self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) -> "NibEventHandlerProc"
                                        [] self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0, ofc1} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0, ofc1} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in (({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG}) -> "ControllerWatchDogProc"
                                        [] self \in ( {"proc"} \X {OFC_FAILOVER}) -> "OfcFailoverNewMasterInitialization"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                \/ switchLock[2] = self[2]
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type \in {INSTALL_FLOW, ROLE_REQ, FLOW_STAT_REQ}, 
                                       "Failure of assertion at line 1068, column 9.")
                             /\ IF ingressPkt'[self].type = INSTALL_FLOW
                                   THEN /\ IF hasModificationAccess(self[2], ingressPkt'[self].from)
                                              THEN /\ installedIRs' = Append(installedIRs, (ingressPkt'[self].IR))
                                                   /\ installedBy' = [installedBy EXCEPT ![(ingressPkt'[self].IR)] = installedBy[(ingressPkt'[self].IR)] \cup {(ingressPkt'[self].from)}]
                                                   /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], (ingressPkt'[self].IR))]
                                                   /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                                                                                                from |-> self[2],
                                                                                                                                                to |-> (getMasterController(self[2])),
                                                                                                                                                IR |-> (ingressPkt'[self].IR)])]
                                              ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> BAD_REQUEST,
                                                                                                                                                from |-> self[2],
                                                                                                                                                to |-> (ofaInMsg[self].from),
                                                                                                                                                IR |-> (ofaInMsg[self].IR)])]
                                                   /\ UNCHANGED << installedIRs, 
                                                                   installedBy, 
                                                                   TCAM >>
                                        /\ UNCHANGED switchControllerRoleStatus
                                   ELSE /\ IF ingressPkt'[self].type = ROLE_REQ
                                              THEN /\ Assert(ingressPkt'[self].roletype \in {ROLE_MASTER, ROLE_SLAVE, ROLE_EQUAL}, 
                                                             "Failure of assertion at line 1078, column 13.")
                                                   /\ IF (ingressPkt'[self].roletype) = ROLE_MASTER
                                                         THEN /\ IF getMasterController(self[2]) # (ingressPkt'[self].from)
                                                                    THEN /\ switchControllerRoleStatus' = [switchControllerRoleStatus EXCEPT ![self[2]][getMasterController(self[2])] = ROLE_SLAVE,
                                                                                                                                             ![self[2]][(ingressPkt'[self].from)] = ROLE_MASTER]
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED switchControllerRoleStatus
                                                         ELSE /\ switchControllerRoleStatus' = [switchControllerRoleStatus EXCEPT ![self[2]][(ingressPkt'[self].from)] = ingressPkt'[self].roletype]
                                                   /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> ROLE_REPLY,
                                                                                                                                                from |-> self[2],
                                                                                                                                                roletype |-> (ingressPkt'[self].roletype),
                                                                                                                                                to |-> (ingressPkt'[self].from)])]
                                              ELSE /\ IF ingressPkt'[self].type = FLOW_STAT_REQ
                                                         THEN /\ TRUE
                                                         ELSE /\ TRUE
                                                   /\ UNCHANGED << Ofa2NicAsicBuff, 
                                                                   switchControllerRoleStatus >>
                                        /\ UNCHANGED << installedIRs, 
                                                        installedBy, TCAM >>
                             /\ Assert(\/ switchLock[2] = self[2]
                                       \/ switchLock[2] = NO_LOCK, 
                                       "Failure of assertion at line 868, column 9 of macro called at line 1086, column 9.")
                             /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             switch2Controller, switchStatus, 
                                             swFailedNum, NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, 
                                             controlMsgCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, SwSuspensionStatus, 
                                             IRQueueNIB, subscribeList, 
                                             SetScheduledIRs, 
                                             ofcFailoverStateNIB, ingressIR, 
                                             egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event, swSet, currSW, 
                                             IRQueueEntries, entry, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, 
                                             controllerFailedModules >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(ingressIR'[self].type \in {ROLE_REQ, INSTALL_FLOW}, 
                                   "Failure of assertion at line 1111, column 9.")
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                            \/ switchLock[2] = self[2]
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << controllerLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, swSeqChangedStatus, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, installedBy, 
                                         swFailedNum, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         switchControllerRoleStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, workerLocalQueue, 
                                         controllerRoleInSW, nibEventQueue, 
                                         roleUpdateStatus, isOfcEnabled, 
                                         setScheduledRoleUpdates, 
                                         ofcModuleTerminationStatus, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, subscribeList, 
                                         SetScheduledIRs, ofcFailoverStateNIB, 
                                         ingressPkt, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, toBeScheduledIRs, 
                                         nextIR, stepOfFailure_, 
                                         subscriberOfcSet, ofcID, event, swSet, 
                                         currSW, IRQueueEntries, entry, 
                                         nextToSent, entryIndex, rowIndex, 
                                         rowRemove, removeRow, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, 
                                         controllerFailedModules >>

SwitchNicAsicInsertToOfaBuff(self) == /\ pc[self] = "SwitchNicAsicInsertToOfaBuff"
                                      /\ IF swCanReceivePackets(self[2])
                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                    \/ switchLock[2] = self[2]
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
                                                      installedBy, swFailedNum, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchControllerRoleStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      workerLocalQueue, 
                                                      controllerRoleInSW, 
                                                      nibEventQueue, 
                                                      roleUpdateStatus, 
                                                      isOfcEnabled, 
                                                      setScheduledRoleUpdates, 
                                                      ofcModuleTerminationStatus, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      subscribeList, 
                                                      SetScheduledIRs, 
                                                      ofcFailoverStateNIB, 
                                                      ingressPkt, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      subscriberOfcSet, ofcID, 
                                                      event, swSet, currSW, 
                                                      IRQueueEntries, entry, 
                                                      nextToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      removeRow, 
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
                             /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                \/ switchLock[2] = self[2]
                             /\ switchLock' = self
                             /\ Assert(egressMsg'[self].type \in {INSTALLED_SUCCESSFULLY, ROLE_REPLY, BAD_REQUEST}, 
                                       "Failure of assertion at line 1139, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, SwSuspensionStatus, 
                                             IRQueueNIB, subscribeList, 
                                             SetScheduledIRs, 
                                             ofcFailoverStateNIB, ingressPkt, 
                                             ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event, swSet, currSW, 
                                             IRQueueEntries, entry, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, 
                                             controllerFailedModules >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                               \/ switchLock[2] = self[2]
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 868, column 9 of macro called at line 1146, column 17.")
                                            /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ switch2Controller' = [switch2Controller EXCEPT ![egressMsg[self].to] = Append(switch2Controller[egressMsg[self].to], egressMsg[self])]
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
                                                 installedBy, swFailedNum, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 switchControllerRoleStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, 
                                                 dependencyGraph, IR2SW, 
                                                 irCounter, MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 workerLocalQueue, 
                                                 controllerRoleInSW, 
                                                 nibEventQueue, 
                                                 roleUpdateStatus, 
                                                 isOfcEnabled, 
                                                 setScheduledRoleUpdates, 
                                                 ofcModuleTerminationStatus, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, subscribeList, 
                                                 SetScheduledIRs, 
                                                 ofcFailoverStateNIB, 
                                                 ingressPkt, ingressIR, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, 
                                                 subscriberOfcSet, ofcID, 
                                                 event, swSet, currSW, 
                                                 IRQueueEntries, entry, 
                                                 nextToSent, entryIndex, 
                                                 rowIndex, rowRemove, 
                                                 removeRow, stepOfFailure_c, 
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
                         /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                            \/ switchLock[2] = self[2]
                         /\ switchLock' = self
                         /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = Head(NicAsic2OfaBuff[self[2]])]
                         /\ Assert(ofaInMsg'[self].to = self[2], 
                                   "Failure of assertion at line 1174, column 9.")
                         /\ Assert(\/ /\ ofaInMsg'[self].type = ROLE_REQ
                                      /\ ofaInMsg'[self].roletype \in {ROLE_SLAVE, ROLE_MASTER, ROLE_EQUAL}
                                   \/ /\ ofaInMsg'[self].type = INSTALL_FLOW
                                      /\ ofaInMsg'[self].IR  \in 1..MAX_NUM_IRs, 
                                   "Failure of assertion at line 1175, column 9.")
                         /\ Assert(ofaInMsg'[self].from \in {ofc0, ofc1}, 
                                   "Failure of assertion at line 1179, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << controllerLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         installedBy, swFailedNum, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         switchControllerRoleStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, workerLocalQueue, 
                                         controllerRoleInSW, nibEventQueue, 
                                         roleUpdateStatus, isOfcEnabled, 
                                         setScheduledRoleUpdates, 
                                         ofcModuleTerminationStatus, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, subscribeList, 
                                         SetScheduledIRs, ofcFailoverStateNIB, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, toBeScheduledIRs, 
                                         nextIR, stepOfFailure_, 
                                         subscriberOfcSet, ofcID, event, swSet, 
                                         currSW, IRQueueEntries, entry, 
                                         nextToSent, entryIndex, rowIndex, 
                                         rowRemove, removeRow, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, 
                                         controllerFailedModules >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ Assert(ofaInMsg[self].type \in {INSTALL_FLOW, ROLE_REQ}, 
                                                     "Failure of assertion at line 1190, column 17.")
                                           /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                                 THEN /\ IF hasModificationAccess(self[2], ofaInMsg[self].from)
                                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                                    \/ switchLock[2] = self[2]
                                                                 /\ switchLock' = <<INSTALLER, self[2]>>
                                                                 /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]],
                                                                                                                                            [IR |-> ofaInMsg[self].IR,
                                                                                                                                            from |-> ofaInMsg[self].from])]
                                                                 /\ UNCHANGED Ofa2NicAsicBuff
                                                            ELSE /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                                    \/ switchLock[2] = self[2]
                                                                 /\ switchLock' = <<NIC_ASIC_OUT, self[2]>>
                                                                 /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> BAD_REQUEST,
                                                                                                                                                              from |-> self[2],
                                                                                                                                                              to |-> (ofaInMsg[self].from),
                                                                                                                                                              IR |-> (ofaInMsg[self].IR)])]
                                                                 /\ UNCHANGED Ofa2InstallerBuff
                                                      /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                                      /\ UNCHANGED switchControllerRoleStatus
                                                 ELSE /\ IF ofaInMsg[self].type = ROLE_REQ
                                                            THEN /\ Assert(ofaInMsg[self].roletype \in {ROLE_MASTER, ROLE_SLAVE, ROLE_EQUAL}, 
                                                                           "Failure of assertion at line 1214, column 21.")
                                                                 /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                                    \/ switchLock[2] = self[2]
                                                                 /\ switchLock' = self
                                                                 /\ IF (ofaInMsg[self].roletype) = ROLE_MASTER
                                                                       THEN /\ IF getMasterController(self[2]) # (ofaInMsg[self].from)
                                                                                  THEN /\ switchControllerRoleStatus' = [switchControllerRoleStatus EXCEPT ![self[2]][getMasterController(self[2])] = ROLE_SLAVE,
                                                                                                                                                           ![self[2]][(ofaInMsg[self].from)] = ROLE_MASTER]
                                                                                  ELSE /\ TRUE
                                                                                       /\ UNCHANGED switchControllerRoleStatus
                                                                       ELSE /\ switchControllerRoleStatus' = [switchControllerRoleStatus EXCEPT ![self[2]][(ofaInMsg[self].from)] = ofaInMsg[self].roletype]
                                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchSendRoleReply"]
                                                            ELSE /\ IF ofaInMsg[self].type = FLOW_STAT_REQ
                                                                       THEN /\ TRUE
                                                                       ELSE /\ TRUE
                                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                                                 /\ UNCHANGED << switchLock, 
                                                                                 switchControllerRoleStatus >>
                                                      /\ UNCHANGED << Ofa2NicAsicBuff, 
                                                                      Ofa2InstallerBuff >>
                                           /\ UNCHANGED ofaInMsg
                                      ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED << switchLock, 
                                                           Ofa2NicAsicBuff, 
                                                           Ofa2InstallerBuff, 
                                                           switchControllerRoleStatus >>
                                /\ UNCHANGED << controllerLock, FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                installedBy, swFailedNum, 
                                                NicAsic2OfaBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                roleUpdateStatus, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                subscribeList, SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, 
                                                subscriberOfcSet, ofcID, event, 
                                                swSet, currSW, IRQueueEntries, 
                                                entry, nextToSent, entryIndex, 
                                                rowIndex, rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                controllerFailedModules >>

SwitchSendRoleReply(self) == /\ pc[self] = "SwitchSendRoleReply"
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                \/ switchLock[2] = self[2]
                             /\ switchLock' = <<NIC_ASIC_OUT, self[2]>>
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> ROLE_REPLY,
                                                                                                                          from |-> self[2],
                                                                                                                          roletype |-> (ofaInMsg[self].roletype),
                                                                                                                          to |-> (ofaInMsg[self].from)])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, SwSuspensionStatus, 
                                             IRQueueNIB, subscribeList, 
                                             SetScheduledIRs, 
                                             ofcFailoverStateNIB, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event, swSet, currSW, 
                                             IRQueueEntries, entry, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, 
                                             controllerFailedModules >>

ofaModuleProcPacketIn(self) == SwitchOfaProcIn(self)
                                  \/ SwitchOfaProcessPacket(self)
                                  \/ SwitchSendRoleReply(self)

SwitchOfaProcOut(self) == /\ pc[self] = "SwitchOfaProcOut"
                          /\ swOFACanProcessIRs(self[2])
                          /\ Installer2OfaBuff[self[2]] # <<>>
                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             \/ switchLock[2] = self[2]
                          /\ switchLock' = self
                          /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = Head(Installer2OfaBuff[self[2]])]
                          /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Tail(Installer2OfaBuff[self[2]])]
                          /\ Assert(ofaOutConfirmation'[self].IR \in 1..MAX_NUM_IRs, 
                                    "Failure of assertion at line 1245, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << controllerLock, FirstInstall, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          installedBy, swFailedNum, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, 
                                          switchControllerRoleStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, irCounter, MAX_IR_COUNTER, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          workerLocalQueue, controllerRoleInSW, 
                                          nibEventQueue, roleUpdateStatus, 
                                          isOfcEnabled, 
                                          setScheduledRoleUpdates, 
                                          ofcModuleTerminationStatus, 
                                          masterState, controllerStateNIB, 
                                          IRStatus, SwSuspensionStatus, 
                                          IRQueueNIB, subscribeList, 
                                          SetScheduledIRs, ofcFailoverStateNIB, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, subscriberOfcSet, 
                                          ofcID, event, swSet, currSW, 
                                          IRQueueEntries, entry, nextToSent, 
                                          entryIndex, rowIndex, rowRemove, 
                                          removeRow, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, 
                                          controllerFailedModules >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                    \/ switchLock[2] = self[2]
                                                 /\ switchLock' = <<NIC_ASIC_OUT, self[2]>>
                                                 /\ IF hasModificationAccess(self[2], ofaOutConfirmation[self].from)
                                                       THEN /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                                                                                                         from |-> self[2],
                                                                                                                                                         to |-> (ofaOutConfirmation[self].from),
                                                                                                                                                         IR |-> (ofaOutConfirmation[self].IR)])]
                                                       ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> BAD_REQUEST,
                                                                                                                                                         from |-> self[2],
                                                                                                                                                         to |-> (ofaOutConfirmation[self].from),
                                                                                                                                                         IR |-> (ofaOutConfirmation[self].IR)])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                 /\ UNCHANGED ofaOutConfirmation
                                            ELSE /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = [type |-> 0]]
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
                                                      installedBy, swFailedNum, 
                                                      NicAsic2OfaBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchControllerRoleStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      workerLocalQueue, 
                                                      controllerRoleInSW, 
                                                      nibEventQueue, 
                                                      roleUpdateStatus, 
                                                      isOfcEnabled, 
                                                      setScheduledRoleUpdates, 
                                                      ofcModuleTerminationStatus, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      subscribeList, 
                                                      SetScheduledIRs, 
                                                      ofcFailoverStateNIB, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      subscriberOfcSet, ofcID, 
                                                      event, swSet, currSW, 
                                                      IRQueueEntries, entry, 
                                                      nextToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      removeRow, 
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
                             /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                \/ switchLock[2] = self[2]
                             /\ switchLock' = self
                             /\ installerInIR' = [installerInIR EXCEPT ![self] = Head(Ofa2InstallerBuff[self[2]])]
                             /\ Assert(installerInIR'[self].IR \in 1..MAX_NUM_IRs, 
                                       "Failure of assertion at line 1281, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, SwSuspensionStatus, 
                                             IRQueueNIB, subscribeList, 
                                             SetScheduledIRs, 
                                             ofcFailoverStateNIB, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, toBeScheduledIRs, 
                                             nextIR, stepOfFailure_, 
                                             subscriberOfcSet, ofcID, event, 
                                             swSet, currSW, IRQueueEntries, 
                                             entry, nextToSent, entryIndex, 
                                             rowIndex, rowRemove, removeRow, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, 
                                             controllerFailedModules >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                               /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                  \/ switchLock[2] = self[2]
                                               /\ switchLock' = self
                                               /\ installedIRs' = Append(installedIRs, (installerInIR[self].IR))
                                               /\ installedBy' = [installedBy EXCEPT ![(installerInIR[self].IR)] = installedBy[(installerInIR[self].IR)] \cup {(installerInIR[self].from)}]
                                               /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], (installerInIR[self].IR))]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerSendConfirmation"]
                                               /\ UNCHANGED installerInIR
                                          ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0]]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                               /\ UNCHANGED << switchLock, 
                                                               installedIRs, 
                                                               installedBy, 
                                                               TCAM >>
                                    /\ UNCHANGED << controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, swFailedNum, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    workerLocalQueue, 
                                                    controllerRoleInSW, 
                                                    nibEventQueue, 
                                                    roleUpdateStatus, 
                                                    isOfcEnabled, 
                                                    setScheduledRoleUpdates, 
                                                    ofcModuleTerminationStatus, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, subscribeList, 
                                                    SetScheduledIRs, 
                                                    ofcFailoverStateNIB, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    subscriberOfcSet, ofcID, 
                                                    event, swSet, currSW, 
                                                    IRQueueEntries, entry, 
                                                    nextToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    removeRow, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, 
                                                    controllerFailedModules >>

SwitchInstallerSendConfirmation(self) == /\ pc[self] = "SwitchInstallerSendConfirmation"
                                         /\ IF swCanInstallIRs(self[2])
                                               THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                    /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                       \/ switchLock[2] = self[2]
                                                    /\ switchLock' = <<OFA_OUT, self[2]>>
                                                    /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Append(Installer2OfaBuff[self[2]], installerInIR[self])]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED installerInIR
                                               ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0]]
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
                                                         installedBy, 
                                                         swFailedNum, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         switchControllerRoleStatus, 
                                                         controllerSubmoduleFailNum, 
                                                         controllerSubmoduleFailStat, 
                                                         switchOrdering, 
                                                         dependencyGraph, 
                                                         IR2SW, irCounter, 
                                                         MAX_IR_COUNTER, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         workerLocalQueue, 
                                                         controllerRoleInSW, 
                                                         nibEventQueue, 
                                                         roleUpdateStatus, 
                                                         isOfcEnabled, 
                                                         setScheduledRoleUpdates, 
                                                         ofcModuleTerminationStatus, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         subscribeList, 
                                                         SetScheduledIRs, 
                                                         ofcFailoverStateNIB, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         subscriberOfcSet, 
                                                         ofcID, event, swSet, 
                                                         currSW, 
                                                         IRQueueEntries, entry, 
                                                         nextToSent, 
                                                         entryIndex, rowIndex, 
                                                         rowRemove, removeRow, 
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
                       /\ swFailedNum[self[2]] < MAX_NUM_SW_FAILURE
                       /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                             \/ switchLock[2] = self[2]
                       /\ \E x \in getSetIRsForSwitch(self[2]): IRStatus[x] # IR_DONE
                       /\ self[2] \in Head(sw_fail_ordering_var)
                       /\ Assert((self[2]) \in Head(sw_fail_ordering_var), 
                                 "Failure of assertion at line 557, column 9 of macro called at line 1333, column 9.")
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{(self[2])})>> \o Tail(sw_fail_ordering_var)
                       /\ \E elem \in notFailedSet'[self]:
                            failedElem' = [failedElem EXCEPT ![self] = elem]
                       /\ IF failedElem'[self] = "cpu"
                             THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                  /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                            "Failure of assertion at line 636, column 9 of macro called at line 1342, column 17.")
                                  /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = Failed,
                                                                          ![self[2]].ofa = Failed,
                                                                          ![self[2]].installer = Failed]
                                  /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                  /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                  /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                        THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                             /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                          swID |-> self[2],
                                                                                          num |-> controlMsgCounter'[self[2]]]]
                                             /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg'[self])]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << swSeqChangedStatus, 
                                                             controlMsgCounter, 
                                                             statusMsg >>
                                  /\ UNCHANGED controller2Switch
                             ELSE /\ IF failedElem'[self] = "ofa"
                                        THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                             /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed, 
                                                       "Failure of assertion at line 689, column 9 of macro called at line 1345, column 17.")
                                             /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = Failed]
                                             /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                             /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                   THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                        /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                                     swID |-> self[2],
                                                                                                     num |-> controlMsgCounter'[self[2]]]]
                                                        /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg'[self])]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << swSeqChangedStatus, 
                                                                        controlMsgCounter, 
                                                                        statusMsg >>
                                             /\ UNCHANGED controller2Switch
                                        ELSE /\ IF failedElem'[self] = "installer"
                                                   THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                                        /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed, 
                                                                  "Failure of assertion at line 734, column 9 of macro called at line 1348, column 17.")
                                                        /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                        /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                                        /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                              THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                             "Failure of assertion at line 738, column 13 of macro called at line 1348, column 17.")
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]],
                                                                                                                status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                                                   /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg'[self])]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                                                   controlMsgCounter, 
                                                                                   statusMsg >>
                                                        /\ UNCHANGED controller2Switch
                                                   ELSE /\ IF failedElem'[self] = "nicAsic"
                                                              THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                                                   /\ Assert(switchStatus[self[2]].nicAsic = NotFailed, 
                                                                             "Failure of assertion at line 581, column 9 of macro called at line 1351, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                   /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]]]]
                                                                   /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg'[self])]
                                                              ELSE /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 1352, column 14.")
                                                                   /\ UNCHANGED << swSeqChangedStatus, 
                                                                                   controller2Switch, 
                                                                                   switchStatus, 
                                                                                   swFailedNum, 
                                                                                   controlMsgCounter, 
                                                                                   statusMsg >>
                                  /\ UNCHANGED << NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff >>
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstall, ContProcSet, SwProcSet, 
                                       switch2Controller, installedIRs, 
                                       installedBy, TCAM, 
                                       switchControllerRoleStatus, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       irCounter, MAX_IR_COUNTER, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, workerLocalQueue, 
                                       controllerRoleInSW, nibEventQueue, 
                                       roleUpdateStatus, isOfcEnabled, 
                                       setScheduledRoleUpdates, 
                                       ofcModuleTerminationStatus, masterState, 
                                       controllerStateNIB, IRStatus, 
                                       SwSuspensionStatus, IRQueueNIB, 
                                       subscribeList, SetScheduledIRs, 
                                       ofcFailoverStateNIB, ingressPkt, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, toBeScheduledIRs, nextIR, 
                                       stepOfFailure_, subscriberOfcSet, ofcID, 
                                       event, swSet, currSW, IRQueueEntries, 
                                       entry, nextToSent, entryIndex, rowIndex, 
                                       rowRemove, removeRow, stepOfFailure_c, 
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
                                                   "Failure of assertion at line 664, column 9 of macro called at line 1378, column 39.")
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
                                                    /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg'[self])]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << swSeqChangedStatus, 
                                                                    controlMsgCounter, 
                                                                    statusResolveMsg >>
                                         /\ UNCHANGED controller2Switch
                                    ELSE /\ IF recoveredElem'[self] = "nicAsic"
                                               THEN /\ nicAsicStartingMode(self[2])
                                                    /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                              "Failure of assertion at line 608, column 9 of macro called at line 1379, column 46.")
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
                                                    /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg'[self])]
                                               ELSE /\ IF recoveredElem'[self] = "ofa"
                                                          THEN /\ ofaStartingMode(self[2])
                                                               /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = Failed, 
                                                                         "Failure of assertion at line 712, column 9 of macro called at line 1380, column 42.")
                                                               /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = NotFailed]
                                                               /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                                     THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                          /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                                                     swID |-> self[2],
                                                                                                                                     num |-> controlMsgCounter'[self[2]],
                                                                                                                                     status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                                                          /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg'[self])]
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                                                          controlMsgCounter, 
                                                                                          statusResolveMsg >>
                                                          ELSE /\ IF recoveredElem'[self] = "installer"
                                                                     THEN /\ installerInStartingMode(self[2])
                                                                          /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = Failed, 
                                                                                    "Failure of assertion at line 757, column 9 of macro called at line 1381, column 48.")
                                                                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                               "Failure of assertion at line 760, column 13 of macro called at line 1381, column 48.")
                                                                                     /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                                     /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                                                                swID |-> self[2],
                                                                                                                                                num |-> controlMsgCounter'[self[2]],
                                                                                                                                                status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                                                                     /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![getMasterController(self[2])] = Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg'[self])]
                                                                                ELSE /\ TRUE
                                                                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                                                                     controlMsgCounter, 
                                                                                                     statusResolveMsg >>
                                                                     ELSE /\ Assert(FALSE, 
                                                                                    "Failure of assertion at line 1382, column 14.")
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
                                              installedBy, swFailedNum, TCAM, 
                                              switchControllerRoleStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, dependencyGraph, 
                                              IR2SW, irCounter, MAX_IR_COUNTER, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              workerLocalQueue, 
                                              controllerRoleInSW, 
                                              nibEventQueue, roleUpdateStatus, 
                                              isOfcEnabled, 
                                              setScheduledRoleUpdates, 
                                              ofcModuleTerminationStatus, 
                                              masterState, controllerStateNIB, 
                                              IRStatus, SwSuspensionStatus, 
                                              IRQueueNIB, subscribeList, 
                                              SetScheduledIRs, 
                                              ofcFailoverStateNIB, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, subscriberOfcSet, 
                                              ofcID, event, swSet, currSW, 
                                              IRQueueEntries, entry, 
                                              nextToSent, entryIndex, rowIndex, 
                                              rowRemove, removeRow, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, 
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
                             "Failure of assertion at line 868, column 9 of macro called at line 1416, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << controllerLock, FirstInstall, 
                                   sw_fail_ordering_var, ContProcSet, 
                                   SwProcSet, swSeqChangedStatus, 
                                   controller2Switch, switch2Controller, 
                                   switchStatus, installedIRs, installedBy, 
                                   swFailedNum, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   switchControllerRoleStatus, 
                                   controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   dependencyGraph, IR2SW, irCounter, 
                                   MAX_IR_COUNTER, idThreadWorkingOnIR, 
                                   workerThreadRanking, workerLocalQueue, 
                                   controllerRoleInSW, nibEventQueue, 
                                   roleUpdateStatus, isOfcEnabled, 
                                   setScheduledRoleUpdates, 
                                   ofcModuleTerminationStatus, masterState, 
                                   controllerStateNIB, IRStatus, 
                                   SwSuspensionStatus, IRQueueNIB, 
                                   subscribeList, SetScheduledIRs, 
                                   ofcFailoverStateNIB, ingressPkt, ingressIR, 
                                   egressMsg, ofaInMsg, ofaOutConfirmation, 
                                   installerInIR, statusMsg, notFailedSet, 
                                   failedElem, failedSet, statusResolveMsg, 
                                   recoveredElem, toBeScheduledIRs, nextIR, 
                                   stepOfFailure_, subscriberOfcSet, ofcID, 
                                   event, swSet, currSW, IRQueueEntries, entry, 
                                   nextToSent, entryIndex, rowIndex, rowRemove, 
                                   removeRow, stepOfFailure_c, monitoringEvent, 
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
                                           installedIRs, installedBy, 
                                           swFailedNum, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           switchControllerRoleStatus, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           IR2SW, irCounter, MAX_IR_COUNTER, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, 
                                           workerLocalQueue, 
                                           controllerRoleInSW, nibEventQueue, 
                                           roleUpdateStatus, isOfcEnabled, 
                                           setScheduledRoleUpdates, 
                                           ofcModuleTerminationStatus, 
                                           masterState, controllerStateNIB, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, subscribeList, 
                                           SetScheduledIRs, 
                                           ofcFailoverStateNIB, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, nextIR, 
                                           stepOfFailure_, subscriberOfcSet, 
                                           ofcID, event, swSet, currSW, 
                                           IRQueueEntries, entry, nextToSent, 
                                           entryIndex, rowIndex, rowRemove, 
                                           removeRow, stepOfFailure_c, 
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
                                            FirstInstall, sw_fail_ordering_var, 
                                            ContProcSet, SwProcSet, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, installedBy, 
                                            swFailedNum, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            switchControllerRoleStatus, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, irCounter, MAX_IR_COUNTER, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            workerLocalQueue, 
                                            controllerRoleInSW, nibEventQueue, 
                                            roleUpdateStatus, isOfcEnabled, 
                                            setScheduledRoleUpdates, 
                                            ofcModuleTerminationStatus, 
                                            masterState, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            subscribeList, ofcFailoverStateNIB, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, toBeScheduledIRs, 
                                            subscriberOfcSet, ofcID, event, 
                                            swSet, currSW, IRQueueEntries, 
                                            entry, nextToSent, entryIndex, 
                                            rowIndex, rowRemove, removeRow, 
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
                             THEN /\ IRQueueNIB' = Append(IRQueueNIB, ([type |-> INSTALL_FLOW, to |-> IR2SW[nextIR[self]], IR |-> nextIR[self]]))
                                  /\ subscriberOfcSet' = [subscriberOfcSet EXCEPT ![self] = subscribeList.IRQueueNIB]
                                  /\ pc' = [pc EXCEPT ![self] = "sendIRQueueModNotification"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "sequencerApplyFailure"]
                                  /\ UNCHANGED << IRQueueNIB, subscriberOfcSet >>
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstall, sw_fail_ordering_var, 
                                       ContProcSet, SwProcSet, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, switchStatus, 
                                       installedIRs, installedBy, swFailedNum, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Installer2OfaBuff, Ofa2InstallerBuff, 
                                       TCAM, controlMsgCounter, 
                                       switchControllerRoleStatus, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       irCounter, MAX_IR_COUNTER, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, workerLocalQueue, 
                                       controllerRoleInSW, nibEventQueue, 
                                       roleUpdateStatus, isOfcEnabled, 
                                       setScheduledRoleUpdates, 
                                       ofcModuleTerminationStatus, masterState, 
                                       controllerStateNIB, IRStatus, 
                                       SwSuspensionStatus, subscribeList, 
                                       SetScheduledIRs, ofcFailoverStateNIB, 
                                       ingressPkt, ingressIR, egressMsg, 
                                       ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, failedSet, statusResolveMsg, 
                                       recoveredElem, toBeScheduledIRs, nextIR, 
                                       ofcID, event, swSet, currSW, 
                                       IRQueueEntries, entry, nextToSent, 
                                       entryIndex, rowIndex, rowRemove, 
                                       removeRow, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, 
                                       controllerFailedModules >>

sendIRQueueModNotification(self) == /\ pc[self] = "sendIRQueueModNotification"
                                    /\ IF subscriberOfcSet[self] # {}
                                          THEN /\ ofcID' = [ofcID EXCEPT ![self] = CHOOSE x \in subscriberOfcSet[self]: TRUE]
                                               /\ subscriberOfcSet' = [subscriberOfcSet EXCEPT ![self] = subscriberOfcSet[self] \ {ofcID'[self]}]
                                               /\ nibEventQueue' = [nibEventQueue EXCEPT ![ofcID'[self]] = Append((nibEventQueue[ofcID'[self]]), ([type |-> INSTALL_FLOW,
                                                                                                                                                   to |-> IR2SW[nextIR[self]],
                                                                                                                                                   IR |-> nextIR[self]]))]
                                               /\ pc' = [pc EXCEPT ![self] = "sendIRQueueModNotification"]
                                               /\ UNCHANGED << controllerStateNIB, 
                                                               toBeScheduledIRs >>
                                          ELSE /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR[self]}]
                                               /\ IF (stepOfFailure_[self] # 2)
                                                     THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED controllerStateNIB
                                               /\ pc' = [pc EXCEPT ![self] = "sequencerApplyFailure"]
                                               /\ UNCHANGED << nibEventQueue, 
                                                               subscriberOfcSet, 
                                                               ofcID >>
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    installedBy, swFailedNum, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    workerLocalQueue, 
                                                    controllerRoleInSW, 
                                                    roleUpdateStatus, 
                                                    isOfcEnabled, 
                                                    setScheduledRoleUpdates, 
                                                    ofcModuleTerminationStatus, 
                                                    masterState, IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, subscribeList, 
                                                    SetScheduledIRs, 
                                                    ofcFailoverStateNIB, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, nextIR, 
                                                    stepOfFailure_, event, 
                                                    swSet, currSW, 
                                                    IRQueueEntries, entry, 
                                                    nextToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    removeRow, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, 
                                                    controllerFailedModules >>

sequencerApplyFailure(self) == /\ pc[self] = "sequencerApplyFailure"
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
                                               switch2Controller, switchStatus, 
                                               installedIRs, installedBy, 
                                               swFailedNum, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               switchControllerRoleStatus, 
                                               switchOrdering, dependencyGraph, 
                                               IR2SW, irCounter, 
                                               MAX_IR_COUNTER, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               workerLocalQueue, 
                                               controllerRoleInSW, 
                                               nibEventQueue, roleUpdateStatus, 
                                               isOfcEnabled, 
                                               setScheduledRoleUpdates, 
                                               ofcModuleTerminationStatus, 
                                               masterState, controllerStateNIB, 
                                               IRStatus, SwSuspensionStatus, 
                                               IRQueueNIB, subscribeList, 
                                               SetScheduledIRs, 
                                               ofcFailoverStateNIB, ingressPkt, 
                                               ingressIR, egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, 
                                               subscriberOfcSet, ofcID, event, 
                                               swSet, currSW, IRQueueEntries, 
                                               entry, nextToSent, entryIndex, 
                                               rowIndex, rowRemove, removeRow, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
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
                                                          installedBy, 
                                                          swFailedNum, 
                                                          NicAsic2OfaBuff, 
                                                          Ofa2NicAsicBuff, 
                                                          Installer2OfaBuff, 
                                                          Ofa2InstallerBuff, 
                                                          TCAM, 
                                                          controlMsgCounter, 
                                                          switchControllerRoleStatus, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          dependencyGraph, 
                                                          IR2SW, irCounter, 
                                                          MAX_IR_COUNTER, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          workerLocalQueue, 
                                                          controllerRoleInSW, 
                                                          nibEventQueue, 
                                                          roleUpdateStatus, 
                                                          isOfcEnabled, 
                                                          setScheduledRoleUpdates, 
                                                          ofcModuleTerminationStatus, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          subscribeList, 
                                                          ofcFailoverStateNIB, 
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
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          subscriberOfcSet, 
                                                          ofcID, event, swSet, 
                                                          currSW, 
                                                          IRQueueEntries, 
                                                          entry, nextToSent, 
                                                          entryIndex, rowIndex, 
                                                          rowRemove, removeRow, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          controllerFailedModules >>

controllerSequencer(self) == ControllerSeqProc(self)
                                \/ SchedulerMechanism(self)
                                \/ ScheduleTheIR(self)
                                \/ sendIRQueueModNotification(self)
                                \/ sequencerApplyFailure(self)
                                \/ ControllerSeqStateReconciliation(self)

NibEventHandlerProc(self) == /\ pc[self] = "NibEventHandlerProc"
                             /\ \/ ofcFailoverStateNIB[self[1]] \in {FAILOVER_INIT, FAILOVER_TERMINATE}
                                \/ /\ masterState[self[1]] = ROLE_MASTER
                                   /\ nibEventQueue[self[1]] # <<>>
                                \/ /\ masterState[self[1]] = ROLE_MASTER
                                   /\ getSetSwitchInEqualRole(self[1]) # {}
                             /\ IF ofcFailoverStateNIB[self[1]] = FAILOVER_INIT
                                   THEN /\ isOfcEnabled' = [isOfcEnabled EXCEPT ![self[1]] = TRUE]
                                        /\ swSet' = [swSet EXCEPT ![self] = getSetSwitchInSlaveRole(self[1])]
                                        /\ pc' = [pc EXCEPT ![self] = "ScheduleRoleUpdateEqual"]
                                        /\ UNCHANGED << workerLocalQueue, 
                                                        nibEventQueue, 
                                                        roleUpdateStatus, 
                                                        setScheduledRoleUpdates, 
                                                        ofcModuleTerminationStatus, 
                                                        subscribeList, event, 
                                                        currSW >>
                                   ELSE /\ IF ofcFailoverStateNIB[self[1]] = FAILOVER_TERMINATE
                                              THEN /\ subscribeList' = [subscribeList EXCEPT !.IRQueueNIB = subscribeList.IRQueueNIB \ {self[1]}]
                                                   /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]] = [y \in CONTROLLER_THREAD_POOL |-> TERMINATE_INIT]
                                                                                                                                                       @@ ofcModuleTerminationStatus[self[1]]]
                                                   /\ pc' = [pc EXCEPT ![self] = "WaitForWorkersTermination"]
                                                   /\ UNCHANGED << workerLocalQueue, 
                                                                   nibEventQueue, 
                                                                   roleUpdateStatus, 
                                                                   setScheduledRoleUpdates, 
                                                                   event, 
                                                                   currSW >>
                                              ELSE /\ IF nibEventQueue[self[1]] # <<>>
                                                         THEN /\ event' = [event EXCEPT ![self] = Head((nibEventQueue[self[1]]))]
                                                              /\ IF event'[self].type = INSTALL_FLOW
                                                                    THEN /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> event'[self], id |-> -1, tag |-> NO_TAG])]
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED workerLocalQueue
                                                              /\ nibEventQueue' = [nibEventQueue EXCEPT ![self[1]] = Tail((nibEventQueue[self[1]]))]
                                                              /\ UNCHANGED << roleUpdateStatus, 
                                                                              setScheduledRoleUpdates, 
                                                                              currSW >>
                                                         ELSE /\ currSW' = [currSW EXCEPT ![self] = CHOOSE x \in getSetSwitchInEqualRole(self[1]): TRUE]
                                                              /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][currSW'[self]] = IR_NONE]
                                                              /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> ([type |-> ROLE_REQ, roletype |-> ROLE_MASTER, to |-> currSW'[self]]), id |-> -1, tag |-> NO_TAG])]
                                                              /\ setScheduledRoleUpdates' = [setScheduledRoleUpdates EXCEPT ![self[1]] = setScheduledRoleUpdates[self[1]] \cup {currSW'[self]}]
                                                              /\ UNCHANGED << nibEventQueue, 
                                                                              event >>
                                                   /\ pc' = [pc EXCEPT ![self] = "NibEventHandlerProc"]
                                                   /\ UNCHANGED << ofcModuleTerminationStatus, 
                                                                   subscribeList >>
                                        /\ UNCHANGED << isOfcEnabled, swSet >>
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             controllerRoleInSW, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, 
                                             ofcFailoverStateNIB, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, IRQueueEntries, entry, 
                                             nextToSent, entryIndex, rowIndex, 
                                             rowRemove, removeRow, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, 
                                             controllerFailedModules >>

ScheduleRoleUpdateEqual(self) == /\ pc[self] = "ScheduleRoleUpdateEqual"
                                 /\ currSW' = [currSW EXCEPT ![self] = CHOOSE x \in swSet[self]: TRUE]
                                 /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> ([type |-> ROLE_REQ, roletype |-> ROLE_EQUAL, to |-> currSW'[self]]), id |-> -1, tag |-> NO_TAG])]
                                 /\ swSet' = [swSet EXCEPT ![self] = swSet[self] \ {currSW'[self]}]
                                 /\ IF swSet'[self] = {}
                                       THEN /\ pc' = [pc EXCEPT ![self] = "WaitForSwitchUpdateRoleACK"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ScheduleRoleUpdateEqual"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 installedBy, swFailedNum, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 switchControllerRoleStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, 
                                                 dependencyGraph, IR2SW, 
                                                 irCounter, MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 controllerRoleInSW, 
                                                 nibEventQueue, 
                                                 roleUpdateStatus, 
                                                 isOfcEnabled, 
                                                 setScheduledRoleUpdates, 
                                                 ofcModuleTerminationStatus, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, subscribeList, 
                                                 SetScheduledIRs, 
                                                 ofcFailoverStateNIB, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, 
                                                 subscriberOfcSet, ofcID, 
                                                 event, IRQueueEntries, entry, 
                                                 nextToSent, entryIndex, 
                                                 rowIndex, rowRemove, 
                                                 removeRow, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, 
                                                 controllerFailedModules >>

WaitForSwitchUpdateRoleACK(self) == /\ pc[self] = "WaitForSwitchUpdateRoleACK"
                                    /\ allSwitchInEqualRole(self[1])
                                    /\ subscribeList' = [subscribeList EXCEPT !.IRQueueNIB = subscribeList.IRQueueNIB \cup {self[1]}]
                                    /\ IRQueueEntries' = [IRQueueEntries EXCEPT ![self] = IRQueueNIB]
                                    /\ pc' = [pc EXCEPT ![self] = "QueryIRQueueNIB"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    installedBy, swFailedNum, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    workerLocalQueue, 
                                                    controllerRoleInSW, 
                                                    nibEventQueue, 
                                                    roleUpdateStatus, 
                                                    isOfcEnabled, 
                                                    setScheduledRoleUpdates, 
                                                    ofcModuleTerminationStatus, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ofcFailoverStateNIB, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    subscriberOfcSet, ofcID, 
                                                    event, swSet, currSW, 
                                                    entry, nextToSent, 
                                                    entryIndex, rowIndex, 
                                                    rowRemove, removeRow, 
                                                    stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, 
                                                    controllerFailedModules >>

QueryIRQueueNIB(self) == /\ pc[self] = "QueryIRQueueNIB"
                         /\ IF IRQueueEntries[self] # <<>>
                               THEN /\ entry' = [entry EXCEPT ![self] = Head(IRQueueEntries[self])]
                                    /\ IRQueueEntries' = [IRQueueEntries EXCEPT ![self] = Tail(IRQueueEntries[self])]
                                    /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> entry'[self], id |-> -1, tag |-> NO_TAG])]
                                    /\ pc' = [pc EXCEPT ![self] = "QueryIRQueueNIB"]
                                    /\ UNCHANGED ofcFailoverStateNIB
                               ELSE /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![self[1]] = FAILOVER_READY]
                                    /\ pc' = [pc EXCEPT ![self] = "WaitForRoleMaster"]
                                    /\ UNCHANGED << workerLocalQueue, 
                                                    IRQueueEntries, entry >>
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstall, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, installedBy, 
                                         swFailedNum, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         switchControllerRoleStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         controllerRoleInSW, nibEventQueue, 
                                         roleUpdateStatus, isOfcEnabled, 
                                         setScheduledRoleUpdates, 
                                         ofcModuleTerminationStatus, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, subscribeList, 
                                         SetScheduledIRs, ingressPkt, 
                                         ingressIR, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, toBeScheduledIRs, 
                                         nextIR, stepOfFailure_, 
                                         subscriberOfcSet, ofcID, event, swSet, 
                                         currSW, nextToSent, entryIndex, 
                                         rowIndex, rowRemove, removeRow, 
                                         stepOfFailure_c, monitoringEvent, 
                                         setIRsToReset, resetIR, stepOfFailure, 
                                         msg, controllerFailedModules >>

WaitForRoleMaster(self) == /\ pc[self] = "WaitForRoleMaster"
                           /\ masterState[self[1]] = ROLE_MASTER
                           /\ pc' = [pc EXCEPT ![self] = "NibEventHandlerProc"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, installedBy, 
                                           swFailedNum, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           switchControllerRoleStatus, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           IR2SW, irCounter, MAX_IR_COUNTER, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, 
                                           workerLocalQueue, 
                                           controllerRoleInSW, nibEventQueue, 
                                           roleUpdateStatus, isOfcEnabled, 
                                           setScheduledRoleUpdates, 
                                           ofcModuleTerminationStatus, 
                                           masterState, controllerStateNIB, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, subscribeList, 
                                           SetScheduledIRs, 
                                           ofcFailoverStateNIB, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, toBeScheduledIRs, 
                                           nextIR, stepOfFailure_, 
                                           subscriberOfcSet, ofcID, event, 
                                           swSet, currSW, IRQueueEntries, 
                                           entry, nextToSent, entryIndex, 
                                           rowIndex, rowRemove, removeRow, 
                                           stepOfFailure_c, monitoringEvent, 
                                           setIRsToReset, resetIR, 
                                           stepOfFailure, msg, 
                                           controllerFailedModules >>

WaitForWorkersTermination(self) == /\ pc[self] = "WaitForWorkersTermination"
                                   /\ allWorkersTerminated(self[1])
                                   /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]] = [y \in {CONT_MONITOR, CONT_EVENT} |-> TERMINATE_INIT]
                                                                                                                                         @@ ofcModuleTerminationStatus[self[1]]]
                                   /\ pc' = [pc EXCEPT ![self] = "WaitForAllModulesTermination"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   installedBy, swFailedNum, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switchControllerRoleStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   dependencyGraph, IR2SW, 
                                                   irCounter, MAX_IR_COUNTER, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   workerLocalQueue, 
                                                   controllerRoleInSW, 
                                                   nibEventQueue, 
                                                   roleUpdateStatus, 
                                                   isOfcEnabled, 
                                                   setScheduledRoleUpdates, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   IRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, subscribeList, 
                                                   SetScheduledIRs, 
                                                   ofcFailoverStateNIB, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   subscriberOfcSet, ofcID, 
                                                   event, swSet, currSW, 
                                                   IRQueueEntries, entry, 
                                                   nextToSent, entryIndex, 
                                                   rowIndex, rowRemove, 
                                                   removeRow, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, 
                                                   controllerFailedModules >>

WaitForAllModulesTermination(self) == /\ pc[self] = "WaitForAllModulesTermination"
                                      /\ allModulesTerminated(self[1])
                                      /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![self[1]] = FAILOVER_TERMINATE_DONE]
                                      /\ pc' = [pc EXCEPT ![self] = "NibEventHandlerProc"]
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
                                                      installedBy, swFailedNum, 
                                                      NicAsic2OfaBuff, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchControllerRoleStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      workerLocalQueue, 
                                                      controllerRoleInSW, 
                                                      nibEventQueue, 
                                                      roleUpdateStatus, 
                                                      isOfcEnabled, 
                                                      setScheduledRoleUpdates, 
                                                      ofcModuleTerminationStatus, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      subscribeList, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      subscriberOfcSet, ofcID, 
                                                      event, swSet, currSW, 
                                                      IRQueueEntries, entry, 
                                                      nextToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      removeRow, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
                                                      controllerFailedModules >>

nibEventHandler(self) == NibEventHandlerProc(self)
                            \/ ScheduleRoleUpdateEqual(self)
                            \/ WaitForSwitchUpdateRoleACK(self)
                            \/ QueryIRQueueNIB(self)
                            \/ WaitForRoleMaster(self)
                            \/ WaitForWorkersTermination(self)
                            \/ WaitForAllModulesTermination(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ IF ~shouldWorkerTerminate(self[1], self[2])
                                THEN /\ isOfcEnabled[self[1]]
                                     /\ moduleIsUp(self)
                                     /\ workerLocalQueue # <<>>
                                     /\ canWorkerThreadContinue(self[1], self)
                                     /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                     /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead((workerLocalQueue[self[1]]), self)]
                                     /\ nextToSent' = [nextToSent EXCEPT ![self] = (workerLocalQueue[self[1]])[rowIndex'[self]].item]
                                     /\ IF existEquivalentItemWithID((workerLocalQueue[self[1]]), nextToSent'[self])
                                           THEN /\ entryIndex' = [entryIndex EXCEPT ![self] = getIdOfEquivalentItem((workerLocalQueue[self[1]]), nextToSent'[self])]
                                                /\ UNCHANGED irCounter
                                           ELSE /\ irCounter' = (irCounter + 1) % MAX_IR_COUNTER
                                                /\ entryIndex' = [entryIndex EXCEPT ![self] = irCounter']
                                     /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]][rowIndex'[self]].tag = self,
                                                                                     ![self[1]][rowIndex'[self]].id = entryIndex'[self]]
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
                                           ELSE /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextToSent'[self], index |-> entryIndex'[self]]]
                                                /\ IF (stepOfFailure_c'[self] = 2)
                                                      THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                           /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                           /\ UNCHANGED idThreadWorkingOnIR
                                                      ELSE /\ IF idThreadWorkingOnIR[self[1]][entryIndex'[self]] = IR_UNLOCK
                                                                 THEN /\ threadWithLowerIDGetsTheLock(self[1], self, nextToSent'[self], workerLocalQueue'[self[1]])
                                                                      /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![self[1]][entryIndex'[self]] = self[2]]
                                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveQueue1"]
                                                                      /\ UNCHANGED idThreadWorkingOnIR
                                                           /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                           controllerSubmoduleFailStat >>
                                     /\ UNCHANGED ofcModuleTerminationStatus
                                ELSE /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]][self[2]] = TERMINATE_DONE]
                                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     irCounter, 
                                                     idThreadWorkingOnIR, 
                                                     workerLocalQueue, 
                                                     controllerStateNIB, 
                                                     nextToSent, entryIndex, 
                                                     rowIndex, stepOfFailure_c >>
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          installedBy, swFailedNum, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          switchControllerRoleStatus, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, MAX_IR_COUNTER, 
                                          workerThreadRanking, 
                                          controllerRoleInSW, nibEventQueue, 
                                          roleUpdateStatus, isOfcEnabled, 
                                          setScheduledRoleUpdates, masterState, 
                                          IRStatus, SwSuspensionStatus, 
                                          IRQueueNIB, subscribeList, 
                                          SetScheduledIRs, ofcFailoverStateNIB, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, subscriberOfcSet, 
                                          ofcID, event, swSet, currSW, 
                                          IRQueueEntries, entry, rowRemove, 
                                          removeRow, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure, msg, 
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
                                      THEN /\ IF workerCanSendTheIR(self[1], nextToSent[self])
                                                 THEN /\ Assert(nextToSent[self].type \in {INSTALL_FLOW, ROLE_REQ}, 
                                                                "Failure of assertion at line 1710, column 21.")
                                                      /\ IF nextToSent[self].type = INSTALL_FLOW
                                                            THEN /\ IRStatus' = [IRStatus EXCEPT ![nextToSent[self].IR] = IR_SENT]
                                                                 /\ UNCHANGED roleUpdateStatus
                                                            ELSE /\ IF nextToSent[self].type = ROLE_REQ
                                                                       THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][nextToSent[self].to] = IR_SENT]
                                                                       ELSE /\ TRUE
                                                                            /\ UNCHANGED roleUpdateStatus
                                                                 /\ UNCHANGED IRStatus
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                                      /\ UNCHANGED << roleUpdateStatus, 
                                                                      IRStatus >>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                           /\ UNCHANGED << roleUpdateStatus, 
                                                           IRStatus >>
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                installedBy, swFailedNum, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchControllerRoleStatus, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                controllerRoleInSW, 
                                                nibEventQueue, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                masterState, 
                                                controllerStateNIB, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                subscribeList, SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, 
                                                subscriberOfcSet, ofcID, event, 
                                                swSet, currSW, IRQueueEntries, 
                                                entry, nextToSent, entryIndex, 
                                                rowIndex, rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..2:
                                                   stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure_c'[self] # 1)
                                         THEN /\ IF nextToSent[self].type = INSTALL_FLOW
                                                    THEN /\ controller2Switch' = [controller2Switch EXCEPT ![nextToSent[self].to] = Append(controller2Switch[nextToSent[self].to], [type |-> INSTALL_FLOW,
                                                                                                                                                                                    from |-> self[1],
                                                                                                                                                                                    to |-> nextToSent[self].to,
                                                                                                                                                                                    IR |-> nextToSent[self].IR])]
                                                    ELSE /\ IF nextToSent[self].type = ROLE_REQ
                                                               THEN /\ controller2Switch' = [controller2Switch EXCEPT ![nextToSent[self].to] = Append(controller2Switch[nextToSent[self].to], [type |-> ROLE_REQ,
                                                                                                                                                                                               from |-> self[1],
                                                                                                                                                                                               to |-> nextToSent[self].to,
                                                                                                                                                                                               roletype |-> nextToSent[self].roletype])]
                                                               ELSE /\ TRUE
                                                                    /\ UNCHANGED controller2Switch
                                              /\ IF whichSwitchModel(nextToSent[self].to) = SW_COMPLEX_MODEL
                                                    THEN /\ switchLock' = <<NIC_ASIC_IN, nextToSent[self].to>>
                                                    ELSE /\ switchLock' = <<SW_SIMPLE_ID, nextToSent[self].to>>
                                              /\ IF (stepOfFailure_c'[self] # 2)
                                                    THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_SENT_DONE,
                                                                                                                        next |-> nextToSent[self],
                                                                                                                        index |-> entryIndex[self]]]
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
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ UNCHANGED << controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   installedBy, swFailedNum, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switchControllerRoleStatus, 
                                                   switchOrdering, 
                                                   dependencyGraph, IR2SW, 
                                                   irCounter, MAX_IR_COUNTER, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   workerLocalQueue, 
                                                   controllerRoleInSW, 
                                                   nibEventQueue, 
                                                   roleUpdateStatus, 
                                                   isOfcEnabled, 
                                                   setScheduledRoleUpdates, 
                                                   ofcModuleTerminationStatus, 
                                                   masterState, IRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, subscribeList, 
                                                   SetScheduledIRs, 
                                                   ofcFailoverStateNIB, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   subscriberOfcSet, ofcID, 
                                                   event, swSet, currSW, 
                                                   IRQueueEntries, entry, 
                                                   nextToSent, entryIndex, 
                                                   rowIndex, rowRemove, 
                                                   removeRow, monitoringEvent, 
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
                                               THEN /\ IF idThreadWorkingOnIR[self[1]][entryIndex[self]] = self[2]
                                                          THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![self[1]][entryIndex[self]] = IR_UNLOCK]
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
                                                         installedBy, 
                                                         swFailedNum, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Installer2OfaBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         switchControllerRoleStatus, 
                                                         switchOrdering, 
                                                         dependencyGraph, 
                                                         IR2SW, irCounter, 
                                                         MAX_IR_COUNTER, 
                                                         workerThreadRanking, 
                                                         workerLocalQueue, 
                                                         controllerRoleInSW, 
                                                         nibEventQueue, 
                                                         roleUpdateStatus, 
                                                         isOfcEnabled, 
                                                         setScheduledRoleUpdates, 
                                                         ofcModuleTerminationStatus, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         subscribeList, 
                                                         SetScheduledIRs, 
                                                         ofcFailoverStateNIB, 
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
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         subscriberOfcSet, 
                                                         ofcID, event, swSet, 
                                                         currSW, 
                                                         IRQueueEntries, entry, 
                                                         nextToSent, 
                                                         entryIndex, rowIndex, 
                                                         rowRemove, removeRow, 
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
                                        THEN /\ IF nextToSent[self].type = INSTALL_FLOW
                                                   THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextToSent[self].to] = SetScheduledIRs[nextToSent[self].to]\{nextToSent[self].IR}]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED SetScheduledIRs
                                             /\ IF (stepOfFailure_c'[self] # 2)
                                                   THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                        /\ IF (stepOfFailure_c'[self] # 3)
                                                              THEN /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith((workerLocalQueue[self[1]]), nextToSent[self], self)]
                                                                   /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = removeFromSeq((workerLocalQueue[self[1]]), rowRemove'[self])]
                                                                   /\ IF nextToSent[self].type = INSTALL_FLOW
                                                                         THEN /\ IF existsEquivalentItem(IRQueueNIB, nextToSent[self])
                                                                                    THEN /\ removeRow' = [removeRow EXCEPT ![self] = CHOOSE x \in DOMAIN IRQueueNIB: isIdenticalElement(IRQueueNIB[x], nextToSent[self])]
                                                                                         /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                                                                    ELSE /\ TRUE
                                                                                         /\ UNCHANGED << IRQueueNIB, 
                                                                                                         removeRow >>
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED << IRQueueNIB, 
                                                                                              removeRow >>
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << workerLocalQueue, 
                                                                                   IRQueueNIB, 
                                                                                   rowRemove, 
                                                                                   removeRow >>
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << workerLocalQueue, 
                                                                        controllerStateNIB, 
                                                                        IRQueueNIB, 
                                                                        rowRemove, 
                                                                        removeRow >>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << workerLocalQueue, 
                                                             controllerStateNIB, 
                                                             IRQueueNIB, 
                                                             SetScheduledIRs, 
                                                             rowRemove, 
                                                             removeRow >>
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
                                                  installedBy, swFailedNum, 
                                                  NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  switchControllerRoleStatus, 
                                                  switchOrdering, 
                                                  dependencyGraph, IR2SW, 
                                                  irCounter, MAX_IR_COUNTER, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  controllerRoleInSW, 
                                                  nibEventQueue, 
                                                  roleUpdateStatus, 
                                                  isOfcEnabled, 
                                                  setScheduledRoleUpdates, 
                                                  ofcModuleTerminationStatus, 
                                                  masterState, IRStatus, 
                                                  SwSuspensionStatus, 
                                                  subscribeList, 
                                                  ofcFailoverStateNIB, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, 
                                                  subscriberOfcSet, ofcID, 
                                                  event, swSet, currSW, 
                                                  IRQueueEntries, entry, 
                                                  nextToSent, entryIndex, 
                                                  rowIndex, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, 
                                                  controllerFailedModules >>

ControllerThreadRemoveQueue1(self) == /\ pc[self] = "ControllerThreadRemoveQueue1"
                                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith((workerLocalQueue[self[1]]), nextToSent[self], self)]
                                      /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = removeFromSeq((workerLocalQueue[self[1]]), rowRemove'[self])]
                                      /\ IF nextToSent[self].type = INSTALL_FLOW
                                            THEN /\ IF existsEquivalentItem(IRQueueNIB, nextToSent[self])
                                                       THEN /\ removeRow' = [removeRow EXCEPT ![self] = CHOOSE x \in DOMAIN IRQueueNIB: isIdenticalElement(IRQueueNIB[x], nextToSent[self])]
                                                            /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED << IRQueueNIB, 
                                                                            removeRow >>
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << IRQueueNIB, 
                                                                 removeRow >>
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
                                                      installedBy, swFailedNum, 
                                                      NicAsic2OfaBuff, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchControllerRoleStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      controllerRoleInSW, 
                                                      nibEventQueue, 
                                                      roleUpdateStatus, 
                                                      isOfcEnabled, 
                                                      setScheduledRoleUpdates, 
                                                      ofcModuleTerminationStatus, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      subscribeList, 
                                                      SetScheduledIRs, 
                                                      ofcFailoverStateNIB, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      subscriberOfcSet, ofcID, 
                                                      event, swSet, currSW, 
                                                      IRQueueEntries, entry, 
                                                      nextToSent, entryIndex, 
                                                      rowIndex, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, 
                                                      controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ isOfcEnabled[self[1]]
                                             /\ moduleIsUp(self)
                                             /\ IRQueueNIB # <<>>
                                             /\ canWorkerThreadContinue(self[1], self)
                                             /\ \/ controllerLock = self
                                                \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (controllerStateNIB[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (controllerStateNIB[self].next.type = INSTALL_FLOW)
                                                              THEN /\ IF (IRStatus[controllerStateNIB[self].next.IR] = IR_SENT)
                                                                         THEN /\ IRStatus' = [IRStatus EXCEPT ![controllerStateNIB[self].next.IR] = IR_NONE]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED IRStatus
                                                                   /\ UNCHANGED roleUpdateStatus
                                                              ELSE /\ IF (controllerStateNIB[self].next.type = ROLE_REQ)
                                                                         THEN /\ IF (roleUpdateStatus[self[1]][controllerStateNIB[self].next.to] = IR_SENT)
                                                                                    THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][controllerStateNIB[self].next.to] = IR_NONE]
                                                                                    ELSE /\ TRUE
                                                                                         /\ UNCHANGED roleUpdateStatus
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED roleUpdateStatus
                                                                   /\ UNCHANGED IRStatus
                                                        /\ IF (idThreadWorkingOnIR[self[1]][controllerStateNIB[self].index] = self[2])
                                                              THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![self[1]][controllerStateNIB[self].index] = IR_UNLOCK]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                        /\ UNCHANGED SetScheduledIRs
                                                   ELSE /\ IF (controllerStateNIB[self].type = STATUS_SENT_DONE)
                                                              THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![controllerStateNIB[self].next.to] = SetScheduledIRs[controllerStateNIB[self].next.to] \cup {controllerStateNIB[self].next.IR}]
                                                                   /\ IF (idThreadWorkingOnIR[self[1]][controllerStateNIB[self].index] = self[2])
                                                                         THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![self[1]][controllerStateNIB[self].index] = IR_UNLOCK]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED idThreadWorkingOnIR
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << idThreadWorkingOnIR, 
                                                                                   SetScheduledIRs >>
                                                        /\ UNCHANGED << roleUpdateStatus, 
                                                                        IRStatus >>
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
                                                             installedBy, 
                                                             swFailedNum, 
                                                             NicAsic2OfaBuff, 
                                                             Ofa2NicAsicBuff, 
                                                             Installer2OfaBuff, 
                                                             Ofa2InstallerBuff, 
                                                             TCAM, 
                                                             controlMsgCounter, 
                                                             switchControllerRoleStatus, 
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             switchOrdering, 
                                                             dependencyGraph, 
                                                             IR2SW, irCounter, 
                                                             MAX_IR_COUNTER, 
                                                             workerThreadRanking, 
                                                             workerLocalQueue, 
                                                             controllerRoleInSW, 
                                                             nibEventQueue, 
                                                             isOfcEnabled, 
                                                             setScheduledRoleUpdates, 
                                                             ofcModuleTerminationStatus, 
                                                             masterState, 
                                                             controllerStateNIB, 
                                                             SwSuspensionStatus, 
                                                             IRQueueNIB, 
                                                             subscribeList, 
                                                             ofcFailoverStateNIB, 
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
                                                             stepOfFailure_, 
                                                             subscriberOfcSet, 
                                                             ofcID, event, 
                                                             swSet, currSW, 
                                                             IRQueueEntries, 
                                                             entry, nextToSent, 
                                                             entryIndex, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             removeRow, 
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
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadRemoveQueue1(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ IF ~shouldEventHandlerTerminate(self[1])
                                          THEN /\ isOfcEnabled[self[1]]
                                               /\ moduleIsUp(self)
                                               /\ swSeqChangedStatus[self[1]] # <<>>
                                               /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                               /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus[self[1]])]
                                               /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                                     ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                               /\ UNCHANGED ofcModuleTerminationStatus
                                          ELSE /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]][self[2]] = TERMINATE_DONE]
                                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                                               /\ UNCHANGED monitoringEvent
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    installedBy, swFailedNum, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    workerLocalQueue, 
                                                    controllerRoleInSW, 
                                                    nibEventQueue, 
                                                    roleUpdateStatus, 
                                                    isOfcEnabled, 
                                                    setScheduledRoleUpdates, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, subscribeList, 
                                                    SetScheduledIRs, 
                                                    ofcFailoverStateNIB, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    subscriberOfcSet, ofcID, 
                                                    event, swSet, currSW, 
                                                    IRQueueEntries, entry, 
                                                    nextToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    removeRow, stepOfFailure_c, 
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
                                                                    THEN /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![self[1]] = Tail(swSeqChangedStatus[self[1]])]
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
                                                                   installedBy, 
                                                                   swFailedNum, 
                                                                   NicAsic2OfaBuff, 
                                                                   Ofa2NicAsicBuff, 
                                                                   Installer2OfaBuff, 
                                                                   Ofa2InstallerBuff, 
                                                                   TCAM, 
                                                                   controlMsgCounter, 
                                                                   switchControllerRoleStatus, 
                                                                   switchOrdering, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   irCounter, 
                                                                   MAX_IR_COUNTER, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   workerLocalQueue, 
                                                                   controllerRoleInSW, 
                                                                   nibEventQueue, 
                                                                   roleUpdateStatus, 
                                                                   isOfcEnabled, 
                                                                   setScheduledRoleUpdates, 
                                                                   ofcModuleTerminationStatus, 
                                                                   masterState, 
                                                                   IRStatus, 
                                                                   SwSuspensionStatus, 
                                                                   IRQueueNIB, 
                                                                   subscribeList, 
                                                                   SetScheduledIRs, 
                                                                   ofcFailoverStateNIB, 
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
                                                                   stepOfFailure_, 
                                                                   subscriberOfcSet, 
                                                                   ofcID, 
                                                                   event, 
                                                                   swSet, 
                                                                   currSW, 
                                                                   IRQueueEntries, 
                                                                   entry, 
                                                                   nextToSent, 
                                                                   entryIndex, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   removeRow, 
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
                                             installedIRs, installedBy, 
                                             swFailedNum, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, IRQueueNIB, 
                                             subscribeList, SetScheduledIRs, 
                                             ofcFailoverStateNIB, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event, swSet, currSW, 
                                             IRQueueEntries, entry, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
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
                                                   installedBy, swFailedNum, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switchControllerRoleStatus, 
                                                   switchOrdering, 
                                                   dependencyGraph, IR2SW, 
                                                   irCounter, MAX_IR_COUNTER, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   workerLocalQueue, 
                                                   controllerRoleInSW, 
                                                   nibEventQueue, 
                                                   roleUpdateStatus, 
                                                   isOfcEnabled, 
                                                   setScheduledRoleUpdates, 
                                                   ofcModuleTerminationStatus, 
                                                   masterState, IRStatus, 
                                                   IRQueueNIB, subscribeList, 
                                                   SetScheduledIRs, 
                                                   ofcFailoverStateNIB, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   subscriberOfcSet, ofcID, 
                                                   event, swSet, currSW, 
                                                   IRQueueEntries, entry, 
                                                   nextToSent, entryIndex, 
                                                   rowIndex, rowRemove, 
                                                   removeRow, stepOfFailure_c, 
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
                                                THEN /\ IF ~existsMonitoringEventHigherNum(monitoringEvent[self], self[1])
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
                                                          installedBy, 
                                                          swFailedNum, 
                                                          NicAsic2OfaBuff, 
                                                          Ofa2NicAsicBuff, 
                                                          Installer2OfaBuff, 
                                                          Ofa2InstallerBuff, 
                                                          TCAM, 
                                                          controlMsgCounter, 
                                                          switchControllerRoleStatus, 
                                                          switchOrdering, 
                                                          dependencyGraph, 
                                                          IR2SW, irCounter, 
                                                          MAX_IR_COUNTER, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          workerLocalQueue, 
                                                          controllerRoleInSW, 
                                                          nibEventQueue, 
                                                          roleUpdateStatus, 
                                                          isOfcEnabled, 
                                                          setScheduledRoleUpdates, 
                                                          ofcModuleTerminationStatus, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          subscribeList, 
                                                          SetScheduledIRs, 
                                                          ofcFailoverStateNIB, 
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
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          subscriberOfcSet, 
                                                          ofcID, event, swSet, 
                                                          currSW, 
                                                          IRQueueEntries, 
                                                          entry, nextToSent, 
                                                          entryIndex, rowIndex, 
                                                          rowRemove, removeRow, 
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
                                           installedIRs, installedBy, 
                                           swFailedNum, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           switchControllerRoleStatus, 
                                           switchOrdering, dependencyGraph, 
                                           IR2SW, irCounter, MAX_IR_COUNTER, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, 
                                           workerLocalQueue, 
                                           controllerRoleInSW, nibEventQueue, 
                                           roleUpdateStatus, isOfcEnabled, 
                                           setScheduledRoleUpdates, 
                                           ofcModuleTerminationStatus, 
                                           masterState, controllerStateNIB, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, subscribeList, 
                                           SetScheduledIRs, 
                                           ofcFailoverStateNIB, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, toBeScheduledIRs, 
                                           nextIR, stepOfFailure_, 
                                           subscriberOfcSet, ofcID, event, 
                                           swSet, currSW, IRQueueEntries, 
                                           entry, nextToSent, entryIndex, 
                                           rowIndex, rowRemove, removeRow, 
                                           stepOfFailure_c, monitoringEvent, 
                                           resetIR, stepOfFailure, msg, 
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
                                     switchStatus, installedIRs, installedBy, 
                                     swFailedNum, NicAsic2OfaBuff, 
                                     Ofa2NicAsicBuff, Installer2OfaBuff, 
                                     Ofa2InstallerBuff, TCAM, 
                                     controlMsgCounter, 
                                     switchControllerRoleStatus, 
                                     switchOrdering, dependencyGraph, IR2SW, 
                                     irCounter, MAX_IR_COUNTER, 
                                     idThreadWorkingOnIR, workerThreadRanking, 
                                     workerLocalQueue, controllerRoleInSW, 
                                     nibEventQueue, roleUpdateStatus, 
                                     isOfcEnabled, setScheduledRoleUpdates, 
                                     ofcModuleTerminationStatus, masterState, 
                                     controllerStateNIB, SwSuspensionStatus, 
                                     IRQueueNIB, subscribeList, 
                                     SetScheduledIRs, ofcFailoverStateNIB, 
                                     ingressPkt, ingressIR, egressMsg, 
                                     ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, failedSet, statusResolveMsg, 
                                     recoveredElem, toBeScheduledIRs, nextIR, 
                                     stepOfFailure_, subscriberOfcSet, ofcID, 
                                     event, swSet, currSW, IRQueueEntries, 
                                     entry, nextToSent, entryIndex, rowIndex, 
                                     rowRemove, removeRow, stepOfFailure_c, 
                                     monitoringEvent, stepOfFailure, msg, 
                                     controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ isOfcEnabled[self[1]]
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus[self[1]] # <<>>
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
                                                                   installedBy, 
                                                                   swFailedNum, 
                                                                   NicAsic2OfaBuff, 
                                                                   Ofa2NicAsicBuff, 
                                                                   Installer2OfaBuff, 
                                                                   Ofa2InstallerBuff, 
                                                                   TCAM, 
                                                                   controlMsgCounter, 
                                                                   switchControllerRoleStatus, 
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   switchOrdering, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   irCounter, 
                                                                   MAX_IR_COUNTER, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   workerLocalQueue, 
                                                                   controllerRoleInSW, 
                                                                   nibEventQueue, 
                                                                   roleUpdateStatus, 
                                                                   isOfcEnabled, 
                                                                   setScheduledRoleUpdates, 
                                                                   ofcModuleTerminationStatus, 
                                                                   masterState, 
                                                                   controllerStateNIB, 
                                                                   IRStatus, 
                                                                   IRQueueNIB, 
                                                                   subscribeList, 
                                                                   SetScheduledIRs, 
                                                                   ofcFailoverStateNIB, 
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
                                                                   stepOfFailure_, 
                                                                   subscriberOfcSet, 
                                                                   ofcID, 
                                                                   event, 
                                                                   swSet, 
                                                                   currSW, 
                                                                   IRQueueEntries, 
                                                                   entry, 
                                                                   nextToSent, 
                                                                   entryIndex, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   removeRow, 
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
                                       /\ IF ~shouldMonitoringServerTerminate(self[1])
                                             THEN /\ isOfcEnabled[self[1]]
                                                  /\ moduleIsUp(self)
                                                  /\ switch2Controller[self[1]] # <<>>
                                                  /\ \/ controllerLock = self
                                                     \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                  /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                  /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller[self[1]])]
                                                  /\ Assert(\/ /\ msg'[self].type = INSTALLED_SUCCESSFULLY
                                                               /\ msg'[self].from = IR2SW[msg'[self].IR]
                                                            \/ msg'[self].type \in {ROLE_REPLY, BAD_REQUEST}, 
                                                            "Failure of assertion at line 2053, column 9.")
                                                  /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIR2"]
                                                        ELSE /\ IF msg'[self].type = ROLE_REPLY
                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateRole"]
                                                                   ELSE /\ IF msg'[self].type = BAD_REQUEST
                                                                              THEN /\ TRUE
                                                                              ELSE /\ Assert(FALSE, 
                                                                                             "Failure of assertion at line 2104, column 18.")
                                                                        /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                                  /\ UNCHANGED ofcModuleTerminationStatus
                                             ELSE /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]][self[2]] = TERMINATE_DONE]
                                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                  /\ UNCHANGED << controllerLock, 
                                                                  msg >>
                                       /\ UNCHANGED << switchLock, 
                                                       FirstInstall, 
                                                       sw_fail_ordering_var, 
                                                       ContProcSet, SwProcSet, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       switchStatus, 
                                                       installedIRs, 
                                                       installedBy, 
                                                       swFailedNum, 
                                                       NicAsic2OfaBuff, 
                                                       Ofa2NicAsicBuff, 
                                                       Installer2OfaBuff, 
                                                       Ofa2InstallerBuff, TCAM, 
                                                       controlMsgCounter, 
                                                       switchControllerRoleStatus, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       switchOrdering, 
                                                       dependencyGraph, IR2SW, 
                                                       irCounter, 
                                                       MAX_IR_COUNTER, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       workerLocalQueue, 
                                                       controllerRoleInSW, 
                                                       nibEventQueue, 
                                                       roleUpdateStatus, 
                                                       isOfcEnabled, 
                                                       setScheduledRoleUpdates, 
                                                       masterState, 
                                                       controllerStateNIB, 
                                                       IRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       subscribeList, 
                                                       SetScheduledIRs, 
                                                       ofcFailoverStateNIB, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       subscriberOfcSet, ofcID, 
                                                       event, swSet, currSW, 
                                                       IRQueueEntries, entry, 
                                                       nextToSent, entryIndex, 
                                                       rowIndex, rowRemove, 
                                                       removeRow, 
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
                                               THEN /\ switch2Controller' = [switch2Controller EXCEPT ![self[1]] = Tail(switch2Controller[self[1]])]
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
                                                         installedBy, 
                                                         swFailedNum, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Installer2OfaBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         switchControllerRoleStatus, 
                                                         switchOrdering, 
                                                         dependencyGraph, 
                                                         IR2SW, irCounter, 
                                                         MAX_IR_COUNTER, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         workerLocalQueue, 
                                                         controllerRoleInSW, 
                                                         nibEventQueue, 
                                                         roleUpdateStatus, 
                                                         isOfcEnabled, 
                                                         setScheduledRoleUpdates, 
                                                         ofcModuleTerminationStatus, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         subscribeList, 
                                                         SetScheduledIRs, 
                                                         ofcFailoverStateNIB, 
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
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         subscriberOfcSet, 
                                                         ofcID, event, swSet, 
                                                         currSW, 
                                                         IRQueueEntries, entry, 
                                                         nextToSent, 
                                                         entryIndex, rowIndex, 
                                                         rowRemove, removeRow, 
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
                                             installedIRs, installedBy, 
                                             swFailedNum, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             masterState, controllerStateNIB, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             subscribeList, SetScheduledIRs, 
                                             ofcFailoverStateNIB, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event, swSet, currSW, 
                                             IRQueueEntries, entry, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, 
                                             controllerFailedModules >>

ControllerUpdateRole(self) == /\ pc[self] = "ControllerUpdateRole"
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
                                    THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][msg[self].from] = IR_DONE]
                                         /\ controllerRoleInSW' = [controllerRoleInSW EXCEPT ![self[1]][msg[self].from] = msg[self].roletype]
                                         /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                         /\ UNCHANGED << controllerRoleInSW, 
                                                         roleUpdateStatus >>
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, installedBy, 
                                              swFailedNum, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              switchControllerRoleStatus, 
                                              switchOrdering, dependencyGraph, 
                                              IR2SW, irCounter, MAX_IR_COUNTER, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              workerLocalQueue, nibEventQueue, 
                                              isOfcEnabled, 
                                              setScheduledRoleUpdates, 
                                              ofcModuleTerminationStatus, 
                                              masterState, controllerStateNIB, 
                                              IRStatus, SwSuspensionStatus, 
                                              IRQueueNIB, subscribeList, 
                                              SetScheduledIRs, 
                                              ofcFailoverStateNIB, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, toBeScheduledIRs, 
                                              nextIR, stepOfFailure_, 
                                              subscriberOfcSet, ofcID, event, 
                                              swSet, currSW, IRQueueEntries, 
                                              entry, nextToSent, entryIndex, 
                                              rowIndex, rowRemove, removeRow, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, 
                                              controllerFailedModules >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerUpdateIR2(self)
                                       \/ ControllerUpdateRole(self)

ControllerWatchDogProc(self) == /\ pc[self] = "ControllerWatchDogProc"
                                /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerFailedModules' = [controllerFailedModules EXCEPT ![self] = returnControllerFailedModules(self[1])]
                                /\ Cardinality(controllerFailedModules'[self]) > 0
                                /\ \E module \in controllerFailedModules'[self]:
                                     /\ Assert(controllerSubmoduleFailStat[module] = Failed, 
                                               "Failure of assertion at line 2144, column 13.")
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
                                                installedBy, swFailedNum, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchControllerRoleStatus, 
                                                controllerSubmoduleFailNum, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                roleUpdateStatus, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                subscribeList, SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, 
                                                subscriberOfcSet, ofcID, event, 
                                                swSet, currSW, IRQueueEntries, 
                                                entry, nextToSent, entryIndex, 
                                                rowIndex, rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg >>

watchDog(self) == ControllerWatchDogProc(self)

OfcFailoverNewMasterInitialization(self) == /\ pc[self] = "OfcFailoverNewMasterInitialization"
                                            /\ SHOULD_FAILOVER = 1
                                            /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![ofc1] = FAILOVER_INIT]
                                            /\ pc' = [pc EXCEPT ![self] = "ofcFailoverCurrMasterTerminate"]
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
                                                            installedBy, 
                                                            swFailedNum, 
                                                            NicAsic2OfaBuff, 
                                                            Ofa2NicAsicBuff, 
                                                            Installer2OfaBuff, 
                                                            Ofa2InstallerBuff, 
                                                            TCAM, 
                                                            controlMsgCounter, 
                                                            switchControllerRoleStatus, 
                                                            controllerSubmoduleFailNum, 
                                                            controllerSubmoduleFailStat, 
                                                            switchOrdering, 
                                                            dependencyGraph, 
                                                            IR2SW, irCounter, 
                                                            MAX_IR_COUNTER, 
                                                            idThreadWorkingOnIR, 
                                                            workerThreadRanking, 
                                                            workerLocalQueue, 
                                                            controllerRoleInSW, 
                                                            nibEventQueue, 
                                                            roleUpdateStatus, 
                                                            isOfcEnabled, 
                                                            setScheduledRoleUpdates, 
                                                            ofcModuleTerminationStatus, 
                                                            masterState, 
                                                            controllerStateNIB, 
                                                            IRStatus, 
                                                            SwSuspensionStatus, 
                                                            IRQueueNIB, 
                                                            subscribeList, 
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
                                                            nextIR, 
                                                            stepOfFailure_, 
                                                            subscriberOfcSet, 
                                                            ofcID, event, 
                                                            swSet, currSW, 
                                                            IRQueueEntries, 
                                                            entry, nextToSent, 
                                                            entryIndex, 
                                                            rowIndex, 
                                                            rowRemove, 
                                                            removeRow, 
                                                            stepOfFailure_c, 
                                                            monitoringEvent, 
                                                            setIRsToReset, 
                                                            resetIR, 
                                                            stepOfFailure, msg, 
                                                            controllerFailedModules >>

ofcFailoverCurrMasterTerminate(self) == /\ pc[self] = "ofcFailoverCurrMasterTerminate"
                                        /\ ofcFailoverStateNIB[ofc1] = FAILOVER_READY
                                        /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![ofc0] = FAILOVER_TERMINATE]
                                        /\ pc' = [pc EXCEPT ![self] = "ofcFailoverChangeRoles"]
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
                                                        installedBy, 
                                                        swFailedNum, 
                                                        NicAsic2OfaBuff, 
                                                        Ofa2NicAsicBuff, 
                                                        Installer2OfaBuff, 
                                                        Ofa2InstallerBuff, 
                                                        TCAM, 
                                                        controlMsgCounter, 
                                                        switchControllerRoleStatus, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        dependencyGraph, IR2SW, 
                                                        irCounter, 
                                                        MAX_IR_COUNTER, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        workerLocalQueue, 
                                                        controllerRoleInSW, 
                                                        nibEventQueue, 
                                                        roleUpdateStatus, 
                                                        isOfcEnabled, 
                                                        setScheduledRoleUpdates, 
                                                        ofcModuleTerminationStatus, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        IRStatus, 
                                                        SwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        subscribeList, 
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
                                                        toBeScheduledIRs, 
                                                        nextIR, stepOfFailure_, 
                                                        subscriberOfcSet, 
                                                        ofcID, event, swSet, 
                                                        currSW, IRQueueEntries, 
                                                        entry, nextToSent, 
                                                        entryIndex, rowIndex, 
                                                        rowRemove, removeRow, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        controllerFailedModules >>

ofcFailoverChangeRoles(self) == /\ pc[self] = "ofcFailoverChangeRoles"
                                /\ ofcFailoverStateNIB[ofc0] = FAILOVER_TERMINATE_DONE
                                /\ masterState' = [masterState EXCEPT ![ofc0] = ROLE_SLAVE,
                                                                      ![ofc1] = ROLE_MASTER]
                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                installedBy, swFailedNum, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchControllerRoleStatus, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                roleUpdateStatus, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                subscribeList, SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, 
                                                subscriberOfcSet, ofcID, event, 
                                                swSet, currSW, IRQueueEntries, 
                                                entry, nextToSent, entryIndex, 
                                                rowIndex, rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                controllerFailedModules >>

failoverProc(self) == OfcFailoverNewMasterInitialization(self)
                         \/ ofcFailoverCurrMasterTerminate(self)
                         \/ ofcFailoverChangeRoles(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

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
           \/ (\E self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}): nibEventHandler(self))
           \/ (\E self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0, ofc1} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0, ofc1} \X {CONT_MONITOR}): controllerMonitoringServer(self))
           \/ (\E self \in (({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG}): watchDog(self))
           \/ (\E self \in ( {"proc"} \X {OFC_FAILOVER}): failoverProc(self))
           \/ Terminating

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
        /\ \A self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) : WF_vars(nibEventHandler(self))
        /\ \A self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0, ofc1} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0, ofc1} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in (({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG}) : WF_vars(watchDog(self))
        /\ \A self \in ( {"proc"} \X {OFC_FAILOVER}) : WF_vars(failoverProc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-8ddcbdbaa70b8ad761d15f13e25c7438
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
AllInstalled == (\A x \in 1..MAX_NUM_IRs: \E y \in DOMAIN installedIRs: installedIRs[y] = x)
AllDoneStatusController == (\A x \in 1..MAX_NUM_IRs: IRStatus[x] = IR_DONE)
InstallationLivenessProp == <>[] (/\ AllInstalled 
                                  /\ AllDoneStatusController)
                                  
isOFCfailoverDone == \/ SHOULD_FAILOVER = 0
                     \/ /\ SHOULD_FAILOVER = 1
                        /\ masterState[ofc0] = ROLE_SLAVE
                        /\ masterState[ofc1] = ROLE_MASTER

allSwitchCorrectMaster == \/ /\ SHOULD_FAILOVER = 0
                             /\ \A x \in SW: switchControllerRoleStatus[x][ofc0] = ROLE_MASTER
                             /\ \A x \in SW: switchControllerRoleStatus[x][ofc1] = ROLE_SLAVE  
                          \/ /\ SHOULD_FAILOVER = 1
                             /\ \A x \in SW: switchControllerRoleStatus[x][ofc0] = ROLE_SLAVE
                             /\ \A x \in SW: switchControllerRoleStatus[x][ofc1] = ROLE_MASTER
                             
OfcFailoverLivenessProp == <>[] (/\ isOFCfailoverDone
                                 /\ allSwitchCorrectMaster) 

\* Safety Properties
\* TODO(@Pooria) IRCriticalSection may need to check whether two workers from two different OFCs working on same IR is OK or not. 
IRCriticalSectionINV == LET 
                           IRCriticalSet == {"ControllerThreadSendIR", "ControllerThreadForwardIR", "ControllerThreadSaveToDB2", "WaitForIRToHaveCorrectStatus", "ReScheduleifIRNone"}
                        IN   
                           \A x, y \in {ofc0, ofc1} \X CONTROLLER_THREAD_POOL: \/ x = y
                                                                               \/ x[1] # y[1]
                                                                               \/ <<pc[x], pc[y]>> \notin IRCriticalSet \X IRCriticalSet
                                                                               \/ /\ <<pc[x], pc[y]>> \in IRCriticalSet \X IRCriticalSet
                                                                                  /\ isIdenticalElement(nextToSent[x], nextToSent[y])

RedundantInstallationINV == \A x \in 1..MAX_NUM_IRs: \/ IRStatus[x] = IR_DONE
                                                   \/ FirstInstall[x] = 0
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
ConsistencyReqINV == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                         \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)
                                                            /\ <<y, x>> \notin dependencyGraph
                                                         \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                            /\ <<x, y>> \notin dependencyGraph
EachIRAtMostOneOFCINV == \A x \in 1..MAX_NUM_IRs: Cardinality(installedBy[x]) < 2                                                         
EachSwitchAtMostOneMasterINV == \A x \in SW: ~\E y, z \in DOMAIN switchControllerRoleStatus[x]: /\ y # z 
                                                                                                /\ switchControllerRoleStatus[x][y] = ROLE_MASTER
                                                                                                /\ switchControllerRoleStatus[x][z] = ROLE_MASTER
=============================================================================
\* Modification History
\* Last modified Thu Dec 03 11:42:07 PST 2020 by root
\* Created Thu Dec 03 11:41:24 PST 2020 by root

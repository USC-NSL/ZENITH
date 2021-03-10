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
\* these two process mimic the failure and recovery of switch, and generating
\* async networking events (such as link failure, port down, etc.)
CONSTANTS SW_FAILURE_PROC,
          SW_RESOLVE_PROC,
          GHOST_UNLOCK_PROC,
          ASYNC_NET_EVE_GEN
          

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
          NIB_EVENT_HANDLER,
          \* id for NIB event handler (type: model value)
          FAILOVER_HANDLER 
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
          FAILOVER_NONE,
          INIT_NONE,
          INIT_RUN,
          INIT_PROCESS
          
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
          FLOW_STAT_REQ,
          ASYNC_EVENT,
          TOPO_MOD 
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
          SW_FAIL_ORDERING,
          SW_MAX_NUM_EVENTS,
          SW_MODULE_CAN_FAIL_OR_NOT,
          ROLE_EMPTY

    
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
(* DOMAIN of SW_MAX_NUM_EVENTS should cover all the switches *)
ASSUME /\ \A x \in SW: x \in DOMAIN SW_MAX_NUM_EVENTS
       /\ \A x \in DOMAIN SW_MAX_NUM_EVENTS: x \in SW
(* SW_MODULE_CAN_FAIL_OR_NOT should cover all the switch elements *)
ASSUME /\ "cpu" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "nicAsic" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "ofa" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "installer" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT


(*--fair algorithm stateConsistency
(************************* variables ***************************************)
    variables (*************** Some Auxiliary Vars ***********************)
              switchLock = <<NO_LOCK, NO_LOCK>>,
              controllerLocalLock = [x \in {ofc0, ofc1, rc0} |-> <<NO_LOCK, NO_LOCK>>],
              controllerGlobalLock = <<NO_LOCK, NO_LOCK>>, 
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
              
              \* auxiliary variable to make sure each switch generates at most
              \* SW_MAX_NUM_EVENT async events
              swNumEvent = [x \in SW |-> 0],
              
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
              
              \* auxiliary variable that stores all the events to make sure
              \* all of them are processed
              switchGeneratedEventSet = [x \in SW |-> {}],
              \* auxiliary event counter to make sure every event is processed
              auxEventCounter = 0,
              
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
              \* switch suspension status maintained locally
              ofcSwSuspensionStatus = [y \in {ofc0, ofc1} |-> [x \in SW |-> SW_RUN]],
              
              \************* Event Handler ****************
              \* auxiliary variable to check events processed by each OFC
              processedEvents = [x \in {ofc0, ofc1} |-> {}],
              \* event log per switch maintained locally
              localEventLog = [x \in {ofc0, ofc1} |-> [y \in SW |-> <<>>]],
              
              \************* NIB Event Handler ************
              \* this is what OFC thinks its role is in the switch 
              controllerRoleInSW = (ofc0 :> [x \in SW |-> ROLE_MASTER]) @@ (ofc1 :> [x \in SW |-> ROLE_SLAVE]),
              \* queue of notifications received from NIB
              nibEventQueue = [x \in {ofc0, ofc1} |-> <<>>],
              \* keeps track of role update messages' cycle
              roleUpdateStatus = [x \in {ofc0, ofc1} |-> [y \in SW |-> [roletpye |-> ROLE_EMPTY, status |-> IR_NONE]]],
              \* each OFC module except NIB event handler starts working when isOfcEnabled is TRUE
              isOfcEnabled = [x \in {ofc0} |-> TRUE] @@ [x \in {ofc1} |-> FALSE],
              \* used for synchronization between NIB event handler scheduled role update msg and workers
              setScheduledRoleUpdates = [x \in {ofc0, ofc1} |-> {}],
              \* ofcModuleTerminationStatus used for graceful termination of OFC modules
              ofcModuleTerminationStatus = [x \in {ofc0, ofc1} |-> 
                                                [y \in ({CONT_MONITOR, CONT_EVENT} \cup CONTROLLER_THREAD_POOL) |-> TERMINATE_NONE]],
              \* ofcModuleInitStatus used for NIB event handler to wake up a process 
              ofcModuleInitStatus = (ofc0 :> [x \in {CONT_EVENT} |-> INIT_PROCESS]) @@ (ofc1 :> [x \in {CONT_EVENT} |-> INIT_RUN]),
              \* recoveredSwitches is a set containing all the switches with slave role used by Failover handler to reschedule ROLE_REQ
              setRecoveredSwWithSlaveRole = [x \in {ofc0, ofc1} |-> {}],
              \* fetchedIRsBeforePassingToWorker contains all the IRs that should be forwarded to the worker after OFC becomes the MASTER
              fetchedIRsBeforePassingToWorker = [x \in {ofc0, ofc1} |-> <<>>],
              \* eventSkipList contains the events that should be skipped because the previous master OFC has processed them. 
              eventSkipList = [x \in {ofc0, ofc1} |-> [y \in SW |-> <<>>]],
              (********************* NIB Vars *****************************)
              \* indicates which module is elected as the holder of the lock 
              masterState = (ofc0 :> ROLE_MASTER @@ ofc1 :> ROLE_SLAVE @@ rc0 :> ROLE_MASTER),
              \* used for reconciliation after module failure (controller partial failure)
              controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]],
              \* keeps track of IR cycle
              IRStatus = [x \in 1..MAX_NUM_IRs |-> IR_NONE],
              \* used by topology event handler to inform rest of system about topology change  
              NIBSwSuspensionStatus = [x \in SW |-> SW_RUN],
              \* IR Queue filled by the sequencer in OFC
              IRQueueNIB = <<>>,
              \* list of subscribers of NIB
              subscribeList = [IRQueueNIB |-> {ofc0}, SwSuspensionStatus |-> {ofc0}], 
              \* used for synchronization between sequencer and workers
              SetScheduledIRs = [y \in SW |-> {}],
              \* status of OFC failover in NIB
              ofcFailoverStateNIB = [y \in {ofc0, ofc1} |-> FAILOVER_NONE],
              \* event log per switch in NIB
              NIBEventLog = [x \in SW |-> <<>>]
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
        getNonSlaveController(swID) == {x \in DOMAIN switchControllerRoleStatus[swID]: switchControllerRoleStatus[swID][x] # ROLE_SLAVE}
        isControllerMaster(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_MASTER
        isControllerSlave(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_SLAVE
        hasModificationAccess(swID, cid) == ~isControllerSlave(swID, cid)
        \**************************** Installer *****************************
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
                               
        \*************************** switch failure process *****************
        returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                                                             /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1}
        \* getSetIRsForSwitch is for verification optimization reasons
        getSetIRsForSwitch(SID) == {x \in 1..MAX_NUM_IRs: IR2SW[x] = SID}
        shouldSendFailMsgToAll(msg) == \/ msg.type \in {NIC_ASIC_DOWN, OFA_DOWN}
                                       \/ /\ msg.type = KEEP_ALIVE
                                          /\ msg.status.installerStatus = INSTALLER_DOWN
                                          
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
        shouldSendRecoveryMsgToAll(msg) == \/ msg.type \in {OFA_DOWN}
                                           \/ /\ msg.type = KEEP_ALIVE
                                              /\ msg.status.installerStatus \in {INSTALLER_DOWN, INSTALLER_UP}
                                                      
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
                                                                  /\ NIBSwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRs[IR2SW[x]]}
                                                                  \*/\ idThreadWorkingOnIR[x] = IR_UNLOCK}
                                                                  
        (****************** OFC (openflow controller) ************************)
        shouldWorkerTerminate(CID, TID) == ofcModuleTerminationStatus[CID][TID] = TERMINATE_INIT 
        shouldEventHandlerTerminate(CID) == ofcModuleTerminationStatus[CID][CONT_EVENT] = TERMINATE_INIT
        shouldMonitoringServerTerminate(CID) == /\ ofcModuleTerminationStatus[CID][CONT_MONITOR] = TERMINATE_INIT
                                                /\ ~\E x \in 1..MAX_NUM_IRs: /\ IRStatus[x] = IR_SENT
                                                                             /\ ofcSwSuspensionStatus[CID][IR2SW[x]] = SW_RUN
        \*********** NIB Event Handler & Failover handler *********************
        allSwitchesEitherEqualRoleOrSuspended(CID) == \A x \in SW: \/ controllerRoleInSW[CID][x] = ROLE_EQUAL
                                                                   \/ ofcSwSuspensionStatus[CID][x] = SW_SUSPEND
        getSetSwitchInSlaveRole(CID) == {x \in SW: controllerRoleInSW[CID][x] = ROLE_SLAVE}
        getSetSwitchInEqualRole(CID) == {x \in SW: controllerRoleInSW[CID][x] = ROLE_EQUAL}
        getSetSwitchInNonMasterRole(CID) == getSetSwitchInSlaveRole(CID) \cup getSetSwitchInEqualRole(CID)
        allModulesTerminated(CID) == \A x \in DOMAIN ofcModuleTerminationStatus[CID]: 
                                                        ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE
        allWorkersTerminated(CID) == \A x \in CONTROLLER_THREAD_POOL: 
                                                        ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE
        MonitoringServerTerminated(CID) == ofcModuleTerminationStatus[CID][CONT_MONITOR] = TERMINATE_DONE                                                
        existRecoveredSwitchWithSlaveRole(CID) == setRecoveredSwWithSlaveRole[CID] # {}
        areEventsEquivalent(event1, event2) == /\ \A x \in DOMAIN event1: \/ x \in {"auxNum"}
                                                                          \/ /\ x \in DOMAIN event2
                                                                             /\ event1[x] = event2[x]
                                               /\ \A x \in DOMAIN event2: \/ x \in {"auxNum"}
                                                                          \/ /\ x \in DOMAIN event1
                                                                             /\ event1[x] = event2[x]                                                  
        \*************************** Workers *********************************
        isSwitchSuspended(CID, sw) == ofcSwSuspensionStatus[CID][sw] = SW_SUSPEND
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
        workerCanSendTheIR(CID, nextToSent) == /\ ~isSwitchSuspended(CID, nextToSent.to)
                                               /\ \/ /\ nextToSent.type = ROLE_REQ
                                                     /\ roleUpdateStatus[CID][nextToSent.to].status = IR_NONE
                                                  \/ /\ nextToSent.type = INSTALL_FLOW
                                                     /\ IRStatus[nextToSent.IR] = IR_NONE
        workerShouldFastRecovery(CID, nextToSent) == \/ /\ nextToSent.type = ROLE_REQ
                                                        /\ roleUpdateStatus[CID][nextToSent.to].status = IR_NONE
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
        isFinished(CID) == /\ \A x \in getSetIRsForSwitch(CID): IRStatus[x] = IR_DONE
                           /\ \/ SHOULD_FAILOVER = 0
                              \/ /\ \A x \in SW: switchControllerRoleStatus[x][ofc0] = ROLE_SLAVE
                                 /\ \A x \in SW: switchControllerRoleStatus[x][ofc1] = ROLE_MASTER 
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
        auxEventCounter := auxEventCounter + 1;
        switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
        statusMsg := [type |-> NIC_ASIC_DOWN, 
                      swID |-> self[2],
                      num |-> controlMsgCounter[self[2]],
                      auxNum |-> auxEventCounter];
        \* swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);              
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
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusResolveMsg := [type |-> OFA_DOWN, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 auxNum |-> auxEventCounter];
        else
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)],
                                 auxNum |-> auxEventCounter];
        end if;
        \* swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);            
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
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusMsg := [type |-> OFA_DOWN, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]],
                          auxNum |-> auxEventCounter];
            \* swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);
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
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)],
                                 auxNum |-> auxEventCounter]; 
            \*swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);    
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
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter}; 
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
            statusMsg := [type |-> OFA_DOWN, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]],
                          auxNum |-> auxEventCounter];
            \* swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);    
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
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)],
                                 auxNum |-> auxEventCounter];
            
            \*swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);             
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
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;    
            statusMsg := [type |-> KEEP_ALIVE, 
                          swID |-> self[2],
                          num |-> controlMsgCounter[self[2]],
                          status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)],
                          auxNum |-> auxEventCounter];
            \*swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusMsg);
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
            auxEventCounter := auxEventCounter + 1;
            switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;    
            statusResolveMsg := [type |-> KEEP_ALIVE, 
                                 swID |-> self[2],
                                 num |-> controlMsgCounter[self[2]],
                                 status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)],
                                 auxNum |-> auxEventCounter];       
            \*swSeqChangedStatus[getMasterController(self[2])] := Append(swSeqChangedStatus[getMasterController(self[2])], statusResolveMsg);    
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
    \* we have 3 types of Lock; switchLock, controllerLocalLock, and 
    \* controllerGlobalLock
    
    \* ===========Wait for Lock==========
    macro switchWaitForLock()
    begin
        \* switch can only proceed if
        \* 1. control plane does not own the Lock
        \* 2. either no other switch has the Lock or the switch itself 
        \*    has the lock        
        await controllerGlobalLock = <<NO_LOCK, NO_LOCK>>;
        await \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
              \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                 /\ switchLock[2] = self[2];
    end macro;
    \* =================================
    
    \* ==== Switch Acquire Lock =======
    macro switchAcquireLock()
    begin
        \* switch acquires the lock if switchWaitForLock conditions are 
        \* satisfied
        switchWaitForLock();
        switchLock := self;
    end macro;
    \* =================================
    
    \* ====== Acquire & Change Lock =====
    macro switchAcquireAndChangeLock(nextLockHolder)
    begin
        \* Using this macro, processes can pass lock to another process        
        switchWaitForLock();
        switchLock := nextLockHolder;
    end macro;
    \* =================================
    
    \* ========= Release Lock ==========
    macro switchReleaseLock()
    begin
        assert \/ switchLock[2] = self[2]
               \/ switchLock[2] = NO_LOCK;
        switchLock := <<NO_LOCK, NO_LOCK>>;
    end macro;
    \* =================================
    
    \* ===== Is Global Lock free =======
    macro controllerWaitForGlobalLockFree()
    begin
        await \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
              \/ controllerGlobalLock[1] = self[1];
        await switchLock = <<NO_LOCK, NO_LOCK>>;    
    end macro
    \* =================================
        
    \* ===== Is Local Lock free ========
    macro controllerWaitForLocalLockFree()
    begin
        \* controller only proceeds when the following three conditions 
        \* are satified;
        controllerWaitForGlobalLockFree();
        await \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
              \/ controllerLocalLock[self[1]] = self;
    end macro
    \* =================================
    
    \* =Is Lock free (only for workers)=
    macro controllerWorkerWaitForLockFree()
    begin
        await switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
    end macro
    \* ================================
    
    \* = Controller Acquire Glob Lock ==
    macro controllerAcquireGlobalLock()
    begin
        controllerWaitForGlobalLockFree();
        controllerGlobalLock := self;
    end macro
    \* =================================
    
    \* = Controller Acquire Local Lock =
    macro controllerAcquireLocalLock()
    begin
        controllerWaitForLocalLockFree();
        controllerLocalLock[self[1]] := self;
    end macro
    \* =================================
    
    \* = controller release Local Lock =
    macro controllerReleaseLocalLock()
    begin
        \* only the controller process itself can release the controller lock. 
        controllerWaitForLocalLockFree();
        controllerLocalLock[self[1]] := <<NO_LOCK, NO_LOCK>>;
    end macro
    \* =================================
    
    macro controllerReleaseGlobalLock()
    begin
        controllerWaitForGlobalLockFree();
        controllerGlobalLock := <<NO_LOCK, NO_LOCK>>;
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
    
    \* === Schedule RoleUpdate Msgs ===
    macro scheduleRoleEqual(swID)  
    begin
        roleUpdateStatus[self[1]][swID] := [roletype |-> ROLE_EQUAL, status |-> IR_NONE]; 
        modifiedEnqueue(workerLocalQueue[self[1]], 
                                           [type |-> ROLE_REQ, roletype |-> ROLE_EQUAL, to |-> currSW]);
        setScheduledRoleUpdates[self[1]] := setScheduledRoleUpdates[self[1]] \cup {swID};
    end macro
    
    macro scheduleRoleMaster(swID)
    begin
        roleUpdateStatus[self[1]][swID] := [roletype |-> ROLE_MASTER, status |-> IR_NONE]; 
        modifiedEnqueue(workerLocalQueue[self[1]], [type |-> ROLE_REQ, roletype |-> ROLE_MASTER, to |-> swID]);
        setScheduledRoleUpdates[self[1]] := setScheduledRoleUpdates[self[1]] \cup {swID}; 
    end macro
    \* ==============================
    
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
        switchReleaseLock();
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
        
        switchAcquireLock();
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        
        \* Step2: if it is an OpenFlow packet, append it to the OFA input buffer
        SwitchNicAsicInsertToOfaBuff:
            if swCanReceivePackets(self[2]) then
                switchAcquireAndChangeLock(<<OFA_IN, self[2]>>);
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
        switchAcquireLock();
        assert egressMsg.type \in {INSTALLED_SUCCESSFULLY, ROLE_REPLY, BAD_REQUEST};
        Ofa2NicAsicBuff[self[2]] := Tail(Ofa2NicAsicBuff[self[2]]);
        
        \* Step 2: send the packet to the destination (controller)
        SwitchNicAsicSendOutMsg:
            if swCanReceivePackets(self[2]) then
                switchWaitForLock();
                switchReleaseLock();
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
        \* OpenFlow switches are not guaranteed to process the IRs in the same order as received
        \* (unless there is a barrier), we we check every permutation of concurrent IRs by letting 
        \* the controller send the IRs in any possible order (see label "ControllerThreadForwardIR").
        \* TODO(@Pooria): make sure above is true. 
        \* Step 1: Pick the first packet from buffer, process and extract the IR
        await swOFACanProcessIRs(self[2]);
        await Len(NicAsic2OfaBuff[self[2]]) > 0;
        switchAcquireLock();
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
                        switchAcquireAndChangeLock(<<INSTALLER, self[2]>>);
                    
                        Ofa2InstallerBuff[self[2]] := Append(Ofa2InstallerBuff[self[2]], 
                                                                  [IR |-> ofaInMsg.IR, 
                                                                  from |-> ofaInMsg.from]);
                    else 
                        \* 2.2. when IR from slave
                        switchAcquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
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
                    switchAcquireLock();
                    updateRole(ofaInMsg.from, ofaInMsg.roletype);
                        
                    SwitchSendRoleReply:
                        if swOFACanProcessIRs(self[2]) then 
                            switchAcquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                            sendRoleReply(ofaInMsg.from, ofaInMsg.roletype);
                        else
                            ofaInMsg := [type |-> 0];
                            goto SwitchOfaProcIn;
                        end if; 
                       
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
        switchAcquireLock();
        ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
        Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
        assert ofaOutConfirmation.IR \in 1..MAX_NUM_IRs;
        
        \* Step 2: prepare an installation confirmation message and send it to the controller
        \* through the NIC/ASIC
        SendInstallationConfirmation:
            if swOFACanProcessIRs(self[2]) then
                switchAcquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
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
       switchAcquireLock();
       installerInIR := Head(Ofa2InstallerBuff[self[2]]);
       assert installerInIR.IR \in 1..MAX_NUM_IRs;
       Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);
       
       \* Step 2: install the IR to the TCAM
       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then
                switchAcquireLock();
                installToTCAM(installerInIR.from, installerInIR.IR);   
            else
                installerInIR := [type |-> 0];
                goto SwitchInstallerProc;
            end if;
            
       \* Step 3: send the confirmation to the OFA
       SwitchInstallerSendConfirmation:
            if swCanInstallIRs(self[2]) then
                switchAcquireAndChangeLock(<<OFA_OUT, self[2]>>);
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
    variable statusMsg = [type |-> 0], notFailedSet = {}, failedElem = "", controllerSet = {},
    nxtController = "", prevLockHolder = <<NO_LOCK, NO_LOCK>>;
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
        assert statusMsg.type = 0;
        await notFailedSet # {};
        await ~isFinished(self[2]);
        await swFailedNum[self[2]] < MAX_NUM_SW_FAILURE;
        await /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
              /\ switchLock[2] = self[2];
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
        
        \* if OFA or NIC/ASIC or CPU has failed, we should disseminate the StatusMsg
        \* to all the controllers (since all of them have an OF TCP channel with the
        \* switch, failure of OFA/NIC/ASIC/CPU would cause termination of the channel
        \* and all of the controllers would be notified of this)
        \* @TODO(Pooria): For now we do not consider failure of Installer.      
        
        if shouldSendFailMsgToAll(statusMsg) then
            prevLockHolder := switchLock;
            switchAcquireLock();
            controllerSet := {ofc0, ofc1};
            swFailureSendStatusMsg:
                while controllerSet # {} do
                    nxtController := CHOOSE x \in controllerSet: TRUE;
                    controllerSet := controllerSet \ {nxtController};
                    swSeqChangedStatus[nxtController] := Append(swSeqChangedStatus[nxtController], statusMsg);
                end while;
                statusMsg := [type |-> 0];
                switchAcquireAndChangeLock(prevLockHolder);
        \*elsif statusMsg.type = KEEP_ALIVE /\ statusMsg.status.installerStatus = Failed then
        \* if installer is failed, we should notify all the switches with Master/Equal.
        \* Installer 
        \*    controllerSet := getNoneSlaveController(self[2]);
        \*    swInstallerStatusChange:
        \*        while controllerSet # {} do
        \*            nxtController := CHOOSE x \in controllerSet: TRUE;
        \*            controllerSet := controllerSet \ {nxtController};
        \*            swSeqChangedStatus[nxtController] := Append(swSeqChangedStatus[nxtController], statusMsg);
        \*        end while;
        \*        statusMsg := [type |-> 0];
        elsif statusMsg.type # 0 then
            assert FALSE;
        end if;
        
         
        \* switchReleaseLock(self);
    end while
    end process
    \* =================================
    
    \* ==== Failure Resolve Process ====
    fair process swResolveFailure \in ({SW_RESOLVE_PROC} \X SW)
    variable failedSet = {}, statusResolveMsg = [type |-> 0], recoveredElem = "", controllerSet = {}, 
    nxtController = "", prevLockHolder = <<NO_LOCK, NO_LOCK>>;
    begin
    SwitchResolveFailure:
    while TRUE do
        \* retrieves all the failed elements and create a branch in each of which
        \* a seperate element recovers
        assert statusResolveMsg.type = 0;
        failedSet := returnSwitchFailedElements(self[2]);
        await Cardinality(failedSet) > 0;
        await ~isFinished(self[2]);
        await /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
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
        
        \* if OFA or NIC/ASIC or CPU recovers, we should disseminate the StatusMsg
        \* to all the controllers (recovery of OFA/NIC/ASIC/CPU would cause initialization
        \* of OpenFlow channel with all the controllers)
        \* @TODO(Pooria): For now, we do not consider failure and recovery of the installer. 
        if shouldSendRecoveryMsgToAll(statusResolveMsg) then
            prevLockHolder := switchLock;
            switchAcquireLock();
            controllerSet := {ofc0, ofc1};
            swRecoverySendStatusMsg:
                while controllerSet # {} do
                    nxtController := CHOOSE x \in controllerSet: TRUE; 
                    controllerSet := controllerSet \ {nxtController};
                    swSeqChangedStatus[nxtController] := Append(swSeqChangedStatus[nxtController], statusResolveMsg);
                end while;
                statusResolveMsg := [type |-> 0];
                switchAcquireAndChangeLock(prevLockHolder);
        \*elsif statusMsg.type = KEEP_ALIVE /\ statusMsg.status.installerStatus = Failed then
        \* if installer is failed, we should notify all the switches with Master/Equal.
        \* Installer 
        \*    controllerSet := getNoneSlaveController(self[2]);
        \*    swInstallerStatusChange:
        \*        while controllerSet # {} do
        \*            nxtController := CHOOSE x \in controllerSet: TRUE;
        \*            controllerSet := controllerSet \ {nxtController};
        \*            swSeqChangedStatus[nxtController] := Append(swSeqChangedStatus[nxtController], statusMsg);
        \*        end while;
        \*        statusMsg := [type |-> 0];
        elsif statusResolveMsg.type # 0 then
            assert FALSE;
        end if;
        \*switchReleaseLock(self);
    end while
    end process
    \* =================================
    
    \* ====== Async Network Events =====
    \* this process asynchronously generate networking events such as port down, link down, etc.
    \* these events are only forwarded to non-slave controllers
    fair process asyncNetworkEventGenerator \in ({ASYNC_NET_EVE_GEN} \X SW)
    variable eventMsg = [type |-> 0], controllerSet = {}, nxtController = "", eventID = 0;
    begin
    asyncNetEventGenProc:
    while TRUE do
        await swNumEvent[self[2]] < SW_MAX_NUM_EVENTS[self[2]];
        switchWaitForLock();
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
        eventID := controlMsgCounter[self[2]];
        swNumEvent[self[2]] := swNumEvent[self[2]] + 1;
        auxEventCounter := auxEventCounter + 1;
        switchGeneratedEventSet[self[2]] := switchGeneratedEventSet[self[2]] \cup {auxEventCounter};       
        if swOFACanProcessIRs(self[2]) then
            controllerSet := getNonSlaveController(self[2]);
            sendNetworkEvent:
                while swOFACanProcessIRs(self[2]) do \* originally while swOFACanProcessIRs(self[2]) /\ controllerSet # {} do
                    switchAcquireLock();
                    nxtController := CHOOSE x \in controllerSet: TRUE;
                    controllerSet := controllerSet \ {nxtController};
                    eventMsg := [type |-> ASYNC_EVENT,
                                 from |-> self[2],
                                 to |-> nxtController,
                                 num |-> eventID,
                                 auxNum |-> auxEventCounter];
                    Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], eventMsg);  
                    
                    if controllerSet # {} then \* end while condition
                        goto asyncNetEventGenProc;
                    end if;          
                end while;
        end if;
    end while
    end process
    
    \* ======== Ghost UNLOCK ===========
    \* this process makes sure deadlock does not happend
    \* and switch releases the lock even if it has been failed
    fair process ghostUnlockProcess \in ({GHOST_UNLOCK_PROC} \X SW)
    begin
    ghostProc:
    while TRUE do
        \* @TODO(Pooria): More Optimization possible on especially for SW_FAILURE_PROC and
        \* SW_RESOLVE_FAILURE
        await /\ switchLock # <<NO_LOCK, NO_LOCK>>
              /\ switchLock[2] = self[2]
              /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>;
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
            elsif switchLock[1] \in {SW_FAILURE_PROC} then
                await pc[<<SW_FAILURE_PROC, self[2]>>] = "SwitchFailure";
            elsif switchLock[1] \in {SW_RESOLVE_PROC} then
                await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"; 
            end if;
        end if;
        switchReleaseLock();
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
        toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1]);
        await toBeScheduledIRs # {};
        
        controllerWaitForLocalLockFree();
        \* SchedulerMechanism consists of three operations; 
        \* 1) choosing one IR from the set of valid IRs
        \* 2) updating the state of DB to start scheduling
        \* 3) add the IR to the scheduled Set (acts as a buffer 
        \*      for sequencer to make sure it does not unnecessarily
        \*      reschedules any IR) 
        \* (sequencer may fail between these Ops)
        SchedulerMechanism:
        while TRUE do \* while toBeScheduledIRs # {} do
            controllerWaitForLocalLockFree();
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
            \* 1) Enqueueing the IR to the IRQueue in NIB
            \* 2) Clearing the state on DB 
            \* Sequencer may fail between these two Ops. 
            ScheduleTheIR: 
                controllerAcquireGlobalLock();
                whichStepToFail(2);
                if (stepOfFailure # 1) then
                    \* step 1: enqueue the IR 
                    enqueue(IRQueueNIB, [type |-> INSTALL_FLOW, to |-> IR2SW[nextIR], IR |-> nextIR]);
                    \* Instead of NIB generating notification for change in IRQueueNIB
                    \* for simplicity, Sequencer generates the notification
                    subscriberOfcSet := subscribeList.IRQueueNIB; 
                    sendIRQueueModNotification:
                        while subscriberOfcSet # {} do
                            ofcID := CHOOSE x \in subscriberOfcSet: TRUE;
                            subscriberOfcSet := subscriberOfcSet \ {ofcID};                            
                            enqueue(nibEventQueue[ofcID], [type |-> INSTALL_FLOW, 
                                                           to |-> IR2SW[nextIR], 
                                                           IR |-> nextIR]);
                        end while;
                    \*controllerReleaseGlobalLock();
                    toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                    if (stepOfFailure # 2) then
                        \* step 2: clear the state on NIB  
                        controllerStateNIB[self] := [type |-> NO_STATUS];    
                    end if;
                end if;
                
                sequencerApplyFailure:
                    controllerReleaseGlobalLock();
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
        controllerReleaseGlobalLock();
        controllerReleaseLocalLock();
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
    variables event=[type |-> 0];
    begin
    NibEventHandlerProc:
        while TRUE do
            await nibEventQueue[self[1]] # <<>>;
            \* NIB event handler should pass the IRs to the worker's local queue. 
            read(nibEventQueue[self[1]], event);
            assert event.type \in {INSTALL_FLOW, TOPO_MOD};
            if event.type = TOPO_MOD /\ masterState[self[1]] = ROLE_SLAVE then
               if ofcSwSuspensionStatus[self[1]][event.sw] = SW_RUN /\ event.status = SW_SUSPEND then
                    ofcSwSuspensionStatus[self[1]][event.sw] := SW_SUSPEND;
               elsif ofcSwSuspensionStatus[self[1]][event.sw] = SW_SUSPEND /\ event.status = SW_RUN then
                    ofcSwSuspensionStatus[self[1]][event.sw] := SW_RUN;
                    if controllerRoleInSW[self[1]][event.sw] = ROLE_SLAVE /\ ofcFailoverStateNIB[self[1]] = FAILOVER_INIT then
                        setRecoveredSwWithSlaveRole[self[1]] := setRecoveredSwWithSlaveRole[self[1]] \cup {event.sw};
                    end if;
               end if;
            elsif event.type = INSTALL_FLOW then
                if masterState[self[1]] = ROLE_MASTER then 
                    modifiedEnqueue(workerLocalQueue[self[1]], event);
                else
                    fetchedIRsBeforePassingToWorker[self[1]] := Append(fetchedIRsBeforePassingToWorker[self[1]], event)
                end if;
            end if;
            remove(nibEventQueue[self[1]]);
             
        end while;
    end process
    \* ==========================
    
    \* ==== Failover Handler ====
    fair process ofcFailoverHandler \in ({ofc0, ofc1} \X {FAILOVER_HANDLER})
    variables swSet = {}, currSW = 0, entry = [type |-> 0], index = 0, event = [type |-> 0],
                pulledNIBEventLog = <<>>, remainingEvents = <<>>, receivedEventsCopy = [type |-> <<>>];
    begin
    ofcFailoverHandlerProc:
        while TRUE do
            await \/ ofcFailoverStateNIB[self[1]] \in {FAILOVER_INIT, FAILOVER_TERMINATE}
                  \/ /\ masterState[self[1]] = ROLE_MASTER
                     /\ getSetSwitchInNonMasterRole(self[1]) # {};
            controllerWaitForLocalLockFree();
            controllerReleaseGlobalLock();
            \* if Failover handler receives notification about its failover status FAILOVER_INIT
            \* it should perform necessary actions to be ready to takeover the OFC reponsibilities;
            \* 1) subscribe to and pull the NIB SwSuspensionStatus
            \* 2) update its role to ROLE_EQUAL in all the switches
            \* 3) subscribe to NIB IR Queue
            \* 4) pull the IRs from NIB IRQueue
            \* 5) change its failover status to FAILOVER_READY
            \* 6) wait for OFC to have role master in NIB
            \* 7) reconcile its local worker queue with NIB IR queue
            \* 8) initialize OFC controller event handler
            if ofcFailoverStateNIB[self[1]] = FAILOVER_INIT then 
                        
                \* controllerAcquireLock(self);
                isOfcEnabled[self[1]] := TRUE; \* This is for optimization
                swSet := getSetSwitchInSlaveRole(self[1]);
                \* Step 1. subscribe to and pull NIB switch suspension status
                subscribeList.SwSuspensionStatus := subscribeList.SwSuspensionStatus \cup {self[1]};
                ofcSwSuspensionStatus[self[1]] := NIBSwSuspensionStatus;
                
                ScheduleRoleUpdateEqual:
                \* Step 2. update role to ROLE_EQUAL in all the switches        
                while swSet # {} do
                        \*controllerWaitForLocalLockFree();
                        controllerAcquireLocalLock();
                        controllerAcquireGlobalLock();
                        
                        currSW := CHOOSE x \in swSet: TRUE;
                        scheduleRoleEqual(currSW);
                        swSet := swSet \ {currSW};
                    end while;
               controllerReleaseLocalLock();
               controllerReleaseGlobalLock();
                        
               
               WaitForSwitchUpdateRoleACK: 
                    \* Step 3: (1) wait for receiving confirmation from all switches regarding 
                    \* role update. (2) subscribe to IR Queue in NIB
                    controllerWaitForLocalLockFree();
                    controllerReleaseGlobalLock();
                    
                    await \/ allSwitchesEitherEqualRoleOrSuspended(self[1])
                          \/ existRecoveredSwitchWithSlaveRole(self[1]);
                    if existRecoveredSwitchWithSlaveRole(self[1]) then
                        currSW := CHOOSE x \in setRecoveredSwWithSlaveRole[self[1]]: TRUE;
                        if controllerRoleInSW[self[1]][currSW] = ROLE_SLAVE then
                            scheduleRoleEqual(currSW);
                        end if;
                        setRecoveredSwWithSlaveRole[self[1]] := setRecoveredSwWithSlaveRole[self[1]] \ {currSW};
                        goto WaitForSwitchUpdateRoleACK;
                    else
                        subscribeList.IRQueueNIB := subscribeList.IRQueueNIB \cup {self[1]};
                        \* Step 4: pull the IRs from NIB IR Queue
                        fetchedIRsBeforePassingToWorker[self[1]] := fetchedIRsBeforePassingToWorker[self[1]] \o IRQueueNIB;
                        \* Step 5: change failover status to FAILOVER_READY
                        ofcFailoverStateNIB[self[1]] := FAILOVER_READY;
                    end if;
                    
               QueryIRQueueNIB:
                    while fetchedIRsBeforePassingToWorker[self[1]] # <<>> do
                        \* Step 6: wait for the OFC to have role master in NIB
                        controllerWaitForLocalLockFree();
                        controllerReleaseGlobalLock();
                        await masterState[self[1]] = ROLE_MASTER;
                        \* Step 7: add IRs to worker queue
                        entry := Head(fetchedIRsBeforePassingToWorker[self[1]]);
                        fetchedIRsBeforePassingToWorker[self[1]] := Tail(fetchedIRsBeforePassingToWorker[self[1]]);
                        modifiedEnqueue(workerLocalQueue[self[1]], entry);
                    end while;
                    \* Step 8: initalize OFC controller event handler
                    controllerWaitForLocalLockFree();
                    controllerReleaseGlobalLock();
                    await masterState[self[1]] = ROLE_MASTER;
                    await pc[<<self[1], CONT_EVENT>>] = "ControllerEventHandlerProc";     
                    ofcModuleInitStatus[self[1]][CONT_EVENT] := INIT_NONE; 
                    
               EventHandlerInitStateForReconciliation:
                    pulledNIBEventLog := NIBEventLog;
                    receivedEventsCopy := localEventLog[self[1]];
                    swSet := SW;
                    
               ReconcileEventLogs:
                    while swSet # {} do
                        currSW := CHOOSE x \in swSet: TRUE;
                        ReconcileEventForSW:
                            while pulledNIBEventLog[currSW] # <<>> /\ receivedEventsCopy[currSW] # <<>> do
                                controllerWaitForLocalLockFree();
                                controllerReleaseGlobalLock();
                                event := Head(pulledNIBEventLog[currSW]);
                                assert event.swID = currSW;
                                if areEventsEquivalent(Head(receivedEventsCopy[currSW]), event) then
                                    receivedEventsCopy[currSW] := Tail(receivedEventsCopy[currSW]);
                                else
                                    remainingEvents := Append(remainingEvents, event)
                                end if;
                                pulledNIBEventLog[currSW] := Tail(pulledNIBEventLog[currSW]);
                            end while;
                            if receivedEventsCopy[currSW] # <<>> then
                                remainingEvents := remainingEvents \o receivedEventsCopy[currSW];
                            else
                                eventSkipList[self[1]][currSW] := eventSkipList[self[1]][currSW] \o pulledNIBEventLog[currSW];
                            end if;
                            swSet := swSet \ {currSW};
                    end while;
                    controllerWaitForLocalLockFree();
                    controllerReleaseGlobalLock();
                    swSeqChangedStatus[self[1]] := remainingEvents \o swSeqChangedStatus[self[1]];
                    ofcModuleInitStatus[self[1]][CONT_EVENT] := INIT_PROCESS; 
               
            \* if failover handler receives notification about failover status FAILOVER_TERMINATE
            \* it should gracefully terminate and respond with FAILOVER_TERMINATE_DONE;
            \* 1) send termination signal to workers and wait for them to terminate
            \* 2) send termination signal to topology event handler and monitoring server and wait
            \* for them to terminate
            \* 3) change its failover status to FAILOVER_TERMINATE_DONE       
            elsif ofcFailoverStateNIB[self[1]] = FAILOVER_TERMINATE then
                
              subscribeList.IRQueueNIB := subscribeList.IRQueueNIB \ {self[1]} || 
                                subscribeList.SwSuspensionStatus := subscribeList.SwSuspensionStatus \ {self[1]};
              ofcModuleTerminationStatus[self[1]] := [y \in CONTROLLER_THREAD_POOL |-> TERMINATE_INIT] 
                                                                        @@ ofcModuleTerminationStatus[self[1]];
              
              WaitForWorkersTermination:
                    controllerWaitForLocalLockFree();
                    controllerReleaseGlobalLock();
                    await allWorkersTerminated(self[1]);
                    ofcModuleTerminationStatus[self[1]] := [y \in {CONT_MONITOR} |-> TERMINATE_INIT] 
                                                                                @@ ofcModuleTerminationStatus[self[1]];
              WaitForMonitoringServerTermination:
                    controllerWaitForLocalLockFree();
                    controllerReleaseGlobalLock();
                    await MonitoringServerTerminated(self[1]);
                    ofcModuleTerminationStatus[self[1]] := [y \in {CONT_EVENT} |-> TERMINATE_INIT] 
                                                                                @@ ofcModuleTerminationStatus[self[1]];
              WaitForOFEventHandlerTermination:
                    controllerWaitForLocalLockFree();
                    controllerReleaseGlobalLock();
                    await allModulesTerminated(self[1]);
                    ofcFailoverStateNIB[self[1]] := FAILOVER_TERMINATE_DONE;
                    goto Done;
                    
            \* Failover handler should asynchronously update OFC's role to ROLE_MASTER in all the switches
            else
                
                currSW := CHOOSE x \in getSetSwitchInNonMasterRole(self[1]): TRUE;
                scheduleRoleMaster(currSW);
            
            end if;
        end while
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
        await isOfcEnabled[self[1]];
        await moduleIsUp(self);
        await workerLocalQueue # <<>>; 
        await canWorkerThreadContinue(self[1], self);
        controllerWaitForLocalLockFree();
        \* ControllerThread consists of 4 Ops: 
        \* 1. modified read from IRQueue in the NIB (which gives the 
        \*    next IR to install)
        \* 2. update the state of db to locking mode
        \* 3. try to lock the IR to avoid two workers working on the same IR
        \*      (Note that sequence may fail in the middle of scheduling and
        \*       may reschedule the IR wrongly)
        \* (worker may fail between these Ops)
        \* 4. check necessary conditions on switch status and IR status,
        \*      then, change IR_STATUS to IR_SENT (Update-before-Action)
        
        \* Step 1. modified read
        modifiedRead(workerLocalQueue[self[1]], nextToSent, entryIndex);
        controllerReleaseGlobalLock();
        whichStepToFail(3);
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
                    
                    if (stepOfFailure = 3) then
                        \* Failed after Step 3
                        controllerModuleFails();
                        goto ControllerThreadStateReconciliation;
                    else
                        \* Step 4: check if the switch is not suspended and instruction is in its initial mode
                        if (workerCanSendTheIR(self[1], nextToSent)) then
                            \********* Step 4.1: change the status of IR to IR_SENT before actually sending (Update-before-Action)
                            assert nextToSent.type \in {INSTALL_FLOW, ROLE_REQ};
                        
                            if nextToSent.type = INSTALL_FLOW then
                                IRStatus[nextToSent.IR] := IR_SENT;
                            elsif nextToSent.type = ROLE_REQ then
                                roleUpdateStatus[self[1]][nextToSent.to].status := IR_SENT;
                            end if;
                        
                            \* ControllerThreadForwardIR consists of 2 operations;
                            \* 1. Forwarding the IR to the switch
                            \* 2. Updating the state on db to SENT_DONE
                            \* Worker may fail between these operations
                            ControllerThreadForwardIR:
                                controllerWorkerWaitForLockFree();
                                controllerReleaseGlobalLock();
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
                    end if;                    
                else
                    ControllerThreadRemoveQueue1: 
                        controllerWaitForLocalLockFree();
                        controllerReleaseGlobalLock();
                        modifiedRemove(workerLocalQueue[self[1]], nextToSent);
                        \*if nextToSent.type = INSTALL_FLOW then
                        \*    removeItem(IRQueueNIB, nextToSent);
                        \*end if;
                        goto ControllerThread;    
                end if;
            end if;
        end if;
        
        \* Operations in the next two labels are for performance reasons
        \* since we have already dedicated this worker to a IR, if the switch
        \* is in suspended mode, worker waits for it to be recovered and then, 
        \* does the fast recovery by immediately starting to send the IR
        \* TODO (@Pooria): below should be added again 
        \*WaitForIRToHaveCorrectStatus:  
        \*    controllerWaitForLocalLockFree();
        \*    controllerReleaseGlobalLock();
        \*    controllerModuleFailOrNot();
        \*    if (controllerSubmoduleFailStat[self] = NotFailed) then 
        \*        await ~isSwitchSuspended(self[1], nextToSent.to);
        \*    else
        \*        goto ControllerThreadStateReconciliation;
        \*    end if;
            
        \*ReScheduleifIRNone:
        \*    controllerWaitForLocalLockFree();
        \*    controllerReleaseGlobalLock();
        \*    controllerModuleFailOrNot();
        \*    if (controllerSubmoduleFailStat[self] = NotFailed) then
        \*        if workerShouldFastRecovery(self[1], nextToSent) then
        \*            controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextToSent, index |-> entryIndex]; 
        \*            goto ControllerThreadSendIR;
        \*        end if;
        \*    else
        \*        goto ControllerThreadStateReconciliation;
        \*    end if;
        
        \* ControllerThreadReleaseSemaphoreAndScheduledSet consists of 4 Ops;
        \* 1. unlock the IR which was locked at the begining
        \* 2. Remove the IR from the scheduled set since worker is done with it.
        \* 3. Clear the state on db
        \* 4. Remove the IR from the tagged buffer (lazy removal strategy)
        ControllerThreadReleaseSemaphoreAndScheduledSet:
            controllerWaitForLocalLockFree();
            controllerReleaseGlobalLock();
            whichStepToFail(4);
            if (stepOfFailure # 1) then
                \* Step 1. unlock the IR which was locked before 
                if idThreadWorkingOnIR[self[1]][entryIndex] = self[2] then
                    idThreadWorkingOnIR[self[1]][entryIndex] := IR_UNLOCK;
                end if;
                if (stepOfFailure # 2) then
                    \* Step 2: Remove from scheduled set
                    \* assert nextToSent \in SetScheduledIRs[IR2SW[nextIRToSent]];
                    if nextToSent.type = INSTALL_FLOW then
                        SetScheduledIRs[nextToSent.to] := SetScheduledIRs[nextToSent.to]\{nextToSent.IR};
                    end if;
                    
                    if (stepOfFailure # 3) then 
                        \* Step 3: clear the state on NIB
                        controllerStateNIB[self] := [type |-> NO_STATUS];
                        if (stepOfFailure # 4) then
                            \* Step 4: remove from IRQueue
                            modifiedRemove(workerLocalQueue[self[1]], nextToSent);
                            if nextToSent.type = INSTALL_FLOW then
                                removeItem(IRQueueNIB, nextToSent);
                            end if;
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
        controllerReleaseGlobalLock();
        controllerReleaseLocalLock();
        if (controllerStateNIB[self].type = STATUS_LOCKING) then
            if (controllerStateNIB[self].next.type = INSTALL_FLOW) then
                if (IRStatus[controllerStateNIB[self].next.IR] = IR_SENT) then
                        IRStatus[controllerStateNIB[self].next.IR] := IR_NONE;
                end if;
            elsif (controllerStateNIB[self].next.type = ROLE_REQ) then
                if (roleUpdateStatus[self[1]][controllerStateNIB[self].next.to].status = IR_SENT) then
                    roleUpdateStatus[self[1]][controllerStateNIB[self].next.to].status := IR_NONE;
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
    
    \* === OF Event Handler =====
    fair process controllerEventHandler \in ({ofc0, ofc1} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, resetIR = 0, stepOfFailure = 0,
                notifOFC = 0, isEventProcessed = 0;
    begin
    ControllerEventHandlerProc:
    while ~shouldEventHandlerTerminate(self[1]) do 
         await isOfcEnabled[self[1]];
         await moduleIsUp(self);   
         await swSeqChangedStatus[self[1]] # <<>>;
         assert ofcModuleInitStatus[self[1]][self[2]] \in {INIT_NONE, INIT_RUN, INIT_PROCESS};
         await ofcModuleInitStatus[self[1]][self[2]] \in {INIT_RUN, INIT_PROCESS};
         controllerWaitForLocalLockFree();
         controllerReleaseGlobalLock();
         \* Controller event handler process consists of two operations;
         \* 1. Picking the first event from the event queue
         \* 2. (Only if OF Init status is INIT_PROCESS)
         \*     Check whether the event is a switch failure or a switch recovery
         \*     2.1 if a switch failure and current state of switch is SW_RUN
         \*             , then suspend the switch both locally and in NIB
         \*     2.2. if a switch recovery and current state of switch is SW_SUSPEND
         \*             , then  
         monitoringEvent := Head(swSeqChangedStatus[self[1]]);
         if ofcModuleInitStatus[self[1]][self[2]] = INIT_PROCESS then
            if eventSkipList[self[1]][monitoringEvent.swID] # <<>> then
               
               if areEventsEquivalent(monitoringEvent, Head(eventSkipList[self[1]][monitoringEvent.swID])) then
                    swSeqChangedStatus[self[1]] := Tail(swSeqChangedStatus[self[1]]);
                    if shouldSuspendSw(monitoringEvent) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] = SW_RUN then
                        ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] := SW_SUSPEND; 
                    elsif canfreeSuspendedSw(monitoringEvent) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] = SW_SUSPEND then
                        ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] := SW_RUN; 
                    end if; 
               end if;
               eventSkipList[self[1]][monitoringEvent.swID] := Tail(eventSkipList[self[1]][monitoringEvent.swID]);
               goto ControllerEventHandlerProc;
                       
            else
                isEventProcessed := 1;
                if shouldSuspendSw(monitoringEvent) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] = SW_RUN then
         
                    \* ControllerSuspendSW only suspends the SW (so the rest of the system does not work on
                    \* the tasks related to this switch anymore).
                    \* Here, Due to performance reasons, we defere the task of resetting status of IRs to 
                    \* the time that the switch is recovered (Lazy evaluation) because; First, it might not
                    \* be necessary (for example, the switch may have installed the IR). Second, the switch
                    \* may have faced a permanent failure in which these IRs are not valid anymore. 
                    controllerModuleFailOrNot();
                    if (controllerSubmoduleFailStat[self] = NotFailed) then
                        if (masterState[self[1]] = ROLE_MASTER) then
                            NIBSwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;
                            notifOFC := CHOOSE x \in ({ofc0, ofc1} \ {self[1]}): TRUE;
                            nibEventQueue[notifOFC] := Append(nibEventQueue[notifOFC], [type |-> TOPO_MOD, 
                                                                                        sw |-> monitoringEvent.swID,
                                                                                        status |-> SW_SUSPEND]); 
                        end if;
                        ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] := SW_SUSPEND;        
                    else
                        goto ControllerEventHandlerStateReconciliation;
                    end if;
                
                elsif canfreeSuspendedSw(monitoringEvent) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] = SW_SUSPEND then
            
                    \* ControllerFreeSuspendedSW consists of three operations; 
                    \* 1. Save on db that it is going to reset the IRs
                    \* 2. Change the SW status to SW_RUN (so all the corresponding IRs going to be scheduled immediately)
                    \* (event handler may fail between any of these Ops.)
                    \* 3. Check if this is the last event for the corresponding sw (if it is not, then, maybe the switch
                    \*      has failed again and resetting the IRs is not necessary). Note that we have to process the 
                    \*      event and change the status of SW anyway. Otherwise, it may result in discarding the subsequent
                    \*      events (one of the failures!!!!) 
                    \* 4. Schedule Role Update if necessary  
                    \* 5. GetIRsToBeChecked 
                    \* 6. ResetAllIRs
                    whichStepToFail(3);
                    if (stepOfFailure = 1) then 
                        controllerModuleFails();
                        goto ControllerEventHandlerStateReconciliation;
                    else
                        \* Step 1: save state on NIB
                        controllerStateNIB[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
                        if (stepOfFailure = 2) then
                            controllerModuleFails();
                            goto ControllerEventHandlerStateReconciliation;
                        else
                            \* Step 2: change switch status to SW_RUN
                            if (masterState[self[1]] = ROLE_MASTER) then
                                NIBSwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                                notifOFC := CHOOSE x \in ({ofc0, ofc1} \ {self[1]}): TRUE;
                                nibEventQueue[notifOFC] := Append(nibEventQueue[notifOFC], [type |-> TOPO_MOD, 
                                                                                            sw |-> monitoringEvent.swID,
                                                                                            status |-> SW_RUN]);
                            end if;
                            ofcSwSuspensionStatus[self[1]][monitoringEvent.swID] := SW_RUN;  
                            if (stepOfFailure = 3) then
                                controllerModuleFails();
                                goto ControllerEventHandlerStateReconciliation;
                            else
                                \* Step 3: check if this is the last event
                                if ~existsMonitoringEventHigherNum(monitoringEvent, self[1]) then
                                    \* Step 4: Schedule Role Update Msg if switch is in Non Master Role
                                    if controllerRoleInSW[self[1]][monitoringEvent.swID] # ROLE_MASTER then
                                        scheduleRoleMaster(monitoringEvent.swID);   
                                    end if;
                                    \* Step 5: getIRsToBeChecked retrieves all the IRs need to reset
                                    getIRsToBeChecked:
                                        controllerWaitForLocalLockFree();
                                        controllerReleaseGlobalLock();
                                        controllerModuleFailOrNot();
                                        if (controllerSubmoduleFailStat[self] = NotFailed) then
                                            setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                                            if (setIRsToReset = {}) then \* Do not do the operations in ResetAllIRs label if setIRsToReset is Empty *\
                                                goto ControllerEvenHanlderRemoveEventFromQueue;
                                            end if;
                                        else
                                            goto ControllerEventHandlerStateReconciliation;
                                        end if;
                                    \* Step 6: ResetAllIRs reset all the IRs in IR_SENT mode to IR_NONE one by one
                                    ResetAllIRs:
                                        while TRUE do \* Initially: while setIRsToReset # {} do
                                            controllerWaitForLocalLockFree();
                                            controllerReleaseGlobalLock();
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
                            end if;
                        end if;
                    end if;
                end if;
            end if;
         end if;
         
         \* ControllerEventHandlerRemoveEventFromQueue consists of 2 operations;
         \* 1. Clear the state on db
         \* 2. Remove the event from queue (Lazy removal procedure)
         \* event handler may fail between these Ops. 
         \* 3. add event to NIB event log 
         \* 4. add event to local event log
         ControllerEvenHanlderRemoveEventFromQueue:
            controllerWaitForLocalLockFree();
            controllerReleaseGlobalLock();
            if isEventProcessed = 1 then 
                processedEvents[self[1]] := processedEvents[self[1]] \cup {monitoringEvent.auxNum};
            end if;
            whichStepToFail(2);
            if (stepOfFailure # 1) then 
                \* Step 1: clear state on NIB
                controllerStateNIB[self] := [type |-> NO_STATUS]; 
                if (stepOfFailure # 2) then
                    \* Step 2: remove from event queue
                    swSeqChangedStatus[self[1]] := Tail(swSeqChangedStatus[self[1]]);
                    \* Step 3: add to the NIB event log
                    if masterState[self[1]] = ROLE_MASTER /\ isEventProcessed = 1 then
                        NIBEventLog[monitoringEvent.swID] := Append(NIBEventLog[monitoringEvent.swID], monitoringEvent);
                    end if;
                    \* Step 4: add to the local event log
                    localEventLog[self[1]][monitoringEvent.swID] := Append(localEventLog[self[1]][monitoringEvent.swID], monitoringEvent);
                end if;
            end if;
            isEventProcessed := 0;
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
         await isOfcEnabled[self[1]];
         await moduleIsUp(self);   
         await swSeqChangedStatus[self[1]] # <<>>; 
         controllerReleaseLocalLock();
         controllerReleaseGlobalLock();
         if (controllerStateNIB[self].type = START_RESET_IR) then
            if (masterState[self[1]] = ROLE_MASTER) then
                NIBSwSuspensionStatus[self[1]][controllerStateNIB[self].sw] := SW_SUSPEND;
                notifOFC := CHOOSE x \in ({ofc0, ofc1} \ {self[1]}): TRUE;
                nibEventQueue[notifOFC] := Append(nibEventQueue[notifOFC], [type |-> TOPO_MOD, 
                                                                            sw |-> monitoringEvent.swID,
                                                                            status |-> SW_SUSPEND]);
            end if;
            ofcSwSuspensionStatus[self[1]][controllerStateNIB[self].sw] := SW_SUSPEND;
         end if;
        goto ControllerEventHandlerProc;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    \* monitroing server does not need a reconciliation phase. 
    fair process controllerMonitoringServer \in ({ofc0, ofc1} \X {CONT_MONITOR})
    variable msg = [type |-> 0], stepOfFailure = 0;
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
        controllerReleaseLocalLock();
        controllerReleaseGlobalLock();
        msg := Head(switch2Controller[self[1]]);
        assert \/ /\ msg.type = INSTALLED_SUCCESSFULLY
                  /\ msg.from = IR2SW[msg.IR]
               \/ msg.type \in {ROLE_REPLY, BAD_REQUEST};
        whichStepToFail(2);          
        if msg.type = INSTALLED_SUCCESSFULLY then
                \* If msg type is INSTALLED_SUCCESSFULLY, we have to change the IR status
                \* to IR_DONE. 
                if (stepOfFailure # 1) then 
                    FirstInstall[msg.IR] := 1;
                    IRStatus[msg.IR] := IR_DONE;
                end if;
            
       elsif msg.type = ROLE_REPLY then
                if (stepOfFailure # 1) then
                    if roleUpdateStatus[self[1]][msg.from].roletype = msg.roletype then
                        roleUpdateStatus[self[1]][msg.from].status := IR_DONE;
                    end if;
                    controllerRoleInSW[self[1]][msg.from] := msg.roletype; 
                end if;                   
       elsif msg.type = BAD_REQUEST then
                \* If msg type is BAD_REQUEST, it means this OFC is not the master for the switch
                \* for now we do nothing; Todo(@Pooria)
                skip; 
       else assert FALSE;
       end if;
        
        \*end if;
        
        \* MonitoringServerRemoveFromQueue lazily removes the msg from queue. 
        if (stepOfFailure # 2) then
            switch2Controller[self[1]] := Tail(switch2Controller[self[1]]);
        end if; 
        
        if (stepOfFailure # 0) then
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
        controllerWaitForLocalLockFree();
        controllerFailedModules := returnControllerFailedModules(self[1]);
        await Cardinality(controllerFailedModules) > 0;
        with module \in controllerFailedModules do
            assert controllerSubmoduleFailStat[module] = Failed;
            controllerLocalLock := module;
            controllerGlobalLock := module;
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
        controllerWaitForGlobalLockFree();
        await SHOULD_FAILOVER = 1;
        ofcFailoverStateNIB[ofc1] := FAILOVER_INIT;
    ofcFailoverCurrMasterTerminate:
        controllerWaitForGlobalLockFree();
        await ofcFailoverStateNIB[ofc1] = FAILOVER_READY;
        ofcFailoverStateNIB[ofc0] := FAILOVER_TERMINATE;
    ofcFailoverChangeRoles:
        controllerWaitForGlobalLockFree();
        await ofcFailoverStateNIB[ofc0] = FAILOVER_TERMINATE_DONE;
        masterState[ofc0] := ROLE_SLAVE || masterState[ofc1] := ROLE_MASTER;
    end process    
    \* ==========================
       
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3dffb77fd262836d8386585b42714038 (chksum(pcal) = "9dcf79e8" /\ chksum(tla) = "95dea1ec") (chksum(pcal) = "9dcf79e8" /\ chksum(tla) = "95dea1ec") (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) = "9dcf79e8" /\ chksum(tla) = "95dea1ec") (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) = "3222e15c" /\ chksum(tla) = "180275ab") (chksum(pcal) = "21cbd470" /\ chksum(tla) = "c0cc7a8") (chksum(pcal) = "724d8828" /\ chksum(tla) = "6c9521e2") (chksum(pcal) = "28e9b5d1" /\ chksum(tla) = "e884fb9") (chksum(pcal) = "4a244545" /\ chksum(tla) = "f382faa2") (chksum(pcal) = "518bb467" /\ chksum(tla) = "7010b799") (chksum(pcal) = "518bb467" /\ chksum(tla) = "7010b799") (chksum(pcal) = "8fa76253" /\ chksum(tla) = "ec470895") (chksum(pcal) = "e58d914c" /\ chksum(tla) = "1c98fe65") (chksum(pcal) = "2924d278" /\ chksum(tla) = "58b6f2d6") (chksum(pcal) = "4c6b11f5" /\ chksum(tla) = "b3b47460") (chksum(pcal) = "14ce1a3b" /\ chksum(tla) = "b8f1e908") (chksum(pcal) = "e58d914c" /\ chksum(tla) = "dac05797") (chksum(pcal) = "b549029b" /\ chksum(tla) = "a873514a") (chksum(pcal) = "dab5451d" /\ chksum(tla) = "56896288") (chksum(pcal) = "dab5451d" /\ chksum(tla) = "56896288") (chksum(pcal) = "39563822" /\ chksum(tla) = "23bfeb59") (chksum(pcal) = "9aa440de" /\ chksum(tla) = "dc7e4288") (chksum(pcal) = "a0a0bee1" /\ chksum(tla) = "ed38f0e9") (chksum(pcal) = "cf2eafd2" /\ chksum(tla) = "4c04f272") (chksum(pcal) = "7e7fc0c4" /\ chksum(tla) = "1614e8ec") (chksum(pcal) = "3a14bd2f" /\ chksum(tla) = "591ee32a") (chksum(pcal) = "9b4f8a5a" /\ chksum(tla) = "8875b10") (chksum(pcal) = "475adba0" /\ chksum(tla) = "902308a") (chksum(pcal) = "5dba030c" /\ chksum(tla) = "ea7ede7a") (chksum(pcal) = "7f553d06" /\ chksum(tla) = "83b72369") (chksum(pcal) = "6ba8d8c0" /\ chksum(tla) = "b2958aba") (chksum(pcal) = "49edbd71" /\ chksum(tla) = "979d14c9") (chksum(pcal) = "49edbd71" /\ chksum(tla) = "5ba10a8") (chksum(pcal) = "174dda55" /\ chksum(tla) = "97421c8b") (chksum(pcal) = "c34e3829" /\ chksum(tla) = "7dcd0cea") (chksum(pcal) = "eb8f2be6" /\ chksum(tla) = "a6135120") (chksum(pcal) = "9ecb364d" /\ chksum(tla) = "d6048af4") (chksum(pcal) = "e74eb016" /\ chksum(tla) = "f099fc3b") (chksum(pcal) = "458caf08" /\ chksum(tla) = "1aaf48bb") (chksum(pcal) = "eef344ce" /\ chksum(tla) = "b73aae7f") (chksum(pcal) = "bfeeb2f5" /\ chksum(tla) = "93862fcd") (chksum(pcal) = "6199d9" /\ chksum(tla) = "12ced0da") (chksum(pcal) = "d2273aea" /\ chksum(tla) = "b5e40127") (chksum(pcal) = "6fb9c2c0" /\ chksum(tla) = "956625dd") (chksum(pcal) = "deb6ae30" /\ chksum(tla) = "6d233143") (chksum(pcal) = "8a76d8d1" /\ chksum(tla) = "633b42d2") (chksum(pcal) = "10df42ac" /\ chksum(tla) = "3b7863d2") (chksum(pcal) = "e0d85759" /\ chksum(tla) = "9ab63665") (chksum(pcal) = "6810b04a" /\ chksum(tla) = "e1497760") (chksum(pcal) = "9a4aa047" /\ chksum(tla) = "39fada2a") (chksum(pcal) = "879306b3" /\ chksum(tla) = "a44d770f") (chksum(pcal) = "ba4d2547" /\ chksum(tla) = "cefb538a") (chksum(pcal) = "ba4d2547" /\ chksum(tla) = "cefb538a") (chksum(pcal) = "3ef7b99a" /\ chksum(tla) = "e61146f4") (chksum(pcal) = "e439985b" /\ chksum(tla) = "7a2a009a") (chksum(pcal) = "b1cf2032" /\ chksum(tla) = "d844b090") (chksum(pcal) = "51d845a6" /\ chksum(tla) = "c4365c53") (chksum(pcal) = "f6e10311" /\ chksum(tla) = "205517c0") (chksum(pcal) = "f6e10311" /\ chksum(tla) = "205517c0") (chksum(pcal) = "fcbd4b8c" /\ chksum(tla) = "3b824514") (chksum(pcal) = "8db05c1c" /\ chksum(tla) = "43d0ef2a") (chksum(pcal) = "43aba378" /\ chksum(tla) = "3baec222") (chksum(pcal) = "f324cab4" /\ chksum(tla) = "e46b9b1c") (chksum(pcal) = "bc53f899" /\ chksum(tla) = "aca4552d") (chksum(pcal) = "977eb869" /\ chksum(tla) = "37f2ba54") (chksum(pcal) = "e3f769ef" /\ chksum(tla) = "6be5ba0a") (chksum(pcal) = "844f01e5" /\ chksum(tla) = "a5d60d3c") (chksum(pcal) = "32aeaf9" /\ chksum(tla) = "ab08acb6") (chksum(pcal) = "6bd30667" /\ chksum(tla) = "514bcee2") (chksum(pcal) = "130d5171" /\ chksum(tla) = "c22c1aae") (chksum(pcal) = "32aeaf9" /\ chksum(tla) = "ab08acb6") (chksum(pcal) = "f66c1dd2" /\ chksum(tla) = "4ecd99b3") (chksum(pcal) = "aca9010b" /\ chksum(tla) = "8238474d") (chksum(pcal) = "bad5b442" /\ chksum(tla) = "1e379f7a") (chksum(pcal) = "d9667a04" /\ chksum(tla) = "971610ae") (chksum(pcal) = "9151c33f" /\ chksum(tla) = "972acf") (chksum(pcal) = "3a68dec1" /\ chksum(tla) = "e058e82d") (chksum(pcal) = "3a68dec1" /\ chksum(tla) = "e058e82d") (chksum(pcal) = "9ee8aa69" /\ chksum(tla) = "14958d24") (chksum(pcal) = "122e7f31" /\ chksum(tla) = "8a28dc1d") (chksum(pcal) = "6a963ea3" /\ chksum(tla) = "ce8dc20a") (chksum(pcal) = "55e18a32" /\ chksum(tla) = "70c78b7a")
\* Process variable controllerSet of process swFailureProc at line 1458 col 76 changed to controllerSet_
\* Process variable nxtController of process swFailureProc at line 1459 col 5 changed to nxtController_
\* Process variable prevLockHolder of process swFailureProc at line 1459 col 25 changed to prevLockHolder_
\* Process variable controllerSet of process swResolveFailure at line 1544 col 83 changed to controllerSet_s
\* Process variable nxtController of process swResolveFailure at line 1545 col 5 changed to nxtController_s
\* Process variable stepOfFailure of process controllerSequencer at line 1687 col 50 changed to stepOfFailure_
\* Process variable event of process nibEventHandler at line 1799 col 15 changed to event_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 1996 col 29 changed to stepOfFailure_c
\* Process variable stepOfFailure of process controllerEventHandler at line 2210 col 80 changed to stepOfFailure_co
VARIABLES switchLock, controllerLocalLock, controllerGlobalLock, FirstInstall, 
          sw_fail_ordering_var, ContProcSet, SwProcSet, swSeqChangedStatus, 
          controller2Switch, switch2Controller, switchStatus, installedIRs, 
          installedBy, swFailedNum, swNumEvent, NicAsic2OfaBuff, 
          Ofa2NicAsicBuff, Installer2OfaBuff, Ofa2InstallerBuff, TCAM, 
          controlMsgCounter, switchControllerRoleStatus, 
          switchGeneratedEventSet, auxEventCounter, 
          controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
          switchOrdering, dependencyGraph, IR2SW, irCounter, MAX_IR_COUNTER, 
          idThreadWorkingOnIR, workerThreadRanking, workerLocalQueue, 
          ofcSwSuspensionStatus, processedEvents, localEventLog, 
          controllerRoleInSW, nibEventQueue, roleUpdateStatus, isOfcEnabled, 
          setScheduledRoleUpdates, ofcModuleTerminationStatus, 
          ofcModuleInitStatus, setRecoveredSwWithSlaveRole, 
          fetchedIRsBeforePassingToWorker, eventSkipList, masterState, 
          controllerStateNIB, IRStatus, NIBSwSuspensionStatus, IRQueueNIB, 
          subscribeList, SetScheduledIRs, ofcFailoverStateNIB, NIBEventLog, 
          pc

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
getNonSlaveController(swID) == {x \in DOMAIN switchControllerRoleStatus[swID]: switchControllerRoleStatus[swID][x] # ROLE_SLAVE}
isControllerMaster(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_MASTER
isControllerSlave(swID, cid) == switchControllerRoleStatus[swID][cid] = ROLE_SLAVE
hasModificationAccess(swID, cid) == ~isControllerSlave(swID, cid)

swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed


returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                                                     /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1}

getSetIRsForSwitch(SID) == {x \in 1..MAX_NUM_IRs: IR2SW[x] = SID}
shouldSendFailMsgToAll(msg) == \/ msg.type \in {NIC_ASIC_DOWN, OFA_DOWN}
                               \/ /\ msg.type = KEEP_ALIVE
                                  /\ msg.status.installerStatus = INSTALLER_DOWN


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
shouldSendRecoveryMsgToAll(msg) == \/ msg.type \in {OFA_DOWN}
                                   \/ /\ msg.type = KEEP_ALIVE
                                      /\ msg.status.installerStatus \in {INSTALLER_DOWN, INSTALLER_UP}


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
                                                          /\ NIBSwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                          /\ x \notin SetScheduledIRs[IR2SW[x]]}



shouldWorkerTerminate(CID, TID) == ofcModuleTerminationStatus[CID][TID] = TERMINATE_INIT
shouldEventHandlerTerminate(CID) == ofcModuleTerminationStatus[CID][CONT_EVENT] = TERMINATE_INIT
shouldMonitoringServerTerminate(CID) == /\ ofcModuleTerminationStatus[CID][CONT_MONITOR] = TERMINATE_INIT
                                        /\ ~\E x \in 1..MAX_NUM_IRs: /\ IRStatus[x] = IR_SENT
                                                                     /\ ofcSwSuspensionStatus[CID][IR2SW[x]] = SW_RUN

allSwitchesEitherEqualRoleOrSuspended(CID) == \A x \in SW: \/ controllerRoleInSW[CID][x] = ROLE_EQUAL
                                                           \/ ofcSwSuspensionStatus[CID][x] = SW_SUSPEND
getSetSwitchInSlaveRole(CID) == {x \in SW: controllerRoleInSW[CID][x] = ROLE_SLAVE}
getSetSwitchInEqualRole(CID) == {x \in SW: controllerRoleInSW[CID][x] = ROLE_EQUAL}
getSetSwitchInNonMasterRole(CID) == getSetSwitchInSlaveRole(CID) \cup getSetSwitchInEqualRole(CID)
allModulesTerminated(CID) == \A x \in DOMAIN ofcModuleTerminationStatus[CID]:
                                                ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE
allWorkersTerminated(CID) == \A x \in CONTROLLER_THREAD_POOL:
                                                ofcModuleTerminationStatus[CID][x] = TERMINATE_DONE
MonitoringServerTerminated(CID) == ofcModuleTerminationStatus[CID][CONT_MONITOR] = TERMINATE_DONE
existRecoveredSwitchWithSlaveRole(CID) == setRecoveredSwWithSlaveRole[CID] # {}
areEventsEquivalent(event1, event2) == /\ \A x \in DOMAIN event1: \/ x \in {"auxNum"}
                                                                  \/ /\ x \in DOMAIN event2
                                                                     /\ event1[x] = event2[x]
                                       /\ \A x \in DOMAIN event2: \/ x \in {"auxNum"}
                                                                  \/ /\ x \in DOMAIN event1
                                                                     /\ event1[x] = event2[x]

isSwitchSuspended(CID, sw) == ofcSwSuspensionStatus[CID][sw] = SW_SUSPEND



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
workerCanSendTheIR(CID, nextToSent) == /\ ~isSwitchSuspended(CID, nextToSent.to)
                                       /\ \/ /\ nextToSent.type = ROLE_REQ
                                             /\ roleUpdateStatus[CID][nextToSent.to].status = IR_NONE
                                          \/ /\ nextToSent.type = INSTALL_FLOW
                                             /\ IRStatus[nextToSent.IR] = IR_NONE
workerShouldFastRecovery(CID, nextToSent) == \/ /\ nextToSent.type = ROLE_REQ
                                                /\ roleUpdateStatus[CID][nextToSent.to].status = IR_NONE
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


isFinished(CID) == /\ \A x \in getSetIRsForSwitch(CID): IRStatus[x] = IR_DONE
                   /\ \/ SHOULD_FAILOVER = 0
                      \/ /\ \A x \in SW: switchControllerRoleStatus[x][ofc0] = ROLE_SLAVE
                         /\ \A x \in SW: switchControllerRoleStatus[x][ofc1] = ROLE_MASTER

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, controllerSet_, 
          nxtController_, prevLockHolder_, failedSet, statusResolveMsg, 
          recoveredElem, controllerSet_s, nxtController_s, prevLockHolder, 
          eventMsg, controllerSet, nxtController, eventID, toBeScheduledIRs, 
          nextIR, stepOfFailure_, subscriberOfcSet, ofcID, event_, swSet, 
          currSW, entry, index, event, pulledNIBEventLog, remainingEvents, 
          receivedEventsCopy, nextToSent, entryIndex, rowIndex, rowRemove, 
          removeRow, stepOfFailure_c, monitoringEvent, setIRsToReset, resetIR, 
          stepOfFailure_co, notifOFC, isEventProcessed, msg, stepOfFailure, 
          controllerFailedModules

vars == << switchLock, controllerLocalLock, controllerGlobalLock, 
           FirstInstall, sw_fail_ordering_var, ContProcSet, SwProcSet, 
           swSeqChangedStatus, controller2Switch, switch2Controller, 
           switchStatus, installedIRs, installedBy, swFailedNum, swNumEvent, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
           Ofa2InstallerBuff, TCAM, controlMsgCounter, 
           switchControllerRoleStatus, switchGeneratedEventSet, 
           auxEventCounter, controllerSubmoduleFailNum, 
           controllerSubmoduleFailStat, switchOrdering, dependencyGraph, 
           IR2SW, irCounter, MAX_IR_COUNTER, idThreadWorkingOnIR, 
           workerThreadRanking, workerLocalQueue, ofcSwSuspensionStatus, 
           processedEvents, localEventLog, controllerRoleInSW, nibEventQueue, 
           roleUpdateStatus, isOfcEnabled, setScheduledRoleUpdates, 
           ofcModuleTerminationStatus, ofcModuleInitStatus, 
           setRecoveredSwWithSlaveRole, fetchedIRsBeforePassingToWorker, 
           eventSkipList, masterState, controllerStateNIB, IRStatus, 
           NIBSwSuspensionStatus, IRQueueNIB, subscribeList, SetScheduledIRs, 
           ofcFailoverStateNIB, NIBEventLog, pc, ingressPkt, ingressIR, 
           egressMsg, ofaInMsg, ofaOutConfirmation, installerInIR, statusMsg, 
           notFailedSet, failedElem, controllerSet_, nxtController_, 
           prevLockHolder_, failedSet, statusResolveMsg, recoveredElem, 
           controllerSet_s, nxtController_s, prevLockHolder, eventMsg, 
           controllerSet, nxtController, eventID, toBeScheduledIRs, nextIR, 
           stepOfFailure_, subscriberOfcSet, ofcID, event_, swSet, currSW, 
           entry, index, event, pulledNIBEventLog, remainingEvents, 
           receivedEventsCopy, nextToSent, entryIndex, rowIndex, rowRemove, 
           removeRow, stepOfFailure_c, monitoringEvent, setIRsToReset, 
           resetIR, stepOfFailure_co, notifOFC, isEventProcessed, msg, 
           stepOfFailure, controllerFailedModules >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({ASYNC_NET_EVE_GEN} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({rc0} \X {CONT_SEQ})) \cup (({ofc0, ofc1} \X {NIB_EVENT_HANDLER})) \cup (({ofc0, ofc1} \X {FAILOVER_HANDLER})) \cup (({ofc0, ofc1} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0, ofc1} \X {CONT_EVENT})) \cup (({ofc0, ofc1} \X {CONT_MONITOR})) \cup ((({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG})) \cup (( {"proc"} \X {OFC_FAILOVER}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLocalLock = [x \in {ofc0, ofc1, rc0} |-> <<NO_LOCK, NO_LOCK>>]
        /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
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
        /\ swNumEvent = [x \in SW |-> 0]
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> <<>>]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ switchControllerRoleStatus = [x \in SW |-> (ofc0 :> ROLE_MASTER @@ ofc1 :> ROLE_SLAVE)]
        /\ switchGeneratedEventSet = [x \in SW |-> {}]
        /\ auxEventCounter = 0
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
        /\ ofcSwSuspensionStatus = [y \in {ofc0, ofc1} |-> [x \in SW |-> SW_RUN]]
        /\ processedEvents = [x \in {ofc0, ofc1} |-> {}]
        /\ localEventLog = [x \in {ofc0, ofc1} |-> [y \in SW |-> <<>>]]
        /\ controllerRoleInSW = (ofc0 :> [x \in SW |-> ROLE_MASTER]) @@ (ofc1 :> [x \in SW |-> ROLE_SLAVE])
        /\ nibEventQueue = [x \in {ofc0, ofc1} |-> <<>>]
        /\ roleUpdateStatus = [x \in {ofc0, ofc1} |-> [y \in SW |-> [roletpye |-> ROLE_EMPTY, status |-> IR_NONE]]]
        /\ isOfcEnabled = [x \in {ofc0} |-> TRUE] @@ [x \in {ofc1} |-> FALSE]
        /\ setScheduledRoleUpdates = [x \in {ofc0, ofc1} |-> {}]
        /\ ofcModuleTerminationStatus = [x \in {ofc0, ofc1} |->
                                             [y \in ({CONT_MONITOR, CONT_EVENT} \cup CONTROLLER_THREAD_POOL) |-> TERMINATE_NONE]]
        /\ ofcModuleInitStatus = (ofc0 :> [x \in {CONT_EVENT} |-> INIT_PROCESS]) @@ (ofc1 :> [x \in {CONT_EVENT} |-> INIT_RUN])
        /\ setRecoveredSwWithSlaveRole = [x \in {ofc0, ofc1} |-> {}]
        /\ fetchedIRsBeforePassingToWorker = [x \in {ofc0, ofc1} |-> <<>>]
        /\ eventSkipList = [x \in {ofc0, ofc1} |-> [y \in SW |-> <<>>]]
        /\ masterState = (ofc0 :> ROLE_MASTER @@ ofc1 :> ROLE_SLAVE @@ rc0 :> ROLE_MASTER)
        /\ controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatus = [x \in 1..MAX_NUM_IRs |-> IR_NONE]
        /\ NIBSwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ subscribeList = [IRQueueNIB |-> {ofc0}, SwSuspensionStatus |-> {ofc0}]
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ ofcFailoverStateNIB = [y \in {ofc0, ofc1} |-> FAILOVER_NONE]
        /\ NIBEventLog = [x \in SW |-> <<>>]
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
        /\ controllerSet_ = [self \in ({SW_FAILURE_PROC} \X SW) |-> {}]
        /\ nxtController_ = [self \in ({SW_FAILURE_PROC} \X SW) |-> ""]
        /\ prevLockHolder_ = [self \in ({SW_FAILURE_PROC} \X SW) |-> <<NO_LOCK, NO_LOCK>>]
        (* Process swResolveFailure *)
        /\ failedSet = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> [type |-> 0]]
        /\ recoveredElem = [self \in ({SW_RESOLVE_PROC} \X SW) |-> ""]
        /\ controllerSet_s = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ nxtController_s = [self \in ({SW_RESOLVE_PROC} \X SW) |-> ""]
        /\ prevLockHolder = [self \in ({SW_RESOLVE_PROC} \X SW) |-> <<NO_LOCK, NO_LOCK>>]
        (* Process asyncNetworkEventGenerator *)
        /\ eventMsg = [self \in ({ASYNC_NET_EVE_GEN} \X SW) |-> [type |-> 0]]
        /\ controllerSet = [self \in ({ASYNC_NET_EVE_GEN} \X SW) |-> {}]
        /\ nxtController = [self \in ({ASYNC_NET_EVE_GEN} \X SW) |-> ""]
        /\ eventID = [self \in ({ASYNC_NET_EVE_GEN} \X SW) |-> 0]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ subscriberOfcSet = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ ofcID = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        (* Process nibEventHandler *)
        /\ event_ = [self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) |-> [type |-> 0]]
        (* Process ofcFailoverHandler *)
        /\ swSet = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> {}]
        /\ currSW = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> 0]
        /\ entry = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> [type |-> 0]]
        /\ index = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> 0]
        /\ event = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> [type |-> 0]]
        /\ pulledNIBEventLog = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> <<>>]
        /\ remainingEvents = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> <<>>]
        /\ receivedEventsCopy = [self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) |-> [type |-> <<>>]]
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
        /\ stepOfFailure_co = [self \in ({ofc0, ofc1} \X {CONT_EVENT}) |-> 0]
        /\ notifOFC = [self \in ({ofc0, ofc1} \X {CONT_EVENT}) |-> 0]
        /\ isEventProcessed = [self \in ({ofc0, ofc1} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0, ofc1} \X {CONT_MONITOR}) |-> [type |-> 0]]
        /\ stepOfFailure = [self \in ({ofc0, ofc1} \X {CONT_MONITOR}) |-> 0]
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
                                        [] self \in ({ASYNC_NET_EVE_GEN} \X SW) -> "asyncNetEventGenProc"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({rc0} \X {CONT_SEQ}) -> "ControllerSeqProc"
                                        [] self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) -> "NibEventHandlerProc"
                                        [] self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) -> "ofcFailoverHandlerProc"
                                        [] self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0, ofc1} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0, ofc1} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in (({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG}) -> "ControllerWatchDogProc"
                                        [] self \in ( {"proc"} \X {OFC_FAILOVER}) -> "OfcFailoverNewMasterInitialization"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                             /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                   /\ switchLock[2] = self[2]
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type \in {INSTALL_FLOW, ROLE_REQ, FLOW_STAT_REQ}, 
                                       "Failure of assertion at line 1209, column 9.")
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
                                                             "Failure of assertion at line 1219, column 13.")
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
                                       "Failure of assertion at line 962, column 9 of macro called at line 1227, column 9.")
                             /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << controllerLocalLock, 
                                             controllerGlobalLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             switch2Controller, switchStatus, 
                                             swFailedNum, swNumEvent, 
                                             NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, 
                                             controlMsgCounter, 
                                             switchGeneratedEventSet, 
                                             auxEventCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             ofcSwSuspensionStatus, 
                                             processedEvents, localEventLog, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             ofcModuleInitStatus, 
                                             setRecoveredSwWithSlaveRole, 
                                             fetchedIRsBeforePassingToWorker, 
                                             eventSkipList, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             NIBSwSuspensionStatus, IRQueueNIB, 
                                             subscribeList, SetScheduledIRs, 
                                             ofcFailoverStateNIB, NIBEventLog, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, controllerSet_, 
                                             nxtController_, prevLockHolder_, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, controllerSet_s, 
                                             nxtController_s, prevLockHolder, 
                                             eventMsg, controllerSet, 
                                             nxtController, eventID, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event_, swSet, currSW, 
                                             entry, index, event, 
                                             pulledNIBEventLog, 
                                             remainingEvents, 
                                             receivedEventsCopy, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure_co, 
                                             notifOFC, isEventProcessed, msg, 
                                             stepOfFailure, 
                                             controllerFailedModules >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(ingressIR'[self].type \in {ROLE_REQ, INSTALL_FLOW}, 
                                   "Failure of assertion at line 1252, column 9.")
                         /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                         /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                            \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                               /\ switchLock[2] = self[2]
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << controllerLocalLock, 
                                         controllerGlobalLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, swSeqChangedStatus, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, installedBy, 
                                         swFailedNum, swNumEvent, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         switchControllerRoleStatus, 
                                         switchGeneratedEventSet, 
                                         auxEventCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, workerLocalQueue, 
                                         ofcSwSuspensionStatus, 
                                         processedEvents, localEventLog, 
                                         controllerRoleInSW, nibEventQueue, 
                                         roleUpdateStatus, isOfcEnabled, 
                                         setScheduledRoleUpdates, 
                                         ofcModuleTerminationStatus, 
                                         ofcModuleInitStatus, 
                                         setRecoveredSwWithSlaveRole, 
                                         fetchedIRsBeforePassingToWorker, 
                                         eventSkipList, masterState, 
                                         controllerStateNIB, IRStatus, 
                                         NIBSwSuspensionStatus, IRQueueNIB, 
                                         subscribeList, SetScheduledIRs, 
                                         ofcFailoverStateNIB, NIBEventLog, 
                                         ingressPkt, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         controllerSet_, nxtController_, 
                                         prevLockHolder_, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         controllerSet_s, nxtController_s, 
                                         prevLockHolder, eventMsg, 
                                         controllerSet, nxtController, eventID, 
                                         toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, subscriberOfcSet, 
                                         ofcID, event_, swSet, currSW, entry, 
                                         index, event, pulledNIBEventLog, 
                                         remainingEvents, receivedEventsCopy, 
                                         nextToSent, entryIndex, rowIndex, 
                                         rowRemove, removeRow, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure_co, notifOFC, 
                                         isEventProcessed, msg, stepOfFailure, 
                                         controllerFailedModules >>

SwitchNicAsicInsertToOfaBuff(self) == /\ pc[self] = "SwitchNicAsicInsertToOfaBuff"
                                      /\ IF swCanReceivePackets(self[2])
                                            THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                    \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                       /\ switchLock[2] = self[2]
                                                 /\ switchLock' = <<OFA_IN, self[2]>>
                                                 /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Append(NicAsic2OfaBuff[self[2]], ingressIR[self])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                                 /\ UNCHANGED ingressIR
                                            ELSE /\ ingressIR' = [ingressIR EXCEPT ![self] = [type |-> 0]]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                                 /\ UNCHANGED << switchLock, 
                                                                 NicAsic2OfaBuff >>
                                      /\ UNCHANGED << controllerLocalLock, 
                                                      controllerGlobalLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      installedBy, swFailedNum, 
                                                      swNumEvent, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchControllerRoleStatus, 
                                                      switchGeneratedEventSet, 
                                                      auxEventCounter, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      workerLocalQueue, 
                                                      ofcSwSuspensionStatus, 
                                                      processedEvents, 
                                                      localEventLog, 
                                                      controllerRoleInSW, 
                                                      nibEventQueue, 
                                                      roleUpdateStatus, 
                                                      isOfcEnabled, 
                                                      setScheduledRoleUpdates, 
                                                      ofcModuleTerminationStatus, 
                                                      ofcModuleInitStatus, 
                                                      setRecoveredSwWithSlaveRole, 
                                                      fetchedIRsBeforePassingToWorker, 
                                                      eventSkipList, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      NIBSwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      subscribeList, 
                                                      SetScheduledIRs, 
                                                      ofcFailoverStateNIB, 
                                                      NIBEventLog, ingressPkt, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      controllerSet_, 
                                                      nxtController_, 
                                                      prevLockHolder_, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      controllerSet_s, 
                                                      nxtController_s, 
                                                      prevLockHolder, eventMsg, 
                                                      controllerSet, 
                                                      nxtController, eventID, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      subscriberOfcSet, ofcID, 
                                                      event_, swSet, currSW, 
                                                      entry, index, event, 
                                                      pulledNIBEventLog, 
                                                      remainingEvents, 
                                                      receivedEventsCopy, 
                                                      nextToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      removeRow, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure_co, 
                                                      notifOFC, 
                                                      isEventProcessed, msg, 
                                                      stepOfFailure, 
                                                      controllerFailedModules >>

swNicAsicProcPacketIn(self) == SwitchRcvPacket(self)
                                  \/ SwitchNicAsicInsertToOfaBuff(self)

SwitchFromOFAPacket(self) == /\ pc[self] = "SwitchFromOFAPacket"
                             /\ swCanReceivePackets(self[2])
                             /\ Len(Ofa2NicAsicBuff[self[2]]) > 0
                             /\ egressMsg' = [egressMsg EXCEPT ![self] = Head(Ofa2NicAsicBuff[self[2]])]
                             /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                             /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                   /\ switchLock[2] = self[2]
                             /\ switchLock' = self
                             /\ Assert(egressMsg'[self].type \in {INSTALLED_SUCCESSFULLY, ROLE_REPLY, BAD_REQUEST}, 
                                       "Failure of assertion at line 1280, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << controllerLocalLock, 
                                             controllerGlobalLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, swNumEvent, 
                                             NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             switchGeneratedEventSet, 
                                             auxEventCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             ofcSwSuspensionStatus, 
                                             processedEvents, localEventLog, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             ofcModuleInitStatus, 
                                             setRecoveredSwWithSlaveRole, 
                                             fetchedIRsBeforePassingToWorker, 
                                             eventSkipList, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             NIBSwSuspensionStatus, IRQueueNIB, 
                                             subscribeList, SetScheduledIRs, 
                                             ofcFailoverStateNIB, NIBEventLog, 
                                             ingressPkt, ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, controllerSet_, 
                                             nxtController_, prevLockHolder_, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, controllerSet_s, 
                                             nxtController_s, prevLockHolder, 
                                             eventMsg, controllerSet, 
                                             nxtController, eventID, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event_, swSet, currSW, 
                                             entry, index, event, 
                                             pulledNIBEventLog, 
                                             remainingEvents, 
                                             receivedEventsCopy, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure_co, 
                                             notifOFC, isEventProcessed, msg, 
                                             stepOfFailure, 
                                             controllerFailedModules >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                            /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                               \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                  /\ switchLock[2] = self[2]
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 962, column 9 of macro called at line 1287, column 17.")
                                            /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ switch2Controller' = [switch2Controller EXCEPT ![egressMsg[self].to] = Append(switch2Controller[egressMsg[self].to], egressMsg[self])]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED egressMsg
                                       ELSE /\ egressMsg' = [egressMsg EXCEPT ![self] = [type |-> 0]]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED << switchLock, 
                                                            switch2Controller >>
                                 /\ UNCHANGED << controllerLocalLock, 
                                                 controllerGlobalLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switchStatus, installedIRs, 
                                                 installedBy, swFailedNum, 
                                                 swNumEvent, NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 switchControllerRoleStatus, 
                                                 switchGeneratedEventSet, 
                                                 auxEventCounter, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, 
                                                 dependencyGraph, IR2SW, 
                                                 irCounter, MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 workerLocalQueue, 
                                                 ofcSwSuspensionStatus, 
                                                 processedEvents, 
                                                 localEventLog, 
                                                 controllerRoleInSW, 
                                                 nibEventQueue, 
                                                 roleUpdateStatus, 
                                                 isOfcEnabled, 
                                                 setScheduledRoleUpdates, 
                                                 ofcModuleTerminationStatus, 
                                                 ofcModuleInitStatus, 
                                                 setRecoveredSwWithSlaveRole, 
                                                 fetchedIRsBeforePassingToWorker, 
                                                 eventSkipList, masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 NIBSwSuspensionStatus, 
                                                 IRQueueNIB, subscribeList, 
                                                 SetScheduledIRs, 
                                                 ofcFailoverStateNIB, 
                                                 NIBEventLog, ingressPkt, 
                                                 ingressIR, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 controllerSet_, 
                                                 nxtController_, 
                                                 prevLockHolder_, failedSet, 
                                                 statusResolveMsg, 
                                                 recoveredElem, 
                                                 controllerSet_s, 
                                                 nxtController_s, 
                                                 prevLockHolder, eventMsg, 
                                                 controllerSet, nxtController, 
                                                 eventID, toBeScheduledIRs, 
                                                 nextIR, stepOfFailure_, 
                                                 subscriberOfcSet, ofcID, 
                                                 event_, swSet, currSW, entry, 
                                                 index, event, 
                                                 pulledNIBEventLog, 
                                                 remainingEvents, 
                                                 receivedEventsCopy, 
                                                 nextToSent, entryIndex, 
                                                 rowIndex, rowRemove, 
                                                 removeRow, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure_co, notifOFC, 
                                                 isEventProcessed, msg, 
                                                 stepOfFailure, 
                                                 controllerFailedModules >>

swNicAsicProcPacketOut(self) == SwitchFromOFAPacket(self)
                                   \/ SwitchNicAsicSendOutMsg(self)

SwitchOfaProcIn(self) == /\ pc[self] = "SwitchOfaProcIn"
                         /\ swOFACanProcessIRs(self[2])
                         /\ Len(NicAsic2OfaBuff[self[2]]) > 0
                         /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                         /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                            \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                               /\ switchLock[2] = self[2]
                         /\ switchLock' = self
                         /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = Head(NicAsic2OfaBuff[self[2]])]
                         /\ Assert(ofaInMsg'[self].to = self[2], 
                                   "Failure of assertion at line 1318, column 9.")
                         /\ Assert(\/ /\ ofaInMsg'[self].type = ROLE_REQ
                                      /\ ofaInMsg'[self].roletype \in {ROLE_SLAVE, ROLE_MASTER, ROLE_EQUAL}
                                   \/ /\ ofaInMsg'[self].type = INSTALL_FLOW
                                      /\ ofaInMsg'[self].IR  \in 1..MAX_NUM_IRs, 
                                   "Failure of assertion at line 1319, column 9.")
                         /\ Assert(ofaInMsg'[self].from \in {ofc0, ofc1}, 
                                   "Failure of assertion at line 1323, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << controllerLocalLock, 
                                         controllerGlobalLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         installedBy, swFailedNum, swNumEvent, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         switchControllerRoleStatus, 
                                         switchGeneratedEventSet, 
                                         auxEventCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, workerLocalQueue, 
                                         ofcSwSuspensionStatus, 
                                         processedEvents, localEventLog, 
                                         controllerRoleInSW, nibEventQueue, 
                                         roleUpdateStatus, isOfcEnabled, 
                                         setScheduledRoleUpdates, 
                                         ofcModuleTerminationStatus, 
                                         ofcModuleInitStatus, 
                                         setRecoveredSwWithSlaveRole, 
                                         fetchedIRsBeforePassingToWorker, 
                                         eventSkipList, masterState, 
                                         controllerStateNIB, IRStatus, 
                                         NIBSwSuspensionStatus, IRQueueNIB, 
                                         subscribeList, SetScheduledIRs, 
                                         ofcFailoverStateNIB, NIBEventLog, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         controllerSet_, nxtController_, 
                                         prevLockHolder_, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         controllerSet_s, nxtController_s, 
                                         prevLockHolder, eventMsg, 
                                         controllerSet, nxtController, eventID, 
                                         toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, subscriberOfcSet, 
                                         ofcID, event_, swSet, currSW, entry, 
                                         index, event, pulledNIBEventLog, 
                                         remainingEvents, receivedEventsCopy, 
                                         nextToSent, entryIndex, rowIndex, 
                                         rowRemove, removeRow, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure_co, notifOFC, 
                                         isEventProcessed, msg, stepOfFailure, 
                                         controllerFailedModules >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ Assert(ofaInMsg[self].type \in {INSTALL_FLOW, ROLE_REQ}, 
                                                     "Failure of assertion at line 1334, column 17.")
                                           /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                                 THEN /\ IF hasModificationAccess(self[2], ofaInMsg[self].from)
                                                            THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                                    \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                                       /\ switchLock[2] = self[2]
                                                                 /\ switchLock' = <<INSTALLER, self[2]>>
                                                                 /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]],
                                                                                                                                            [IR |-> ofaInMsg[self].IR,
                                                                                                                                            from |-> ofaInMsg[self].from])]
                                                                 /\ UNCHANGED Ofa2NicAsicBuff
                                                            ELSE /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                                    \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                                       /\ switchLock[2] = self[2]
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
                                                                           "Failure of assertion at line 1358, column 21.")
                                                                 /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                                    \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                                       /\ switchLock[2] = self[2]
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
                                /\ UNCHANGED << controllerLocalLock, 
                                                controllerGlobalLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                installedBy, swFailedNum, 
                                                swNumEvent, NicAsic2OfaBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchGeneratedEventSet, 
                                                auxEventCounter, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                ofcSwSuspensionStatus, 
                                                processedEvents, localEventLog, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                roleUpdateStatus, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                ofcModuleInitStatus, 
                                                setRecoveredSwWithSlaveRole, 
                                                fetchedIRsBeforePassingToWorker, 
                                                eventSkipList, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                NIBSwSuspensionStatus, 
                                                IRQueueNIB, subscribeList, 
                                                SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                NIBEventLog, ingressPkt, 
                                                ingressIR, egressMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                controllerSet_, nxtController_, 
                                                prevLockHolder_, failedSet, 
                                                statusResolveMsg, 
                                                recoveredElem, controllerSet_s, 
                                                nxtController_s, 
                                                prevLockHolder, eventMsg, 
                                                controllerSet, nxtController, 
                                                eventID, toBeScheduledIRs, 
                                                nextIR, stepOfFailure_, 
                                                subscriberOfcSet, ofcID, 
                                                event_, swSet, currSW, entry, 
                                                index, event, 
                                                pulledNIBEventLog, 
                                                remainingEvents, 
                                                receivedEventsCopy, nextToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure_co, 
                                                notifOFC, isEventProcessed, 
                                                msg, stepOfFailure, 
                                                controllerFailedModules >>

SwitchSendRoleReply(self) == /\ pc[self] = "SwitchSendRoleReply"
                             /\ IF swOFACanProcessIRs(self[2])
                                   THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                        /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                              /\ switchLock[2] = self[2]
                                        /\ switchLock' = <<NIC_ASIC_OUT, self[2]>>
                                        /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> ROLE_REPLY,
                                                                                                                                     from |-> self[2],
                                                                                                                                     roletype |-> (ofaInMsg[self].roletype),
                                                                                                                                     to |-> (ofaInMsg[self].from)])]
                                        /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                        /\ UNCHANGED ofaInMsg
                                   ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                        /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                        /\ UNCHANGED << switchLock, 
                                                        Ofa2NicAsicBuff >>
                             /\ UNCHANGED << controllerLocalLock, 
                                             controllerGlobalLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, swNumEvent, 
                                             NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             switchGeneratedEventSet, 
                                             auxEventCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             ofcSwSuspensionStatus, 
                                             processedEvents, localEventLog, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             ofcModuleInitStatus, 
                                             setRecoveredSwWithSlaveRole, 
                                             fetchedIRsBeforePassingToWorker, 
                                             eventSkipList, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             NIBSwSuspensionStatus, IRQueueNIB, 
                                             subscribeList, SetScheduledIRs, 
                                             ofcFailoverStateNIB, NIBEventLog, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, controllerSet_, 
                                             nxtController_, prevLockHolder_, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, controllerSet_s, 
                                             nxtController_s, prevLockHolder, 
                                             eventMsg, controllerSet, 
                                             nxtController, eventID, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event_, swSet, currSW, 
                                             entry, index, event, 
                                             pulledNIBEventLog, 
                                             remainingEvents, 
                                             receivedEventsCopy, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure_co, 
                                             notifOFC, isEventProcessed, msg, 
                                             stepOfFailure, 
                                             controllerFailedModules >>

ofaModuleProcPacketIn(self) == SwitchOfaProcIn(self)
                                  \/ SwitchOfaProcessPacket(self)
                                  \/ SwitchSendRoleReply(self)

SwitchOfaProcOut(self) == /\ pc[self] = "SwitchOfaProcOut"
                          /\ swOFACanProcessIRs(self[2])
                          /\ Installer2OfaBuff[self[2]] # <<>>
                          /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                /\ switchLock[2] = self[2]
                          /\ switchLock' = self
                          /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = Head(Installer2OfaBuff[self[2]])]
                          /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Tail(Installer2OfaBuff[self[2]])]
                          /\ Assert(ofaOutConfirmation'[self].IR \in 1..MAX_NUM_IRs, 
                                    "Failure of assertion at line 1394, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << controllerLocalLock, 
                                          controllerGlobalLock, FirstInstall, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          installedBy, swFailedNum, swNumEvent, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, 
                                          switchControllerRoleStatus, 
                                          switchGeneratedEventSet, 
                                          auxEventCounter, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, irCounter, MAX_IR_COUNTER, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          workerLocalQueue, 
                                          ofcSwSuspensionStatus, 
                                          processedEvents, localEventLog, 
                                          controllerRoleInSW, nibEventQueue, 
                                          roleUpdateStatus, isOfcEnabled, 
                                          setScheduledRoleUpdates, 
                                          ofcModuleTerminationStatus, 
                                          ofcModuleInitStatus, 
                                          setRecoveredSwWithSlaveRole, 
                                          fetchedIRsBeforePassingToWorker, 
                                          eventSkipList, masterState, 
                                          controllerStateNIB, IRStatus, 
                                          NIBSwSuspensionStatus, IRQueueNIB, 
                                          subscribeList, SetScheduledIRs, 
                                          ofcFailoverStateNIB, NIBEventLog, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, installerInIR, statusMsg, 
                                          notFailedSet, failedElem, 
                                          controllerSet_, nxtController_, 
                                          prevLockHolder_, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          controllerSet_s, nxtController_s, 
                                          prevLockHolder, eventMsg, 
                                          controllerSet, nxtController, 
                                          eventID, toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, subscriberOfcSet, 
                                          ofcID, event_, swSet, currSW, entry, 
                                          index, event, pulledNIBEventLog, 
                                          remainingEvents, receivedEventsCopy, 
                                          nextToSent, entryIndex, rowIndex, 
                                          rowRemove, removeRow, 
                                          stepOfFailure_c, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure_co, notifOFC, 
                                          isEventProcessed, msg, stepOfFailure, 
                                          controllerFailedModules >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                    \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                       /\ switchLock[2] = self[2]
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
                                      /\ UNCHANGED << controllerLocalLock, 
                                                      controllerGlobalLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      installedBy, swFailedNum, 
                                                      swNumEvent, 
                                                      NicAsic2OfaBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchControllerRoleStatus, 
                                                      switchGeneratedEventSet, 
                                                      auxEventCounter, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      workerLocalQueue, 
                                                      ofcSwSuspensionStatus, 
                                                      processedEvents, 
                                                      localEventLog, 
                                                      controllerRoleInSW, 
                                                      nibEventQueue, 
                                                      roleUpdateStatus, 
                                                      isOfcEnabled, 
                                                      setScheduledRoleUpdates, 
                                                      ofcModuleTerminationStatus, 
                                                      ofcModuleInitStatus, 
                                                      setRecoveredSwWithSlaveRole, 
                                                      fetchedIRsBeforePassingToWorker, 
                                                      eventSkipList, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      NIBSwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      subscribeList, 
                                                      SetScheduledIRs, 
                                                      ofcFailoverStateNIB, 
                                                      NIBEventLog, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, installerInIR, 
                                                      statusMsg, notFailedSet, 
                                                      failedElem, 
                                                      controllerSet_, 
                                                      nxtController_, 
                                                      prevLockHolder_, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      controllerSet_s, 
                                                      nxtController_s, 
                                                      prevLockHolder, eventMsg, 
                                                      controllerSet, 
                                                      nxtController, eventID, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      subscriberOfcSet, ofcID, 
                                                      event_, swSet, currSW, 
                                                      entry, index, event, 
                                                      pulledNIBEventLog, 
                                                      remainingEvents, 
                                                      receivedEventsCopy, 
                                                      nextToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      removeRow, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure_co, 
                                                      notifOFC, 
                                                      isEventProcessed, msg, 
                                                      stepOfFailure, 
                                                      controllerFailedModules >>

ofaModuleProcPacketOut(self) == SwitchOfaProcOut(self)
                                   \/ SendInstallationConfirmation(self)

SwitchInstallerProc(self) == /\ pc[self] = "SwitchInstallerProc"
                             /\ swCanInstallIRs(self[2])
                             /\ Len(Ofa2InstallerBuff[self[2]]) > 0
                             /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                             /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                   /\ switchLock[2] = self[2]
                             /\ switchLock' = self
                             /\ installerInIR' = [installerInIR EXCEPT ![self] = Head(Ofa2InstallerBuff[self[2]])]
                             /\ Assert(installerInIR'[self].IR \in 1..MAX_NUM_IRs, 
                                       "Failure of assertion at line 1430, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << controllerLocalLock, 
                                             controllerGlobalLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, swNumEvent, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             switchGeneratedEventSet, 
                                             auxEventCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             ofcSwSuspensionStatus, 
                                             processedEvents, localEventLog, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             ofcModuleInitStatus, 
                                             setRecoveredSwWithSlaveRole, 
                                             fetchedIRsBeforePassingToWorker, 
                                             eventSkipList, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             NIBSwSuspensionStatus, IRQueueNIB, 
                                             subscribeList, SetScheduledIRs, 
                                             ofcFailoverStateNIB, NIBEventLog, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             statusMsg, notFailedSet, 
                                             failedElem, controllerSet_, 
                                             nxtController_, prevLockHolder_, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, controllerSet_s, 
                                             nxtController_s, prevLockHolder, 
                                             eventMsg, controllerSet, 
                                             nxtController, eventID, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event_, swSet, currSW, 
                                             entry, index, event, 
                                             pulledNIBEventLog, 
                                             remainingEvents, 
                                             receivedEventsCopy, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure_co, 
                                             notifOFC, isEventProcessed, msg, 
                                             stepOfFailure, 
                                             controllerFailedModules >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                  \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                     /\ switchLock[2] = self[2]
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
                                    /\ UNCHANGED << controllerLocalLock, 
                                                    controllerGlobalLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, swFailedNum, 
                                                    swNumEvent, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    switchGeneratedEventSet, 
                                                    auxEventCounter, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    workerLocalQueue, 
                                                    ofcSwSuspensionStatus, 
                                                    processedEvents, 
                                                    localEventLog, 
                                                    controllerRoleInSW, 
                                                    nibEventQueue, 
                                                    roleUpdateStatus, 
                                                    isOfcEnabled, 
                                                    setScheduledRoleUpdates, 
                                                    ofcModuleTerminationStatus, 
                                                    ofcModuleInitStatus, 
                                                    setRecoveredSwWithSlaveRole, 
                                                    fetchedIRsBeforePassingToWorker, 
                                                    eventSkipList, masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    NIBSwSuspensionStatus, 
                                                    IRQueueNIB, subscribeList, 
                                                    SetScheduledIRs, 
                                                    ofcFailoverStateNIB, 
                                                    NIBEventLog, ingressPkt, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, controllerSet_, 
                                                    nxtController_, 
                                                    prevLockHolder_, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    controllerSet_s, 
                                                    nxtController_s, 
                                                    prevLockHolder, eventMsg, 
                                                    controllerSet, 
                                                    nxtController, eventID, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    subscriberOfcSet, ofcID, 
                                                    event_, swSet, currSW, 
                                                    entry, index, event, 
                                                    pulledNIBEventLog, 
                                                    remainingEvents, 
                                                    receivedEventsCopy, 
                                                    nextToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    removeRow, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure_co, notifOFC, 
                                                    isEventProcessed, msg, 
                                                    stepOfFailure, 
                                                    controllerFailedModules >>

SwitchInstallerSendConfirmation(self) == /\ pc[self] = "SwitchInstallerSendConfirmation"
                                         /\ IF swCanInstallIRs(self[2])
                                               THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                    /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                       \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                          /\ switchLock[2] = self[2]
                                                    /\ switchLock' = <<OFA_OUT, self[2]>>
                                                    /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Append(Installer2OfaBuff[self[2]], installerInIR[self])]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED installerInIR
                                               ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0]]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED << switchLock, 
                                                                    Installer2OfaBuff >>
                                         /\ UNCHANGED << controllerLocalLock, 
                                                         controllerGlobalLock, 
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
                                                         swNumEvent, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         switchControllerRoleStatus, 
                                                         switchGeneratedEventSet, 
                                                         auxEventCounter, 
                                                         controllerSubmoduleFailNum, 
                                                         controllerSubmoduleFailStat, 
                                                         switchOrdering, 
                                                         dependencyGraph, 
                                                         IR2SW, irCounter, 
                                                         MAX_IR_COUNTER, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         workerLocalQueue, 
                                                         ofcSwSuspensionStatus, 
                                                         processedEvents, 
                                                         localEventLog, 
                                                         controllerRoleInSW, 
                                                         nibEventQueue, 
                                                         roleUpdateStatus, 
                                                         isOfcEnabled, 
                                                         setScheduledRoleUpdates, 
                                                         ofcModuleTerminationStatus, 
                                                         ofcModuleInitStatus, 
                                                         setRecoveredSwWithSlaveRole, 
                                                         fetchedIRsBeforePassingToWorker, 
                                                         eventSkipList, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         NIBSwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         subscribeList, 
                                                         SetScheduledIRs, 
                                                         ofcFailoverStateNIB, 
                                                         NIBEventLog, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, 
                                                         controllerSet_, 
                                                         nxtController_, 
                                                         prevLockHolder_, 
                                                         failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, 
                                                         controllerSet_s, 
                                                         nxtController_s, 
                                                         prevLockHolder, 
                                                         eventMsg, 
                                                         controllerSet, 
                                                         nxtController, 
                                                         eventID, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         subscriberOfcSet, 
                                                         ofcID, event_, swSet, 
                                                         currSW, entry, index, 
                                                         event, 
                                                         pulledNIBEventLog, 
                                                         remainingEvents, 
                                                         receivedEventsCopy, 
                                                         nextToSent, 
                                                         entryIndex, rowIndex, 
                                                         rowRemove, removeRow, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure_co, 
                                                         notifOFC, 
                                                         isEventProcessed, msg, 
                                                         stepOfFailure, 
                                                         controllerFailedModules >>

installerModuleProc(self) == SwitchInstallerProc(self)
                                \/ SwitchInstallerInsert2TCAM(self)
                                \/ SwitchInstallerSendConfirmation(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ notFailedSet' = [notFailedSet EXCEPT ![self] = returnSwitchElementsNotFailed(self[2])]
                       /\ Assert(statusMsg[self].type = 0, 
                                 "Failure of assertion at line 1474, column 9.")
                       /\ notFailedSet'[self] # {}
                       /\ ~isFinished(self[2])
                       /\ swFailedNum[self[2]] < MAX_NUM_SW_FAILURE
                       /\ /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                          /\ switchLock[2] = self[2]
                       /\ self[2] \in Head(sw_fail_ordering_var)
                       /\ Assert((self[2]) \in Head(sw_fail_ordering_var), 
                                 "Failure of assertion at line 622, column 9 of macro called at line 1481, column 9.")
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{(self[2])})>> \o Tail(sw_fail_ordering_var)
                       /\ \E elem \in notFailedSet'[self]:
                            failedElem' = [failedElem EXCEPT ![self] = elem]
                       /\ IF failedElem'[self] = "cpu"
                             THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                  /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                            "Failure of assertion at line 709, column 9 of macro called at line 1490, column 17.")
                                  /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = Failed,
                                                                          ![self[2]].ofa = Failed,
                                                                          ![self[2]].installer = Failed]
                                  /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                  /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                  /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                        THEN /\ auxEventCounter' = auxEventCounter + 1
                                             /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                             /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                             /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                          swID |-> self[2],
                                                                                          num |-> controlMsgCounter'[self[2]],
                                                                                          auxNum |-> auxEventCounter']]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << controlMsgCounter, 
                                                             switchGeneratedEventSet, 
                                                             auxEventCounter, 
                                                             statusMsg >>
                                  /\ UNCHANGED controller2Switch
                             ELSE /\ IF failedElem'[self] = "ofa"
                                        THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                             /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed, 
                                                       "Failure of assertion at line 768, column 9 of macro called at line 1493, column 17.")
                                             /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = Failed]
                                             /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                             /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                   THEN /\ auxEventCounter' = auxEventCounter + 1
                                                        /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                        /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                        /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                                     swID |-> self[2],
                                                                                                     num |-> controlMsgCounter'[self[2]],
                                                                                                     auxNum |-> auxEventCounter']]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << controlMsgCounter, 
                                                                        switchGeneratedEventSet, 
                                                                        auxEventCounter, 
                                                                        statusMsg >>
                                             /\ UNCHANGED controller2Switch
                                        ELSE /\ IF failedElem'[self] = "installer"
                                                   THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                                        /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed, 
                                                                  "Failure of assertion at line 819, column 9 of macro called at line 1496, column 17.")
                                                        /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                        /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                                        /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                              THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                             "Failure of assertion at line 823, column 13 of macro called at line 1496, column 17.")
                                                                   /\ auxEventCounter' = auxEventCounter + 1
                                                                   /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]],
                                                                                                                status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)],
                                                                                                                auxNum |-> auxEventCounter']]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << controlMsgCounter, 
                                                                                   switchGeneratedEventSet, 
                                                                                   auxEventCounter, 
                                                                                   statusMsg >>
                                                        /\ UNCHANGED controller2Switch
                                                   ELSE /\ IF failedElem'[self] = "nicAsic"
                                                              THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                                                   /\ Assert(switchStatus[self[2]].nicAsic = NotFailed, 
                                                                             "Failure of assertion at line 646, column 9 of macro called at line 1499, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                   /\ swFailedNum' = [swFailedNum EXCEPT ![self[2]] = swFailedNum[self[2]] + 1]
                                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ auxEventCounter' = auxEventCounter + 1
                                                                   /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]],
                                                                                                                auxNum |-> auxEventCounter']]
                                                              ELSE /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 1500, column 14.")
                                                                   /\ UNCHANGED << controller2Switch, 
                                                                                   switchStatus, 
                                                                                   swFailedNum, 
                                                                                   controlMsgCounter, 
                                                                                   switchGeneratedEventSet, 
                                                                                   auxEventCounter, 
                                                                                   statusMsg >>
                                  /\ UNCHANGED << NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff >>
                       /\ IF shouldSendFailMsgToAll(statusMsg'[self])
                             THEN /\ prevLockHolder_' = [prevLockHolder_ EXCEPT ![self] = switchLock]
                                  /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                  /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                     \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                        /\ switchLock[2] = self[2]
                                  /\ switchLock' = self
                                  /\ controllerSet_' = [controllerSet_ EXCEPT ![self] = {ofc0, ofc1}]
                                  /\ pc' = [pc EXCEPT ![self] = "swFailureSendStatusMsg"]
                             ELSE /\ IF statusMsg'[self].type # 0
                                        THEN /\ Assert(FALSE, 
                                                       "Failure of assertion at line 1533, column 13.")
                                        ELSE /\ TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                                  /\ UNCHANGED << switchLock, controllerSet_, 
                                                  prevLockHolder_ >>
                       /\ UNCHANGED << controllerLocalLock, 
                                       controllerGlobalLock, FirstInstall, 
                                       ContProcSet, SwProcSet, 
                                       swSeqChangedStatus, switch2Controller, 
                                       installedIRs, installedBy, swNumEvent, 
                                       TCAM, switchControllerRoleStatus, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       irCounter, MAX_IR_COUNTER, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, workerLocalQueue, 
                                       ofcSwSuspensionStatus, processedEvents, 
                                       localEventLog, controllerRoleInSW, 
                                       nibEventQueue, roleUpdateStatus, 
                                       isOfcEnabled, setScheduledRoleUpdates, 
                                       ofcModuleTerminationStatus, 
                                       ofcModuleInitStatus, 
                                       setRecoveredSwWithSlaveRole, 
                                       fetchedIRsBeforePassingToWorker, 
                                       eventSkipList, masterState, 
                                       controllerStateNIB, IRStatus, 
                                       NIBSwSuspensionStatus, IRQueueNIB, 
                                       subscribeList, SetScheduledIRs, 
                                       ofcFailoverStateNIB, NIBEventLog, 
                                       ingressPkt, ingressIR, egressMsg, 
                                       ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, nxtController_, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, controllerSet_s, 
                                       nxtController_s, prevLockHolder, 
                                       eventMsg, controllerSet, nxtController, 
                                       eventID, toBeScheduledIRs, nextIR, 
                                       stepOfFailure_, subscriberOfcSet, ofcID, 
                                       event_, swSet, currSW, entry, index, 
                                       event, pulledNIBEventLog, 
                                       remainingEvents, receivedEventsCopy, 
                                       nextToSent, entryIndex, rowIndex, 
                                       rowRemove, removeRow, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure_co, notifOFC, 
                                       isEventProcessed, msg, stepOfFailure, 
                                       controllerFailedModules >>

swFailureSendStatusMsg(self) == /\ pc[self] = "swFailureSendStatusMsg"
                                /\ IF controllerSet_[self] # {}
                                      THEN /\ nxtController_' = [nxtController_ EXCEPT ![self] = CHOOSE x \in controllerSet_[self]: TRUE]
                                           /\ controllerSet_' = [controllerSet_ EXCEPT ![self] = controllerSet_[self] \ {nxtController_'[self]}]
                                           /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![nxtController_'[self]] = Append(swSeqChangedStatus[nxtController_'[self]], statusMsg[self])]
                                           /\ pc' = [pc EXCEPT ![self] = "swFailureSendStatusMsg"]
                                           /\ UNCHANGED << switchLock, 
                                                           statusMsg >>
                                      ELSE /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> 0]]
                                           /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                           /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                              \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                 /\ switchLock[2] = self[2]
                                           /\ switchLock' = prevLockHolder_[self]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                                           /\ UNCHANGED << swSeqChangedStatus, 
                                                           controllerSet_, 
                                                           nxtController_ >>
                                /\ UNCHANGED << controllerLocalLock, 
                                                controllerGlobalLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                installedBy, swFailedNum, 
                                                swNumEvent, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchControllerRoleStatus, 
                                                switchGeneratedEventSet, 
                                                auxEventCounter, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                ofcSwSuspensionStatus, 
                                                processedEvents, localEventLog, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                roleUpdateStatus, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                ofcModuleInitStatus, 
                                                setRecoveredSwWithSlaveRole, 
                                                fetchedIRsBeforePassingToWorker, 
                                                eventSkipList, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                NIBSwSuspensionStatus, 
                                                IRQueueNIB, subscribeList, 
                                                SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                NIBEventLog, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, notFailedSet, 
                                                failedElem, prevLockHolder_, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, controllerSet_s, 
                                                nxtController_s, 
                                                prevLockHolder, eventMsg, 
                                                controllerSet, nxtController, 
                                                eventID, toBeScheduledIRs, 
                                                nextIR, stepOfFailure_, 
                                                subscriberOfcSet, ofcID, 
                                                event_, swSet, currSW, entry, 
                                                index, event, 
                                                pulledNIBEventLog, 
                                                remainingEvents, 
                                                receivedEventsCopy, nextToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure_co, 
                                                notifOFC, isEventProcessed, 
                                                msg, stepOfFailure, 
                                                controllerFailedModules >>

swFailureProc(self) == SwitchFailure(self) \/ swFailureSendStatusMsg(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ Assert(statusResolveMsg[self].type = 0, 
                                        "Failure of assertion at line 1551, column 9.")
                              /\ failedSet' = [failedSet EXCEPT ![self] = returnSwitchFailedElements(self[2])]
                              /\ Cardinality(failedSet'[self]) > 0
                              /\ ~isFinished(self[2])
                              /\ /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ \E elem \in failedSet'[self]:
                                   recoveredElem' = [recoveredElem EXCEPT ![self] = elem]
                              /\ IF recoveredElem'[self] = "cpu"
                                    THEN /\ ofaStartingMode(self[2]) /\ installerInStartingMode(self[2])
                                         /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                   "Failure of assertion at line 740, column 9 of macro called at line 1562, column 39.")
                                         /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = NotFailed,
                                                                                 ![self[2]].ofa = NotFailed,
                                                                                 ![self[2]].installer = NotFailed]
                                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                         /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                               THEN /\ auxEventCounter' = auxEventCounter + 1
                                                    /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                    /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                    /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                               swID |-> self[2],
                                                                                                               num |-> controlMsgCounter'[self[2]],
                                                                                                               status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)],
                                                                                                               auxNum |-> auxEventCounter']]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << controlMsgCounter, 
                                                                    switchGeneratedEventSet, 
                                                                    auxEventCounter, 
                                                                    statusResolveMsg >>
                                         /\ UNCHANGED controller2Switch
                                    ELSE /\ IF recoveredElem'[self] = "nicAsic"
                                               THEN /\ nicAsicStartingMode(self[2])
                                                    /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                              "Failure of assertion at line 676, column 9 of macro called at line 1563, column 46.")
                                                    /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = NotFailed]
                                                    /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                    /\ IF switchStatus'[self[2]].ofa = Failed
                                                          THEN /\ auxEventCounter' = auxEventCounter + 1
                                                               /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                               /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                               /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> OFA_DOWN,
                                                                                                                          swID |-> self[2],
                                                                                                                          num |-> controlMsgCounter'[self[2]],
                                                                                                                          auxNum |-> auxEventCounter']]
                                                          ELSE /\ auxEventCounter' = auxEventCounter + 1
                                                               /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                               /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                               /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                                          swID |-> self[2],
                                                                                                                          num |-> controlMsgCounter'[self[2]],
                                                                                                                          status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)],
                                                                                                                          auxNum |-> auxEventCounter']]
                                               ELSE /\ IF recoveredElem'[self] = "ofa"
                                                          THEN /\ ofaStartingMode(self[2])
                                                               /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = Failed, 
                                                                         "Failure of assertion at line 794, column 9 of macro called at line 1564, column 42.")
                                                               /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = NotFailed]
                                                               /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                                     THEN /\ auxEventCounter' = auxEventCounter + 1
                                                                          /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                                          /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                          /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                                                     swID |-> self[2],
                                                                                                                                     num |-> controlMsgCounter'[self[2]],
                                                                                                                                     status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)],
                                                                                                                                     auxNum |-> auxEventCounter']]
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED << controlMsgCounter, 
                                                                                          switchGeneratedEventSet, 
                                                                                          auxEventCounter, 
                                                                                          statusResolveMsg >>
                                                          ELSE /\ IF recoveredElem'[self] = "installer"
                                                                     THEN /\ installerInStartingMode(self[2])
                                                                          /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = Failed, 
                                                                                    "Failure of assertion at line 845, column 9 of macro called at line 1565, column 48.")
                                                                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                               "Failure of assertion at line 848, column 13 of macro called at line 1565, column 48.")
                                                                                     /\ auxEventCounter' = auxEventCounter + 1
                                                                                     /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                                                                                     /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                                     /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                                                                swID |-> self[2],
                                                                                                                                                num |-> controlMsgCounter'[self[2]],
                                                                                                                                                status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)],
                                                                                                                                                auxNum |-> auxEventCounter']]
                                                                                ELSE /\ TRUE
                                                                                     /\ UNCHANGED << controlMsgCounter, 
                                                                                                     switchGeneratedEventSet, 
                                                                                                     auxEventCounter, 
                                                                                                     statusResolveMsg >>
                                                                     ELSE /\ Assert(FALSE, 
                                                                                    "Failure of assertion at line 1566, column 14.")
                                                                          /\ UNCHANGED << switchStatus, 
                                                                                          controlMsgCounter, 
                                                                                          switchGeneratedEventSet, 
                                                                                          auxEventCounter, 
                                                                                          statusResolveMsg >>
                                                    /\ UNCHANGED controller2Switch
                                         /\ UNCHANGED << NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Installer2OfaBuff, 
                                                         Ofa2InstallerBuff >>
                              /\ IF shouldSendRecoveryMsgToAll(statusResolveMsg'[self])
                                    THEN /\ prevLockHolder' = [prevLockHolder EXCEPT ![self] = switchLock]
                                         /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                         /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                               /\ switchLock[2] = self[2]
                                         /\ switchLock' = self
                                         /\ controllerSet_s' = [controllerSet_s EXCEPT ![self] = {ofc0, ofc1}]
                                         /\ pc' = [pc EXCEPT ![self] = "swRecoverySendStatusMsg"]
                                    ELSE /\ IF statusResolveMsg'[self].type # 0
                                               THEN /\ Assert(FALSE, 
                                                              "Failure of assertion at line 1597, column 13.")
                                               ELSE /\ TRUE
                                         /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                                         /\ UNCHANGED << switchLock, 
                                                         controllerSet_s, 
                                                         prevLockHolder >>
                              /\ UNCHANGED << controllerLocalLock, 
                                              controllerGlobalLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              swSeqChangedStatus, 
                                              switch2Controller, installedIRs, 
                                              installedBy, swFailedNum, 
                                              swNumEvent, TCAM, 
                                              switchControllerRoleStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, dependencyGraph, 
                                              IR2SW, irCounter, MAX_IR_COUNTER, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              workerLocalQueue, 
                                              ofcSwSuspensionStatus, 
                                              processedEvents, localEventLog, 
                                              controllerRoleInSW, 
                                              nibEventQueue, roleUpdateStatus, 
                                              isOfcEnabled, 
                                              setScheduledRoleUpdates, 
                                              ofcModuleTerminationStatus, 
                                              ofcModuleInitStatus, 
                                              setRecoveredSwWithSlaveRole, 
                                              fetchedIRsBeforePassingToWorker, 
                                              eventSkipList, masterState, 
                                              controllerStateNIB, IRStatus, 
                                              NIBSwSuspensionStatus, 
                                              IRQueueNIB, subscribeList, 
                                              SetScheduledIRs, 
                                              ofcFailoverStateNIB, NIBEventLog, 
                                              ingressPkt, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              controllerSet_, nxtController_, 
                                              prevLockHolder_, nxtController_s, 
                                              eventMsg, controllerSet, 
                                              nxtController, eventID, 
                                              toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, subscriberOfcSet, 
                                              ofcID, event_, swSet, currSW, 
                                              entry, index, event, 
                                              pulledNIBEventLog, 
                                              remainingEvents, 
                                              receivedEventsCopy, nextToSent, 
                                              entryIndex, rowIndex, rowRemove, 
                                              removeRow, stepOfFailure_c, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, stepOfFailure_co, 
                                              notifOFC, isEventProcessed, msg, 
                                              stepOfFailure, 
                                              controllerFailedModules >>

swRecoverySendStatusMsg(self) == /\ pc[self] = "swRecoverySendStatusMsg"
                                 /\ IF controllerSet_s[self] # {}
                                       THEN /\ nxtController_s' = [nxtController_s EXCEPT ![self] = CHOOSE x \in controllerSet_s[self]: TRUE]
                                            /\ controllerSet_s' = [controllerSet_s EXCEPT ![self] = controllerSet_s[self] \ {nxtController_s'[self]}]
                                            /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![nxtController_s'[self]] = Append(swSeqChangedStatus[nxtController_s'[self]], statusResolveMsg[self])]
                                            /\ pc' = [pc EXCEPT ![self] = "swRecoverySendStatusMsg"]
                                            /\ UNCHANGED << switchLock, 
                                                            statusResolveMsg >>
                                       ELSE /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> 0]]
                                            /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                            /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                               \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                                  /\ switchLock[2] = self[2]
                                            /\ switchLock' = prevLockHolder[self]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                                            /\ UNCHANGED << swSeqChangedStatus, 
                                                            controllerSet_s, 
                                                            nxtController_s >>
                                 /\ UNCHANGED << controllerLocalLock, 
                                                 controllerGlobalLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 installedBy, swFailedNum, 
                                                 swNumEvent, NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 switchControllerRoleStatus, 
                                                 switchGeneratedEventSet, 
                                                 auxEventCounter, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, 
                                                 dependencyGraph, IR2SW, 
                                                 irCounter, MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 workerLocalQueue, 
                                                 ofcSwSuspensionStatus, 
                                                 processedEvents, 
                                                 localEventLog, 
                                                 controllerRoleInSW, 
                                                 nibEventQueue, 
                                                 roleUpdateStatus, 
                                                 isOfcEnabled, 
                                                 setScheduledRoleUpdates, 
                                                 ofcModuleTerminationStatus, 
                                                 ofcModuleInitStatus, 
                                                 setRecoveredSwWithSlaveRole, 
                                                 fetchedIRsBeforePassingToWorker, 
                                                 eventSkipList, masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 NIBSwSuspensionStatus, 
                                                 IRQueueNIB, subscribeList, 
                                                 SetScheduledIRs, 
                                                 ofcFailoverStateNIB, 
                                                 NIBEventLog, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 controllerSet_, 
                                                 nxtController_, 
                                                 prevLockHolder_, failedSet, 
                                                 recoveredElem, prevLockHolder, 
                                                 eventMsg, controllerSet, 
                                                 nxtController, eventID, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, 
                                                 subscriberOfcSet, ofcID, 
                                                 event_, swSet, currSW, entry, 
                                                 index, event, 
                                                 pulledNIBEventLog, 
                                                 remainingEvents, 
                                                 receivedEventsCopy, 
                                                 nextToSent, entryIndex, 
                                                 rowIndex, rowRemove, 
                                                 removeRow, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure_co, notifOFC, 
                                                 isEventProcessed, msg, 
                                                 stepOfFailure, 
                                                 controllerFailedModules >>

swResolveFailure(self) == SwitchResolveFailure(self)
                             \/ swRecoverySendStatusMsg(self)

asyncNetEventGenProc(self) == /\ pc[self] = "asyncNetEventGenProc"
                              /\ swNumEvent[self[2]] < SW_MAX_NUM_EVENTS[self[2]]
                              /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                              /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                 \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                    /\ switchLock[2] = self[2]
                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                              /\ eventID' = [eventID EXCEPT ![self] = controlMsgCounter'[self[2]]]
                              /\ swNumEvent' = [swNumEvent EXCEPT ![self[2]] = swNumEvent[self[2]] + 1]
                              /\ auxEventCounter' = auxEventCounter + 1
                              /\ switchGeneratedEventSet' = [switchGeneratedEventSet EXCEPT ![self[2]] = switchGeneratedEventSet[self[2]] \cup {auxEventCounter'}]
                              /\ IF swOFACanProcessIRs(self[2])
                                    THEN /\ controllerSet' = [controllerSet EXCEPT ![self] = getNonSlaveController(self[2])]
                                         /\ pc' = [pc EXCEPT ![self] = "sendNetworkEvent"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "asyncNetEventGenProc"]
                                         /\ UNCHANGED controllerSet
                              /\ UNCHANGED << switchLock, controllerLocalLock, 
                                              controllerGlobalLock, 
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
                                              switchControllerRoleStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, dependencyGraph, 
                                              IR2SW, irCounter, MAX_IR_COUNTER, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              workerLocalQueue, 
                                              ofcSwSuspensionStatus, 
                                              processedEvents, localEventLog, 
                                              controllerRoleInSW, 
                                              nibEventQueue, roleUpdateStatus, 
                                              isOfcEnabled, 
                                              setScheduledRoleUpdates, 
                                              ofcModuleTerminationStatus, 
                                              ofcModuleInitStatus, 
                                              setRecoveredSwWithSlaveRole, 
                                              fetchedIRsBeforePassingToWorker, 
                                              eventSkipList, masterState, 
                                              controllerStateNIB, IRStatus, 
                                              NIBSwSuspensionStatus, 
                                              IRQueueNIB, subscribeList, 
                                              SetScheduledIRs, 
                                              ofcFailoverStateNIB, NIBEventLog, 
                                              ingressPkt, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              controllerSet_, nxtController_, 
                                              prevLockHolder_, failedSet, 
                                              statusResolveMsg, recoveredElem, 
                                              controllerSet_s, nxtController_s, 
                                              prevLockHolder, eventMsg, 
                                              nxtController, toBeScheduledIRs, 
                                              nextIR, stepOfFailure_, 
                                              subscriberOfcSet, ofcID, event_, 
                                              swSet, currSW, entry, index, 
                                              event, pulledNIBEventLog, 
                                              remainingEvents, 
                                              receivedEventsCopy, nextToSent, 
                                              entryIndex, rowIndex, rowRemove, 
                                              removeRow, stepOfFailure_c, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, stepOfFailure_co, 
                                              notifOFC, isEventProcessed, msg, 
                                              stepOfFailure, 
                                              controllerFailedModules >>

sendNetworkEvent(self) == /\ pc[self] = "sendNetworkEvent"
                          /\ IF swOFACanProcessIRs(self[2])
                                THEN /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                     /\ \/ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                        \/ /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                           /\ switchLock[2] = self[2]
                                     /\ switchLock' = self
                                     /\ nxtController' = [nxtController EXCEPT ![self] = CHOOSE x \in controllerSet[self]: TRUE]
                                     /\ controllerSet' = [controllerSet EXCEPT ![self] = controllerSet[self] \ {nxtController'[self]}]
                                     /\ eventMsg' = [eventMsg EXCEPT ![self] = [type |-> ASYNC_EVENT,
                                                                                from |-> self[2],
                                                                                to |-> nxtController'[self],
                                                                                num |-> eventID[self],
                                                                                auxNum |-> auxEventCounter]]
                                     /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], eventMsg'[self])]
                                     /\ IF controllerSet'[self] # {}
                                           THEN /\ pc' = [pc EXCEPT ![self] = "asyncNetEventGenProc"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "sendNetworkEvent"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "asyncNetEventGenProc"]
                                     /\ UNCHANGED << switchLock, 
                                                     Ofa2NicAsicBuff, eventMsg, 
                                                     controllerSet, 
                                                     nxtController >>
                          /\ UNCHANGED << controllerLocalLock, 
                                          controllerGlobalLock, FirstInstall, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          installedBy, swFailedNum, swNumEvent, 
                                          NicAsic2OfaBuff, Installer2OfaBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, 
                                          switchControllerRoleStatus, 
                                          switchGeneratedEventSet, 
                                          auxEventCounter, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, irCounter, MAX_IR_COUNTER, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          workerLocalQueue, 
                                          ofcSwSuspensionStatus, 
                                          processedEvents, localEventLog, 
                                          controllerRoleInSW, nibEventQueue, 
                                          roleUpdateStatus, isOfcEnabled, 
                                          setScheduledRoleUpdates, 
                                          ofcModuleTerminationStatus, 
                                          ofcModuleInitStatus, 
                                          setRecoveredSwWithSlaveRole, 
                                          fetchedIRsBeforePassingToWorker, 
                                          eventSkipList, masterState, 
                                          controllerStateNIB, IRStatus, 
                                          NIBSwSuspensionStatus, IRQueueNIB, 
                                          subscribeList, SetScheduledIRs, 
                                          ofcFailoverStateNIB, NIBEventLog, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, 
                                          controllerSet_, nxtController_, 
                                          prevLockHolder_, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          controllerSet_s, nxtController_s, 
                                          prevLockHolder, eventID, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, subscriberOfcSet, 
                                          ofcID, event_, swSet, currSW, entry, 
                                          index, event, pulledNIBEventLog, 
                                          remainingEvents, receivedEventsCopy, 
                                          nextToSent, entryIndex, rowIndex, 
                                          rowRemove, removeRow, 
                                          stepOfFailure_c, monitoringEvent, 
                                          setIRsToReset, resetIR, 
                                          stepOfFailure_co, notifOFC, 
                                          isEventProcessed, msg, stepOfFailure, 
                                          controllerFailedModules >>

asyncNetworkEventGenerator(self) == asyncNetEventGenProc(self)
                                       \/ sendNetworkEvent(self)

ghostProc(self) == /\ pc[self] = "ghostProc"
                   /\ /\ switchLock # <<NO_LOCK, NO_LOCK>>
                      /\ switchLock[2] = self[2]
                      /\ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
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
                                                          ELSE /\ IF switchLock[1] \in {SW_FAILURE_PROC}
                                                                     THEN /\ pc[<<SW_FAILURE_PROC, self[2]>>] = "SwitchFailure"
                                                                     ELSE /\ IF switchLock[1] \in {SW_RESOLVE_PROC}
                                                                                THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                                                                ELSE /\ TRUE
                   /\ Assert(\/ switchLock[2] = self[2]
                             \/ switchLock[2] = NO_LOCK, 
                             "Failure of assertion at line 962, column 9 of macro called at line 1673, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << controllerLocalLock, controllerGlobalLock, 
                                   FirstInstall, sw_fail_ordering_var, 
                                   ContProcSet, SwProcSet, swSeqChangedStatus, 
                                   controller2Switch, switch2Controller, 
                                   switchStatus, installedIRs, installedBy, 
                                   swFailedNum, swNumEvent, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   switchControllerRoleStatus, 
                                   switchGeneratedEventSet, auxEventCounter, 
                                   controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   dependencyGraph, IR2SW, irCounter, 
                                   MAX_IR_COUNTER, idThreadWorkingOnIR, 
                                   workerThreadRanking, workerLocalQueue, 
                                   ofcSwSuspensionStatus, processedEvents, 
                                   localEventLog, controllerRoleInSW, 
                                   nibEventQueue, roleUpdateStatus, 
                                   isOfcEnabled, setScheduledRoleUpdates, 
                                   ofcModuleTerminationStatus, 
                                   ofcModuleInitStatus, 
                                   setRecoveredSwWithSlaveRole, 
                                   fetchedIRsBeforePassingToWorker, 
                                   eventSkipList, masterState, 
                                   controllerStateNIB, IRStatus, 
                                   NIBSwSuspensionStatus, IRQueueNIB, 
                                   subscribeList, SetScheduledIRs, 
                                   ofcFailoverStateNIB, NIBEventLog, 
                                   ingressPkt, ingressIR, egressMsg, ofaInMsg, 
                                   ofaOutConfirmation, installerInIR, 
                                   statusMsg, notFailedSet, failedElem, 
                                   controllerSet_, nxtController_, 
                                   prevLockHolder_, failedSet, 
                                   statusResolveMsg, recoveredElem, 
                                   controllerSet_s, nxtController_s, 
                                   prevLockHolder, eventMsg, controllerSet, 
                                   nxtController, eventID, toBeScheduledIRs, 
                                   nextIR, stepOfFailure_, subscriberOfcSet, 
                                   ofcID, event_, swSet, currSW, entry, index, 
                                   event, pulledNIBEventLog, remainingEvents, 
                                   receivedEventsCopy, nextToSent, entryIndex, 
                                   rowIndex, rowRemove, removeRow, 
                                   stepOfFailure_c, monitoringEvent, 
                                   setIRsToReset, resetIR, stepOfFailure_co, 
                                   notifOFC, isEventProcessed, msg, 
                                   stepOfFailure, controllerFailedModules >>

ghostUnlockProcess(self) == ghostProc(self)

ControllerSeqProc(self) == /\ pc[self] = "ControllerSeqProc"
                           /\ controllerIsMaster(self[1])
                           /\ moduleIsUp(self)
                           /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1])]
                           /\ toBeScheduledIRs'[self] # {}
                           /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                              \/ controllerGlobalLock[1] = self[1]
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                              \/ controllerLocalLock[self[1]] = self
                           /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                           /\ UNCHANGED << switchLock, controllerLocalLock, 
                                           controllerGlobalLock, FirstInstall, 
                                           sw_fail_ordering_var, ContProcSet, 
                                           SwProcSet, swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, installedBy, 
                                           swFailedNum, swNumEvent, 
                                           NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                           Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           switchControllerRoleStatus, 
                                           switchGeneratedEventSet, 
                                           auxEventCounter, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           IR2SW, irCounter, MAX_IR_COUNTER, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, 
                                           workerLocalQueue, 
                                           ofcSwSuspensionStatus, 
                                           processedEvents, localEventLog, 
                                           controllerRoleInSW, nibEventQueue, 
                                           roleUpdateStatus, isOfcEnabled, 
                                           setScheduledRoleUpdates, 
                                           ofcModuleTerminationStatus, 
                                           ofcModuleInitStatus, 
                                           setRecoveredSwWithSlaveRole, 
                                           fetchedIRsBeforePassingToWorker, 
                                           eventSkipList, masterState, 
                                           controllerStateNIB, IRStatus, 
                                           NIBSwSuspensionStatus, IRQueueNIB, 
                                           subscribeList, SetScheduledIRs, 
                                           ofcFailoverStateNIB, NIBEventLog, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, 
                                           controllerSet_, nxtController_, 
                                           prevLockHolder_, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           controllerSet_s, nxtController_s, 
                                           prevLockHolder, eventMsg, 
                                           controllerSet, nxtController, 
                                           eventID, nextIR, stepOfFailure_, 
                                           subscriberOfcSet, ofcID, event_, 
                                           swSet, currSW, entry, index, event, 
                                           pulledNIBEventLog, remainingEvents, 
                                           receivedEventsCopy, nextToSent, 
                                           entryIndex, rowIndex, rowRemove, 
                                           removeRow, stepOfFailure_c, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure_co, notifOFC, 
                                           isEventProcessed, msg, 
                                           stepOfFailure, 
                                           controllerFailedModules >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                               \/ controllerGlobalLock[1] = self[1]
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                               \/ controllerLocalLock[self[1]] = self
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
                            /\ UNCHANGED << switchLock, controllerLocalLock, 
                                            controllerGlobalLock, FirstInstall, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, installedBy, 
                                            swFailedNum, swNumEvent, 
                                            NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                            Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            switchControllerRoleStatus, 
                                            switchGeneratedEventSet, 
                                            auxEventCounter, switchOrdering, 
                                            dependencyGraph, IR2SW, irCounter, 
                                            MAX_IR_COUNTER, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            workerLocalQueue, 
                                            ofcSwSuspensionStatus, 
                                            processedEvents, localEventLog, 
                                            controllerRoleInSW, nibEventQueue, 
                                            roleUpdateStatus, isOfcEnabled, 
                                            setScheduledRoleUpdates, 
                                            ofcModuleTerminationStatus, 
                                            ofcModuleInitStatus, 
                                            setRecoveredSwWithSlaveRole, 
                                            fetchedIRsBeforePassingToWorker, 
                                            eventSkipList, masterState, 
                                            IRStatus, NIBSwSuspensionStatus, 
                                            IRQueueNIB, subscribeList, 
                                            ofcFailoverStateNIB, NIBEventLog, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            controllerSet_, nxtController_, 
                                            prevLockHolder_, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            controllerSet_s, nxtController_s, 
                                            prevLockHolder, eventMsg, 
                                            controllerSet, nxtController, 
                                            eventID, toBeScheduledIRs, 
                                            subscriberOfcSet, ofcID, event_, 
                                            swSet, currSW, entry, index, event, 
                                            pulledNIBEventLog, remainingEvents, 
                                            receivedEventsCopy, nextToSent, 
                                            entryIndex, rowIndex, rowRemove, 
                                            removeRow, stepOfFailure_c, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure_co, 
                                            notifOFC, isEventProcessed, msg, 
                                            stepOfFailure, 
                                            controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                          \/ controllerGlobalLock[1] = self[1]
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ controllerGlobalLock' = self
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
                       /\ UNCHANGED << switchLock, controllerLocalLock, 
                                       FirstInstall, sw_fail_ordering_var, 
                                       ContProcSet, SwProcSet, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, switchStatus, 
                                       installedIRs, installedBy, swFailedNum, 
                                       swNumEvent, NicAsic2OfaBuff, 
                                       Ofa2NicAsicBuff, Installer2OfaBuff, 
                                       Ofa2InstallerBuff, TCAM, 
                                       controlMsgCounter, 
                                       switchControllerRoleStatus, 
                                       switchGeneratedEventSet, 
                                       auxEventCounter, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       irCounter, MAX_IR_COUNTER, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, workerLocalQueue, 
                                       ofcSwSuspensionStatus, processedEvents, 
                                       localEventLog, controllerRoleInSW, 
                                       nibEventQueue, roleUpdateStatus, 
                                       isOfcEnabled, setScheduledRoleUpdates, 
                                       ofcModuleTerminationStatus, 
                                       ofcModuleInitStatus, 
                                       setRecoveredSwWithSlaveRole, 
                                       fetchedIRsBeforePassingToWorker, 
                                       eventSkipList, masterState, 
                                       controllerStateNIB, IRStatus, 
                                       NIBSwSuspensionStatus, subscribeList, 
                                       SetScheduledIRs, ofcFailoverStateNIB, 
                                       NIBEventLog, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, controllerSet_, 
                                       nxtController_, prevLockHolder_, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, controllerSet_s, 
                                       nxtController_s, prevLockHolder, 
                                       eventMsg, controllerSet, nxtController, 
                                       eventID, toBeScheduledIRs, nextIR, 
                                       ofcID, event_, swSet, currSW, entry, 
                                       index, event, pulledNIBEventLog, 
                                       remainingEvents, receivedEventsCopy, 
                                       nextToSent, entryIndex, rowIndex, 
                                       rowRemove, removeRow, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure_co, notifOFC, 
                                       isEventProcessed, msg, stepOfFailure, 
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
                                    /\ UNCHANGED << switchLock, 
                                                    controllerLocalLock, 
                                                    controllerGlobalLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    installedBy, swFailedNum, 
                                                    swNumEvent, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    switchGeneratedEventSet, 
                                                    auxEventCounter, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    workerLocalQueue, 
                                                    ofcSwSuspensionStatus, 
                                                    processedEvents, 
                                                    localEventLog, 
                                                    controllerRoleInSW, 
                                                    roleUpdateStatus, 
                                                    isOfcEnabled, 
                                                    setScheduledRoleUpdates, 
                                                    ofcModuleTerminationStatus, 
                                                    ofcModuleInitStatus, 
                                                    setRecoveredSwWithSlaveRole, 
                                                    fetchedIRsBeforePassingToWorker, 
                                                    eventSkipList, masterState, 
                                                    IRStatus, 
                                                    NIBSwSuspensionStatus, 
                                                    IRQueueNIB, subscribeList, 
                                                    SetScheduledIRs, 
                                                    ofcFailoverStateNIB, 
                                                    NIBEventLog, ingressPkt, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    controllerSet_, 
                                                    nxtController_, 
                                                    prevLockHolder_, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    controllerSet_s, 
                                                    nxtController_s, 
                                                    prevLockHolder, eventMsg, 
                                                    controllerSet, 
                                                    nxtController, eventID, 
                                                    nextIR, stepOfFailure_, 
                                                    event_, swSet, currSW, 
                                                    entry, index, event, 
                                                    pulledNIBEventLog, 
                                                    remainingEvents, 
                                                    receivedEventsCopy, 
                                                    nextToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    removeRow, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure_co, notifOFC, 
                                                    isEventProcessed, msg, 
                                                    stepOfFailure, 
                                                    controllerFailedModules >>

sequencerApplyFailure(self) == /\ pc[self] = "sequencerApplyFailure"
                               /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                  \/ controllerGlobalLock[1] = self[1]
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                               /\ IF (stepOfFailure_[self] # 0)
                                     THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                          /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerSeqStateReconciliation"]
                                     ELSE /\ IF toBeScheduledIRs[self] = {}
                                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSeqProc"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                          /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat >>
                               /\ UNCHANGED << switchLock, controllerLocalLock, 
                                               FirstInstall, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, installedBy, 
                                               swFailedNum, swNumEvent, 
                                               NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               switchControllerRoleStatus, 
                                               switchGeneratedEventSet, 
                                               auxEventCounter, switchOrdering, 
                                               dependencyGraph, IR2SW, 
                                               irCounter, MAX_IR_COUNTER, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               workerLocalQueue, 
                                               ofcSwSuspensionStatus, 
                                               processedEvents, localEventLog, 
                                               controllerRoleInSW, 
                                               nibEventQueue, roleUpdateStatus, 
                                               isOfcEnabled, 
                                               setScheduledRoleUpdates, 
                                               ofcModuleTerminationStatus, 
                                               ofcModuleInitStatus, 
                                               setRecoveredSwWithSlaveRole, 
                                               fetchedIRsBeforePassingToWorker, 
                                               eventSkipList, masterState, 
                                               controllerStateNIB, IRStatus, 
                                               NIBSwSuspensionStatus, 
                                               IRQueueNIB, subscribeList, 
                                               SetScheduledIRs, 
                                               ofcFailoverStateNIB, 
                                               NIBEventLog, ingressPkt, 
                                               ingressIR, egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               controllerSet_, nxtController_, 
                                               prevLockHolder_, failedSet, 
                                               statusResolveMsg, recoveredElem, 
                                               controllerSet_s, 
                                               nxtController_s, prevLockHolder, 
                                               eventMsg, controllerSet, 
                                               nxtController, eventID, 
                                               toBeScheduledIRs, nextIR, 
                                               stepOfFailure_, 
                                               subscriberOfcSet, ofcID, event_, 
                                               swSet, currSW, entry, index, 
                                               event, pulledNIBEventLog, 
                                               remainingEvents, 
                                               receivedEventsCopy, nextToSent, 
                                               entryIndex, rowIndex, rowRemove, 
                                               removeRow, stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure_co, 
                                               notifOFC, isEventProcessed, msg, 
                                               stepOfFailure, 
                                               controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ controllerIsMaster(self[1])
                                          /\ moduleIsUp(self)
                                          /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                             \/ controllerGlobalLock[1] = self[1]
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ \/ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                             \/ controllerGlobalLock'[1] = self[1]
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                             \/ controllerLocalLock[self[1]] = self
                                          /\ controllerLocalLock' = [controllerLocalLock EXCEPT ![self[1]] = <<NO_LOCK, NO_LOCK>>]
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
                                                          swNumEvent, 
                                                          NicAsic2OfaBuff, 
                                                          Ofa2NicAsicBuff, 
                                                          Installer2OfaBuff, 
                                                          Ofa2InstallerBuff, 
                                                          TCAM, 
                                                          controlMsgCounter, 
                                                          switchControllerRoleStatus, 
                                                          switchGeneratedEventSet, 
                                                          auxEventCounter, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          dependencyGraph, 
                                                          IR2SW, irCounter, 
                                                          MAX_IR_COUNTER, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          workerLocalQueue, 
                                                          ofcSwSuspensionStatus, 
                                                          processedEvents, 
                                                          localEventLog, 
                                                          controllerRoleInSW, 
                                                          nibEventQueue, 
                                                          roleUpdateStatus, 
                                                          isOfcEnabled, 
                                                          setScheduledRoleUpdates, 
                                                          ofcModuleTerminationStatus, 
                                                          ofcModuleInitStatus, 
                                                          setRecoveredSwWithSlaveRole, 
                                                          fetchedIRsBeforePassingToWorker, 
                                                          eventSkipList, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          NIBSwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          subscribeList, 
                                                          ofcFailoverStateNIB, 
                                                          NIBEventLog, 
                                                          ingressPkt, 
                                                          ingressIR, egressMsg, 
                                                          ofaInMsg, 
                                                          ofaOutConfirmation, 
                                                          installerInIR, 
                                                          statusMsg, 
                                                          notFailedSet, 
                                                          failedElem, 
                                                          controllerSet_, 
                                                          nxtController_, 
                                                          prevLockHolder_, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, 
                                                          controllerSet_s, 
                                                          nxtController_s, 
                                                          prevLockHolder, 
                                                          eventMsg, 
                                                          controllerSet, 
                                                          nxtController, 
                                                          eventID, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          subscriberOfcSet, 
                                                          ofcID, event_, swSet, 
                                                          currSW, entry, index, 
                                                          event, 
                                                          pulledNIBEventLog, 
                                                          remainingEvents, 
                                                          receivedEventsCopy, 
                                                          nextToSent, 
                                                          entryIndex, rowIndex, 
                                                          rowRemove, removeRow, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure_co, 
                                                          notifOFC, 
                                                          isEventProcessed, 
                                                          msg, stepOfFailure, 
                                                          controllerFailedModules >>

controllerSequencer(self) == ControllerSeqProc(self)
                                \/ SchedulerMechanism(self)
                                \/ ScheduleTheIR(self)
                                \/ sendIRQueueModNotification(self)
                                \/ sequencerApplyFailure(self)
                                \/ ControllerSeqStateReconciliation(self)

NibEventHandlerProc(self) == /\ pc[self] = "NibEventHandlerProc"
                             /\ nibEventQueue[self[1]] # <<>>
                             /\ event_' = [event_ EXCEPT ![self] = Head((nibEventQueue[self[1]]))]
                             /\ Assert(event_'[self].type \in {INSTALL_FLOW, TOPO_MOD}, 
                                       "Failure of assertion at line 1806, column 13.")
                             /\ IF event_'[self].type = TOPO_MOD /\ masterState[self[1]] = ROLE_SLAVE
                                   THEN /\ IF ofcSwSuspensionStatus[self[1]][event_'[self].sw] = SW_RUN /\ event_'[self].status = SW_SUSPEND
                                              THEN /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]][event_'[self].sw] = SW_SUSPEND]
                                                   /\ UNCHANGED setRecoveredSwWithSlaveRole
                                              ELSE /\ IF ofcSwSuspensionStatus[self[1]][event_'[self].sw] = SW_SUSPEND /\ event_'[self].status = SW_RUN
                                                         THEN /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]][event_'[self].sw] = SW_RUN]
                                                              /\ IF controllerRoleInSW[self[1]][event_'[self].sw] = ROLE_SLAVE /\ ofcFailoverStateNIB[self[1]] = FAILOVER_INIT
                                                                    THEN /\ setRecoveredSwWithSlaveRole' = [setRecoveredSwWithSlaveRole EXCEPT ![self[1]] = setRecoveredSwWithSlaveRole[self[1]] \cup {event_'[self].sw}]
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED setRecoveredSwWithSlaveRole
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << ofcSwSuspensionStatus, 
                                                                              setRecoveredSwWithSlaveRole >>
                                        /\ UNCHANGED << workerLocalQueue, 
                                                        fetchedIRsBeforePassingToWorker >>
                                   ELSE /\ IF event_'[self].type = INSTALL_FLOW
                                              THEN /\ IF masterState[self[1]] = ROLE_MASTER
                                                         THEN /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> event_'[self], id |-> -1, tag |-> NO_TAG])]
                                                              /\ UNCHANGED fetchedIRsBeforePassingToWorker
                                                         ELSE /\ fetchedIRsBeforePassingToWorker' = [fetchedIRsBeforePassingToWorker EXCEPT ![self[1]] = Append(fetchedIRsBeforePassingToWorker[self[1]], event_'[self])]
                                                              /\ UNCHANGED workerLocalQueue
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED << workerLocalQueue, 
                                                                   fetchedIRsBeforePassingToWorker >>
                                        /\ UNCHANGED << ofcSwSuspensionStatus, 
                                                        setRecoveredSwWithSlaveRole >>
                             /\ nibEventQueue' = [nibEventQueue EXCEPT ![self[1]] = Tail((nibEventQueue[self[1]]))]
                             /\ pc' = [pc EXCEPT ![self] = "NibEventHandlerProc"]
                             /\ UNCHANGED << switchLock, controllerLocalLock, 
                                             controllerGlobalLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, swNumEvent, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             switchGeneratedEventSet, 
                                             auxEventCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             processedEvents, localEventLog, 
                                             controllerRoleInSW, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             ofcModuleInitStatus, 
                                             eventSkipList, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             NIBSwSuspensionStatus, IRQueueNIB, 
                                             subscribeList, SetScheduledIRs, 
                                             ofcFailoverStateNIB, NIBEventLog, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             controllerSet_, nxtController_, 
                                             prevLockHolder_, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             controllerSet_s, nxtController_s, 
                                             prevLockHolder, eventMsg, 
                                             controllerSet, nxtController, 
                                             eventID, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, swSet, currSW, entry, 
                                             index, event, pulledNIBEventLog, 
                                             remainingEvents, 
                                             receivedEventsCopy, nextToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             removeRow, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure_co, 
                                             notifOFC, isEventProcessed, msg, 
                                             stepOfFailure, 
                                             controllerFailedModules >>

nibEventHandler(self) == NibEventHandlerProc(self)

ofcFailoverHandlerProc(self) == /\ pc[self] = "ofcFailoverHandlerProc"
                                /\ \/ ofcFailoverStateNIB[self[1]] \in {FAILOVER_INIT, FAILOVER_TERMINATE}
                                   \/ /\ masterState[self[1]] = ROLE_MASTER
                                      /\ getSetSwitchInNonMasterRole(self[1]) # {}
                                /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                   \/ controllerGlobalLock[1] = self[1]
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                   \/ controllerLocalLock[self[1]] = self
                                /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                   \/ controllerGlobalLock[1] = self[1]
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                /\ IF ofcFailoverStateNIB[self[1]] = FAILOVER_INIT
                                      THEN /\ isOfcEnabled' = [isOfcEnabled EXCEPT ![self[1]] = TRUE]
                                           /\ swSet' = [swSet EXCEPT ![self] = getSetSwitchInSlaveRole(self[1])]
                                           /\ subscribeList' = [subscribeList EXCEPT !.SwSuspensionStatus = subscribeList.SwSuspensionStatus \cup {self[1]}]
                                           /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]] = NIBSwSuspensionStatus]
                                           /\ pc' = [pc EXCEPT ![self] = "ScheduleRoleUpdateEqual"]
                                           /\ UNCHANGED << workerLocalQueue, 
                                                           roleUpdateStatus, 
                                                           setScheduledRoleUpdates, 
                                                           ofcModuleTerminationStatus, 
                                                           currSW >>
                                      ELSE /\ IF ofcFailoverStateNIB[self[1]] = FAILOVER_TERMINATE
                                                 THEN /\ subscribeList' = [subscribeList EXCEPT !.IRQueueNIB = subscribeList.IRQueueNIB \ {self[1]},
                                                                                                !.SwSuspensionStatus = subscribeList.SwSuspensionStatus \ {self[1]}]
                                                      /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]] = [y \in CONTROLLER_THREAD_POOL |-> TERMINATE_INIT]
                                                                                                                                                          @@ ofcModuleTerminationStatus[self[1]]]
                                                      /\ pc' = [pc EXCEPT ![self] = "WaitForWorkersTermination"]
                                                      /\ UNCHANGED << workerLocalQueue, 
                                                                      roleUpdateStatus, 
                                                                      setScheduledRoleUpdates, 
                                                                      currSW >>
                                                 ELSE /\ currSW' = [currSW EXCEPT ![self] = CHOOSE x \in getSetSwitchInNonMasterRole(self[1]): TRUE]
                                                      /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][currSW'[self]] = [roletype |-> ROLE_MASTER, status |-> IR_NONE]]
                                                      /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> ([type |-> ROLE_REQ, roletype |-> ROLE_MASTER, to |-> currSW'[self]]), id |-> -1, tag |-> NO_TAG])]
                                                      /\ setScheduledRoleUpdates' = [setScheduledRoleUpdates EXCEPT ![self[1]] = setScheduledRoleUpdates[self[1]] \cup {currSW'[self]}]
                                                      /\ pc' = [pc EXCEPT ![self] = "ofcFailoverHandlerProc"]
                                                      /\ UNCHANGED << ofcModuleTerminationStatus, 
                                                                      subscribeList >>
                                           /\ UNCHANGED << ofcSwSuspensionStatus, 
                                                           isOfcEnabled, swSet >>
                                /\ UNCHANGED << switchLock, 
                                                controllerLocalLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                installedBy, swFailedNum, 
                                                swNumEvent, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchControllerRoleStatus, 
                                                switchGeneratedEventSet, 
                                                auxEventCounter, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                processedEvents, localEventLog, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                ofcModuleInitStatus, 
                                                setRecoveredSwWithSlaveRole, 
                                                fetchedIRsBeforePassingToWorker, 
                                                eventSkipList, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                NIBSwSuspensionStatus, 
                                                IRQueueNIB, SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                NIBEventLog, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                controllerSet_, nxtController_, 
                                                prevLockHolder_, failedSet, 
                                                statusResolveMsg, 
                                                recoveredElem, controllerSet_s, 
                                                nxtController_s, 
                                                prevLockHolder, eventMsg, 
                                                controllerSet, nxtController, 
                                                eventID, toBeScheduledIRs, 
                                                nextIR, stepOfFailure_, 
                                                subscriberOfcSet, ofcID, 
                                                event_, entry, index, event, 
                                                pulledNIBEventLog, 
                                                remainingEvents, 
                                                receivedEventsCopy, nextToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure_co, 
                                                notifOFC, isEventProcessed, 
                                                msg, stepOfFailure, 
                                                controllerFailedModules >>

ScheduleRoleUpdateEqual(self) == /\ pc[self] = "ScheduleRoleUpdateEqual"
                                 /\ IF swSet[self] # {}
                                       THEN /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerGlobalLock[1] = self[1]
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerLocalLock[self[1]] = self
                                            /\ controllerLocalLock' = [controllerLocalLock EXCEPT ![self[1]] = self]
                                            /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerGlobalLock[1] = self[1]
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ controllerGlobalLock' = self
                                            /\ currSW' = [currSW EXCEPT ![self] = CHOOSE x \in swSet[self]: TRUE]
                                            /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][currSW'[self]] = [roletype |-> ROLE_EQUAL, status |-> IR_NONE]]
                                            /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> ([type |-> ROLE_REQ, roletype |-> ROLE_EQUAL, to |-> currSW'[self]]), id |-> -1, tag |-> NO_TAG])]
                                            /\ setScheduledRoleUpdates' = [setScheduledRoleUpdates EXCEPT ![self[1]] = setScheduledRoleUpdates[self[1]] \cup {currSW'[self]}]
                                            /\ swSet' = [swSet EXCEPT ![self] = swSet[self] \ {currSW'[self]}]
                                            /\ pc' = [pc EXCEPT ![self] = "ScheduleRoleUpdateEqual"]
                                       ELSE /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerGlobalLock[1] = self[1]
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerLocalLock[self[1]] = self
                                            /\ controllerLocalLock' = [controllerLocalLock EXCEPT ![self[1]] = <<NO_LOCK, NO_LOCK>>]
                                            /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerGlobalLock[1] = self[1]
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ pc' = [pc EXCEPT ![self] = "WaitForSwitchUpdateRoleACK"]
                                            /\ UNCHANGED << workerLocalQueue, 
                                                            roleUpdateStatus, 
                                                            setScheduledRoleUpdates, 
                                                            swSet, currSW >>
                                 /\ UNCHANGED << switchLock, FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 installedBy, swFailedNum, 
                                                 swNumEvent, NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 switchControllerRoleStatus, 
                                                 switchGeneratedEventSet, 
                                                 auxEventCounter, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, 
                                                 dependencyGraph, IR2SW, 
                                                 irCounter, MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 ofcSwSuspensionStatus, 
                                                 processedEvents, 
                                                 localEventLog, 
                                                 controllerRoleInSW, 
                                                 nibEventQueue, isOfcEnabled, 
                                                 ofcModuleTerminationStatus, 
                                                 ofcModuleInitStatus, 
                                                 setRecoveredSwWithSlaveRole, 
                                                 fetchedIRsBeforePassingToWorker, 
                                                 eventSkipList, masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 NIBSwSuspensionStatus, 
                                                 IRQueueNIB, subscribeList, 
                                                 SetScheduledIRs, 
                                                 ofcFailoverStateNIB, 
                                                 NIBEventLog, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 controllerSet_, 
                                                 nxtController_, 
                                                 prevLockHolder_, failedSet, 
                                                 statusResolveMsg, 
                                                 recoveredElem, 
                                                 controllerSet_s, 
                                                 nxtController_s, 
                                                 prevLockHolder, eventMsg, 
                                                 controllerSet, nxtController, 
                                                 eventID, toBeScheduledIRs, 
                                                 nextIR, stepOfFailure_, 
                                                 subscriberOfcSet, ofcID, 
                                                 event_, entry, index, event, 
                                                 pulledNIBEventLog, 
                                                 remainingEvents, 
                                                 receivedEventsCopy, 
                                                 nextToSent, entryIndex, 
                                                 rowIndex, rowRemove, 
                                                 removeRow, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure_co, notifOFC, 
                                                 isEventProcessed, msg, 
                                                 stepOfFailure, 
                                                 controllerFailedModules >>

WaitForSwitchUpdateRoleACK(self) == /\ pc[self] = "WaitForSwitchUpdateRoleACK"
                                    /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerGlobalLock[1] = self[1]
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerLocalLock[self[1]] = self
                                    /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerGlobalLock[1] = self[1]
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                    /\ \/ allSwitchesEitherEqualRoleOrSuspended(self[1])
                                       \/ existRecoveredSwitchWithSlaveRole(self[1])
                                    /\ IF existRecoveredSwitchWithSlaveRole(self[1])
                                          THEN /\ currSW' = [currSW EXCEPT ![self] = CHOOSE x \in setRecoveredSwWithSlaveRole[self[1]]: TRUE]
                                               /\ IF controllerRoleInSW[self[1]][currSW'[self]] = ROLE_SLAVE
                                                     THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][currSW'[self]] = [roletype |-> ROLE_EQUAL, status |-> IR_NONE]]
                                                          /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> ([type |-> ROLE_REQ, roletype |-> ROLE_EQUAL, to |-> currSW'[self]]), id |-> -1, tag |-> NO_TAG])]
                                                          /\ setScheduledRoleUpdates' = [setScheduledRoleUpdates EXCEPT ![self[1]] = setScheduledRoleUpdates[self[1]] \cup {currSW'[self]}]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED << workerLocalQueue, 
                                                                          roleUpdateStatus, 
                                                                          setScheduledRoleUpdates >>
                                               /\ setRecoveredSwWithSlaveRole' = [setRecoveredSwWithSlaveRole EXCEPT ![self[1]] = setRecoveredSwWithSlaveRole[self[1]] \ {currSW'[self]}]
                                               /\ pc' = [pc EXCEPT ![self] = "WaitForSwitchUpdateRoleACK"]
                                               /\ UNCHANGED << fetchedIRsBeforePassingToWorker, 
                                                               subscribeList, 
                                                               ofcFailoverStateNIB >>
                                          ELSE /\ subscribeList' = [subscribeList EXCEPT !.IRQueueNIB = subscribeList.IRQueueNIB \cup {self[1]}]
                                               /\ fetchedIRsBeforePassingToWorker' = [fetchedIRsBeforePassingToWorker EXCEPT ![self[1]] = fetchedIRsBeforePassingToWorker[self[1]] \o IRQueueNIB]
                                               /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![self[1]] = FAILOVER_READY]
                                               /\ pc' = [pc EXCEPT ![self] = "QueryIRQueueNIB"]
                                               /\ UNCHANGED << workerLocalQueue, 
                                                               roleUpdateStatus, 
                                                               setScheduledRoleUpdates, 
                                                               setRecoveredSwWithSlaveRole, 
                                                               currSW >>
                                    /\ UNCHANGED << switchLock, 
                                                    controllerLocalLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    installedBy, swFailedNum, 
                                                    swNumEvent, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    switchGeneratedEventSet, 
                                                    auxEventCounter, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    ofcSwSuspensionStatus, 
                                                    processedEvents, 
                                                    localEventLog, 
                                                    controllerRoleInSW, 
                                                    nibEventQueue, 
                                                    isOfcEnabled, 
                                                    ofcModuleTerminationStatus, 
                                                    ofcModuleInitStatus, 
                                                    eventSkipList, masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    NIBSwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    NIBEventLog, ingressPkt, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    controllerSet_, 
                                                    nxtController_, 
                                                    prevLockHolder_, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    controllerSet_s, 
                                                    nxtController_s, 
                                                    prevLockHolder, eventMsg, 
                                                    controllerSet, 
                                                    nxtController, eventID, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    subscriberOfcSet, ofcID, 
                                                    event_, swSet, entry, 
                                                    index, event, 
                                                    pulledNIBEventLog, 
                                                    remainingEvents, 
                                                    receivedEventsCopy, 
                                                    nextToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    removeRow, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure_co, notifOFC, 
                                                    isEventProcessed, msg, 
                                                    stepOfFailure, 
                                                    controllerFailedModules >>

QueryIRQueueNIB(self) == /\ pc[self] = "QueryIRQueueNIB"
                         /\ IF fetchedIRsBeforePassingToWorker[self[1]] # <<>>
                               THEN /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerGlobalLock[1] = self[1]
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerLocalLock[self[1]] = self
                                    /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerGlobalLock[1] = self[1]
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                    /\ masterState[self[1]] = ROLE_MASTER
                                    /\ entry' = [entry EXCEPT ![self] = Head(fetchedIRsBeforePassingToWorker[self[1]])]
                                    /\ fetchedIRsBeforePassingToWorker' = [fetchedIRsBeforePassingToWorker EXCEPT ![self[1]] = Tail(fetchedIRsBeforePassingToWorker[self[1]])]
                                    /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> entry'[self], id |-> -1, tag |-> NO_TAG])]
                                    /\ pc' = [pc EXCEPT ![self] = "QueryIRQueueNIB"]
                                    /\ UNCHANGED ofcModuleInitStatus
                               ELSE /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerGlobalLock[1] = self[1]
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerLocalLock[self[1]] = self
                                    /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                       \/ controllerGlobalLock[1] = self[1]
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                    /\ masterState[self[1]] = ROLE_MASTER
                                    /\ pc[<<self[1], CONT_EVENT>>] = "ControllerEventHandlerProc"
                                    /\ ofcModuleInitStatus' = [ofcModuleInitStatus EXCEPT ![self[1]][CONT_EVENT] = INIT_NONE]
                                    /\ pc' = [pc EXCEPT ![self] = "EventHandlerInitStateForReconciliation"]
                                    /\ UNCHANGED << workerLocalQueue, 
                                                    fetchedIRsBeforePassingToWorker, 
                                                    entry >>
                         /\ UNCHANGED << switchLock, controllerLocalLock, 
                                         FirstInstall, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, installedBy, 
                                         swFailedNum, swNumEvent, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         switchControllerRoleStatus, 
                                         switchGeneratedEventSet, 
                                         auxEventCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         ofcSwSuspensionStatus, 
                                         processedEvents, localEventLog, 
                                         controllerRoleInSW, nibEventQueue, 
                                         roleUpdateStatus, isOfcEnabled, 
                                         setScheduledRoleUpdates, 
                                         ofcModuleTerminationStatus, 
                                         setRecoveredSwWithSlaveRole, 
                                         eventSkipList, masterState, 
                                         controllerStateNIB, IRStatus, 
                                         NIBSwSuspensionStatus, IRQueueNIB, 
                                         subscribeList, SetScheduledIRs, 
                                         ofcFailoverStateNIB, NIBEventLog, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, 
                                         controllerSet_, nxtController_, 
                                         prevLockHolder_, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         controllerSet_s, nxtController_s, 
                                         prevLockHolder, eventMsg, 
                                         controllerSet, nxtController, eventID, 
                                         toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, subscriberOfcSet, 
                                         ofcID, event_, swSet, currSW, index, 
                                         event, pulledNIBEventLog, 
                                         remainingEvents, receivedEventsCopy, 
                                         nextToSent, entryIndex, rowIndex, 
                                         rowRemove, removeRow, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure_co, notifOFC, 
                                         isEventProcessed, msg, stepOfFailure, 
                                         controllerFailedModules >>

EventHandlerInitStateForReconciliation(self) == /\ pc[self] = "EventHandlerInitStateForReconciliation"
                                                /\ pulledNIBEventLog' = [pulledNIBEventLog EXCEPT ![self] = NIBEventLog]
                                                /\ receivedEventsCopy' = [receivedEventsCopy EXCEPT ![self] = localEventLog[self[1]]]
                                                /\ swSet' = [swSet EXCEPT ![self] = SW]
                                                /\ pc' = [pc EXCEPT ![self] = "ReconcileEventLogs"]
                                                /\ UNCHANGED << switchLock, 
                                                                controllerLocalLock, 
                                                                controllerGlobalLock, 
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
                                                                swNumEvent, 
                                                                NicAsic2OfaBuff, 
                                                                Ofa2NicAsicBuff, 
                                                                Installer2OfaBuff, 
                                                                Ofa2InstallerBuff, 
                                                                TCAM, 
                                                                controlMsgCounter, 
                                                                switchControllerRoleStatus, 
                                                                switchGeneratedEventSet, 
                                                                auxEventCounter, 
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
                                                                ofcSwSuspensionStatus, 
                                                                processedEvents, 
                                                                localEventLog, 
                                                                controllerRoleInSW, 
                                                                nibEventQueue, 
                                                                roleUpdateStatus, 
                                                                isOfcEnabled, 
                                                                setScheduledRoleUpdates, 
                                                                ofcModuleTerminationStatus, 
                                                                ofcModuleInitStatus, 
                                                                setRecoveredSwWithSlaveRole, 
                                                                fetchedIRsBeforePassingToWorker, 
                                                                eventSkipList, 
                                                                masterState, 
                                                                controllerStateNIB, 
                                                                IRStatus, 
                                                                NIBSwSuspensionStatus, 
                                                                IRQueueNIB, 
                                                                subscribeList, 
                                                                SetScheduledIRs, 
                                                                ofcFailoverStateNIB, 
                                                                NIBEventLog, 
                                                                ingressPkt, 
                                                                ingressIR, 
                                                                egressMsg, 
                                                                ofaInMsg, 
                                                                ofaOutConfirmation, 
                                                                installerInIR, 
                                                                statusMsg, 
                                                                notFailedSet, 
                                                                failedElem, 
                                                                controllerSet_, 
                                                                nxtController_, 
                                                                prevLockHolder_, 
                                                                failedSet, 
                                                                statusResolveMsg, 
                                                                recoveredElem, 
                                                                controllerSet_s, 
                                                                nxtController_s, 
                                                                prevLockHolder, 
                                                                eventMsg, 
                                                                controllerSet, 
                                                                nxtController, 
                                                                eventID, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                stepOfFailure_, 
                                                                subscriberOfcSet, 
                                                                ofcID, event_, 
                                                                currSW, entry, 
                                                                index, event, 
                                                                remainingEvents, 
                                                                nextToSent, 
                                                                entryIndex, 
                                                                rowIndex, 
                                                                rowRemove, 
                                                                removeRow, 
                                                                stepOfFailure_c, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, 
                                                                stepOfFailure_co, 
                                                                notifOFC, 
                                                                isEventProcessed, 
                                                                msg, 
                                                                stepOfFailure, 
                                                                controllerFailedModules >>

ReconcileEventLogs(self) == /\ pc[self] = "ReconcileEventLogs"
                            /\ IF swSet[self] # {}
                                  THEN /\ currSW' = [currSW EXCEPT ![self] = CHOOSE x \in swSet[self]: TRUE]
                                       /\ pc' = [pc EXCEPT ![self] = "ReconcileEventForSW"]
                                       /\ UNCHANGED << controllerGlobalLock, 
                                                       swSeqChangedStatus, 
                                                       ofcModuleInitStatus >>
                                  ELSE /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                          \/ controllerGlobalLock[1] = self[1]
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                          \/ controllerLocalLock[self[1]] = self
                                       /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                          \/ controllerGlobalLock[1] = self[1]
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                       /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![self[1]] = remainingEvents[self] \o swSeqChangedStatus[self[1]]]
                                       /\ ofcModuleInitStatus' = [ofcModuleInitStatus EXCEPT ![self[1]][CONT_EVENT] = INIT_PROCESS]
                                       /\ pc' = [pc EXCEPT ![self] = "ofcFailoverHandlerProc"]
                                       /\ UNCHANGED currSW
                            /\ UNCHANGED << switchLock, controllerLocalLock, 
                                            FirstInstall, sw_fail_ordering_var, 
                                            ContProcSet, SwProcSet, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, installedBy, 
                                            swFailedNum, swNumEvent, 
                                            NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                            Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            switchControllerRoleStatus, 
                                            switchGeneratedEventSet, 
                                            auxEventCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, irCounter, MAX_IR_COUNTER, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            workerLocalQueue, 
                                            ofcSwSuspensionStatus, 
                                            processedEvents, localEventLog, 
                                            controllerRoleInSW, nibEventQueue, 
                                            roleUpdateStatus, isOfcEnabled, 
                                            setScheduledRoleUpdates, 
                                            ofcModuleTerminationStatus, 
                                            setRecoveredSwWithSlaveRole, 
                                            fetchedIRsBeforePassingToWorker, 
                                            eventSkipList, masterState, 
                                            controllerStateNIB, IRStatus, 
                                            NIBSwSuspensionStatus, IRQueueNIB, 
                                            subscribeList, SetScheduledIRs, 
                                            ofcFailoverStateNIB, NIBEventLog, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            controllerSet_, nxtController_, 
                                            prevLockHolder_, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            controllerSet_s, nxtController_s, 
                                            prevLockHolder, eventMsg, 
                                            controllerSet, nxtController, 
                                            eventID, toBeScheduledIRs, nextIR, 
                                            stepOfFailure_, subscriberOfcSet, 
                                            ofcID, event_, swSet, entry, index, 
                                            event, pulledNIBEventLog, 
                                            remainingEvents, 
                                            receivedEventsCopy, nextToSent, 
                                            entryIndex, rowIndex, rowRemove, 
                                            removeRow, stepOfFailure_c, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure_co, 
                                            notifOFC, isEventProcessed, msg, 
                                            stepOfFailure, 
                                            controllerFailedModules >>

ReconcileEventForSW(self) == /\ pc[self] = "ReconcileEventForSW"
                             /\ IF pulledNIBEventLog[self][currSW[self]] # <<>> /\ receivedEventsCopy[self][currSW[self]] # <<>>
                                   THEN /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                           \/ controllerGlobalLock[1] = self[1]
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                           \/ controllerLocalLock[self[1]] = self
                                        /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                           \/ controllerGlobalLock[1] = self[1]
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                        /\ event' = [event EXCEPT ![self] = Head(pulledNIBEventLog[self][currSW[self]])]
                                        /\ Assert(event'[self].swID = currSW[self], 
                                                  "Failure of assertion at line 1929, column 33.")
                                        /\ IF areEventsEquivalent(Head(receivedEventsCopy[self][currSW[self]]), event'[self])
                                              THEN /\ receivedEventsCopy' = [receivedEventsCopy EXCEPT ![self][currSW[self]] = Tail(receivedEventsCopy[self][currSW[self]])]
                                                   /\ UNCHANGED remainingEvents
                                              ELSE /\ remainingEvents' = [remainingEvents EXCEPT ![self] = Append(remainingEvents[self], event'[self])]
                                                   /\ UNCHANGED receivedEventsCopy
                                        /\ pulledNIBEventLog' = [pulledNIBEventLog EXCEPT ![self][currSW[self]] = Tail(pulledNIBEventLog[self][currSW[self]])]
                                        /\ pc' = [pc EXCEPT ![self] = "ReconcileEventForSW"]
                                        /\ UNCHANGED << eventSkipList, swSet >>
                                   ELSE /\ IF receivedEventsCopy[self][currSW[self]] # <<>>
                                              THEN /\ remainingEvents' = [remainingEvents EXCEPT ![self] = remainingEvents[self] \o receivedEventsCopy[self][currSW[self]]]
                                                   /\ UNCHANGED eventSkipList
                                              ELSE /\ eventSkipList' = [eventSkipList EXCEPT ![self[1]][currSW[self]] = eventSkipList[self[1]][currSW[self]] \o pulledNIBEventLog[self][currSW[self]]]
                                                   /\ UNCHANGED remainingEvents
                                        /\ swSet' = [swSet EXCEPT ![self] = swSet[self] \ {currSW[self]}]
                                        /\ pc' = [pc EXCEPT ![self] = "ReconcileEventLogs"]
                                        /\ UNCHANGED << controllerGlobalLock, 
                                                        event, 
                                                        pulledNIBEventLog, 
                                                        receivedEventsCopy >>
                             /\ UNCHANGED << switchLock, controllerLocalLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, installedBy, 
                                             swFailedNum, swNumEvent, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             switchControllerRoleStatus, 
                                             switchGeneratedEventSet, 
                                             auxEventCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             workerLocalQueue, 
                                             ofcSwSuspensionStatus, 
                                             processedEvents, localEventLog, 
                                             controllerRoleInSW, nibEventQueue, 
                                             roleUpdateStatus, isOfcEnabled, 
                                             setScheduledRoleUpdates, 
                                             ofcModuleTerminationStatus, 
                                             ofcModuleInitStatus, 
                                             setRecoveredSwWithSlaveRole, 
                                             fetchedIRsBeforePassingToWorker, 
                                             masterState, controllerStateNIB, 
                                             IRStatus, NIBSwSuspensionStatus, 
                                             IRQueueNIB, subscribeList, 
                                             SetScheduledIRs, 
                                             ofcFailoverStateNIB, NIBEventLog, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             controllerSet_, nxtController_, 
                                             prevLockHolder_, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             controllerSet_s, nxtController_s, 
                                             prevLockHolder, eventMsg, 
                                             controllerSet, nxtController, 
                                             eventID, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, subscriberOfcSet, 
                                             ofcID, event_, currSW, entry, 
                                             index, nextToSent, entryIndex, 
                                             rowIndex, rowRemove, removeRow, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure_co, notifOFC, 
                                             isEventProcessed, msg, 
                                             stepOfFailure, 
                                             controllerFailedModules >>

WaitForWorkersTermination(self) == /\ pc[self] = "WaitForWorkersTermination"
                                   /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                      \/ controllerGlobalLock[1] = self[1]
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                      \/ controllerLocalLock[self[1]] = self
                                   /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                      \/ controllerGlobalLock[1] = self[1]
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                   /\ allWorkersTerminated(self[1])
                                   /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]] = [y \in {CONT_MONITOR} |-> TERMINATE_INIT]
                                                                                                                                         @@ ofcModuleTerminationStatus[self[1]]]
                                   /\ pc' = [pc EXCEPT ![self] = "WaitForMonitoringServerTermination"]
                                   /\ UNCHANGED << switchLock, 
                                                   controllerLocalLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   installedBy, swFailedNum, 
                                                   swNumEvent, NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switchControllerRoleStatus, 
                                                   switchGeneratedEventSet, 
                                                   auxEventCounter, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   dependencyGraph, IR2SW, 
                                                   irCounter, MAX_IR_COUNTER, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   workerLocalQueue, 
                                                   ofcSwSuspensionStatus, 
                                                   processedEvents, 
                                                   localEventLog, 
                                                   controllerRoleInSW, 
                                                   nibEventQueue, 
                                                   roleUpdateStatus, 
                                                   isOfcEnabled, 
                                                   setScheduledRoleUpdates, 
                                                   ofcModuleInitStatus, 
                                                   setRecoveredSwWithSlaveRole, 
                                                   fetchedIRsBeforePassingToWorker, 
                                                   eventSkipList, masterState, 
                                                   controllerStateNIB, 
                                                   IRStatus, 
                                                   NIBSwSuspensionStatus, 
                                                   IRQueueNIB, subscribeList, 
                                                   SetScheduledIRs, 
                                                   ofcFailoverStateNIB, 
                                                   NIBEventLog, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   controllerSet_, 
                                                   nxtController_, 
                                                   prevLockHolder_, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, 
                                                   controllerSet_s, 
                                                   nxtController_s, 
                                                   prevLockHolder, eventMsg, 
                                                   controllerSet, 
                                                   nxtController, eventID, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   subscriberOfcSet, ofcID, 
                                                   event_, swSet, currSW, 
                                                   entry, index, event, 
                                                   pulledNIBEventLog, 
                                                   remainingEvents, 
                                                   receivedEventsCopy, 
                                                   nextToSent, entryIndex, 
                                                   rowIndex, rowRemove, 
                                                   removeRow, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure_co, notifOFC, 
                                                   isEventProcessed, msg, 
                                                   stepOfFailure, 
                                                   controllerFailedModules >>

WaitForMonitoringServerTermination(self) == /\ pc[self] = "WaitForMonitoringServerTermination"
                                            /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerGlobalLock[1] = self[1]
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerLocalLock[self[1]] = self
                                            /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerGlobalLock[1] = self[1]
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ MonitoringServerTerminated(self[1])
                                            /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]] = [y \in {CONT_EVENT} |-> TERMINATE_INIT]
                                                                                                                                                  @@ ofcModuleTerminationStatus[self[1]]]
                                            /\ pc' = [pc EXCEPT ![self] = "WaitForOFEventHandlerTermination"]
                                            /\ UNCHANGED << switchLock, 
                                                            controllerLocalLock, 
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
                                                            swNumEvent, 
                                                            NicAsic2OfaBuff, 
                                                            Ofa2NicAsicBuff, 
                                                            Installer2OfaBuff, 
                                                            Ofa2InstallerBuff, 
                                                            TCAM, 
                                                            controlMsgCounter, 
                                                            switchControllerRoleStatus, 
                                                            switchGeneratedEventSet, 
                                                            auxEventCounter, 
                                                            controllerSubmoduleFailNum, 
                                                            controllerSubmoduleFailStat, 
                                                            switchOrdering, 
                                                            dependencyGraph, 
                                                            IR2SW, irCounter, 
                                                            MAX_IR_COUNTER, 
                                                            idThreadWorkingOnIR, 
                                                            workerThreadRanking, 
                                                            workerLocalQueue, 
                                                            ofcSwSuspensionStatus, 
                                                            processedEvents, 
                                                            localEventLog, 
                                                            controllerRoleInSW, 
                                                            nibEventQueue, 
                                                            roleUpdateStatus, 
                                                            isOfcEnabled, 
                                                            setScheduledRoleUpdates, 
                                                            ofcModuleInitStatus, 
                                                            setRecoveredSwWithSlaveRole, 
                                                            fetchedIRsBeforePassingToWorker, 
                                                            eventSkipList, 
                                                            masterState, 
                                                            controllerStateNIB, 
                                                            IRStatus, 
                                                            NIBSwSuspensionStatus, 
                                                            IRQueueNIB, 
                                                            subscribeList, 
                                                            SetScheduledIRs, 
                                                            ofcFailoverStateNIB, 
                                                            NIBEventLog, 
                                                            ingressPkt, 
                                                            ingressIR, 
                                                            egressMsg, 
                                                            ofaInMsg, 
                                                            ofaOutConfirmation, 
                                                            installerInIR, 
                                                            statusMsg, 
                                                            notFailedSet, 
                                                            failedElem, 
                                                            controllerSet_, 
                                                            nxtController_, 
                                                            prevLockHolder_, 
                                                            failedSet, 
                                                            statusResolveMsg, 
                                                            recoveredElem, 
                                                            controllerSet_s, 
                                                            nxtController_s, 
                                                            prevLockHolder, 
                                                            eventMsg, 
                                                            controllerSet, 
                                                            nxtController, 
                                                            eventID, 
                                                            toBeScheduledIRs, 
                                                            nextIR, 
                                                            stepOfFailure_, 
                                                            subscriberOfcSet, 
                                                            ofcID, event_, 
                                                            swSet, currSW, 
                                                            entry, index, 
                                                            event, 
                                                            pulledNIBEventLog, 
                                                            remainingEvents, 
                                                            receivedEventsCopy, 
                                                            nextToSent, 
                                                            entryIndex, 
                                                            rowIndex, 
                                                            rowRemove, 
                                                            removeRow, 
                                                            stepOfFailure_c, 
                                                            monitoringEvent, 
                                                            setIRsToReset, 
                                                            resetIR, 
                                                            stepOfFailure_co, 
                                                            notifOFC, 
                                                            isEventProcessed, 
                                                            msg, stepOfFailure, 
                                                            controllerFailedModules >>

WaitForOFEventHandlerTermination(self) == /\ pc[self] = "WaitForOFEventHandlerTermination"
                                          /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                             \/ controllerGlobalLock[1] = self[1]
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                             \/ controllerLocalLock[self[1]] = self
                                          /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                             \/ controllerGlobalLock[1] = self[1]
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ allModulesTerminated(self[1])
                                          /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![self[1]] = FAILOVER_TERMINATE_DONE]
                                          /\ pc' = [pc EXCEPT ![self] = "Done"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLocalLock, 
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
                                                          swNumEvent, 
                                                          NicAsic2OfaBuff, 
                                                          Ofa2NicAsicBuff, 
                                                          Installer2OfaBuff, 
                                                          Ofa2InstallerBuff, 
                                                          TCAM, 
                                                          controlMsgCounter, 
                                                          switchControllerRoleStatus, 
                                                          switchGeneratedEventSet, 
                                                          auxEventCounter, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          dependencyGraph, 
                                                          IR2SW, irCounter, 
                                                          MAX_IR_COUNTER, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          workerLocalQueue, 
                                                          ofcSwSuspensionStatus, 
                                                          processedEvents, 
                                                          localEventLog, 
                                                          controllerRoleInSW, 
                                                          nibEventQueue, 
                                                          roleUpdateStatus, 
                                                          isOfcEnabled, 
                                                          setScheduledRoleUpdates, 
                                                          ofcModuleTerminationStatus, 
                                                          ofcModuleInitStatus, 
                                                          setRecoveredSwWithSlaveRole, 
                                                          fetchedIRsBeforePassingToWorker, 
                                                          eventSkipList, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          NIBSwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          subscribeList, 
                                                          SetScheduledIRs, 
                                                          NIBEventLog, 
                                                          ingressPkt, 
                                                          ingressIR, egressMsg, 
                                                          ofaInMsg, 
                                                          ofaOutConfirmation, 
                                                          installerInIR, 
                                                          statusMsg, 
                                                          notFailedSet, 
                                                          failedElem, 
                                                          controllerSet_, 
                                                          nxtController_, 
                                                          prevLockHolder_, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, 
                                                          controllerSet_s, 
                                                          nxtController_s, 
                                                          prevLockHolder, 
                                                          eventMsg, 
                                                          controllerSet, 
                                                          nxtController, 
                                                          eventID, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          subscriberOfcSet, 
                                                          ofcID, event_, swSet, 
                                                          currSW, entry, index, 
                                                          event, 
                                                          pulledNIBEventLog, 
                                                          remainingEvents, 
                                                          receivedEventsCopy, 
                                                          nextToSent, 
                                                          entryIndex, rowIndex, 
                                                          rowRemove, removeRow, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure_co, 
                                                          notifOFC, 
                                                          isEventProcessed, 
                                                          msg, stepOfFailure, 
                                                          controllerFailedModules >>

ofcFailoverHandler(self) == ofcFailoverHandlerProc(self)
                               \/ ScheduleRoleUpdateEqual(self)
                               \/ WaitForSwitchUpdateRoleACK(self)
                               \/ QueryIRQueueNIB(self)
                               \/ EventHandlerInitStateForReconciliation(self)
                               \/ ReconcileEventLogs(self)
                               \/ ReconcileEventForSW(self)
                               \/ WaitForWorkersTermination(self)
                               \/ WaitForMonitoringServerTermination(self)
                               \/ WaitForOFEventHandlerTermination(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ IF ~shouldWorkerTerminate(self[1], self[2])
                                THEN /\ isOfcEnabled[self[1]]
                                     /\ moduleIsUp(self)
                                     /\ workerLocalQueue # <<>>
                                     /\ canWorkerThreadContinue(self[1], self)
                                     /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                        \/ controllerGlobalLock[1] = self[1]
                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                     /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                        \/ controllerLocalLock[self[1]] = self
                                     /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead((workerLocalQueue[self[1]]), self)]
                                     /\ nextToSent' = [nextToSent EXCEPT ![self] = (workerLocalQueue[self[1]])[rowIndex'[self]].item]
                                     /\ IF existEquivalentItemWithID((workerLocalQueue[self[1]]), nextToSent'[self])
                                           THEN /\ entryIndex' = [entryIndex EXCEPT ![self] = getIdOfEquivalentItem((workerLocalQueue[self[1]]), nextToSent'[self])]
                                                /\ UNCHANGED irCounter
                                           ELSE /\ irCounter' = (irCounter + 1) % MAX_IR_COUNTER
                                                /\ entryIndex' = [entryIndex EXCEPT ![self] = irCounter']
                                     /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]][rowIndex'[self]].tag = self,
                                                                                     ![self[1]][rowIndex'[self]].id = entryIndex'[self]]
                                     /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                        \/ controllerGlobalLock[1] = self[1]
                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                     /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                     /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                           THEN /\ \E num \in 0..3:
                                                     stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                           ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                     /\ IF (stepOfFailure_c'[self] = 1)
                                           THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                /\ UNCHANGED << idThreadWorkingOnIR, 
                                                                roleUpdateStatus, 
                                                                controllerStateNIB, 
                                                                IRStatus >>
                                           ELSE /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextToSent'[self], index |-> entryIndex'[self]]]
                                                /\ IF (stepOfFailure_c'[self] = 2)
                                                      THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                           /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                           /\ UNCHANGED << idThreadWorkingOnIR, 
                                                                           roleUpdateStatus, 
                                                                           IRStatus >>
                                                      ELSE /\ IF idThreadWorkingOnIR[self[1]][entryIndex'[self]] = IR_UNLOCK
                                                                 THEN /\ threadWithLowerIDGetsTheLock(self[1], self, nextToSent'[self], workerLocalQueue'[self[1]])
                                                                      /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![self[1]][entryIndex'[self]] = self[2]]
                                                                      /\ IF (stepOfFailure_c'[self] = 3)
                                                                            THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                                                 /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                                                                 /\ UNCHANGED << roleUpdateStatus, 
                                                                                                 IRStatus >>
                                                                            ELSE /\ IF (workerCanSendTheIR(self[1], nextToSent'[self]))
                                                                                       THEN /\ Assert(nextToSent'[self].type \in {INSTALL_FLOW, ROLE_REQ}, 
                                                                                                      "Failure of assertion at line 2046, column 29.")
                                                                                            /\ IF nextToSent'[self].type = INSTALL_FLOW
                                                                                                  THEN /\ IRStatus' = [IRStatus EXCEPT ![nextToSent'[self].IR] = IR_SENT]
                                                                                                       /\ UNCHANGED roleUpdateStatus
                                                                                                  ELSE /\ IF nextToSent'[self].type = ROLE_REQ
                                                                                                             THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][nextToSent'[self].to].status = IR_SENT]
                                                                                                             ELSE /\ TRUE
                                                                                                                  /\ UNCHANGED roleUpdateStatus
                                                                                                       /\ UNCHANGED IRStatus
                                                                                            /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadReleaseSemaphoreAndScheduledSet"]
                                                                                            /\ UNCHANGED << roleUpdateStatus, 
                                                                                                            IRStatus >>
                                                                                 /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                                                 controllerSubmoduleFailStat >>
                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveQueue1"]
                                                                      /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                                      controllerSubmoduleFailStat, 
                                                                                      idThreadWorkingOnIR, 
                                                                                      roleUpdateStatus, 
                                                                                      IRStatus >>
                                     /\ UNCHANGED ofcModuleTerminationStatus
                                ELSE /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]][self[2]] = TERMINATE_DONE]
                                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED << controllerGlobalLock, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     irCounter, 
                                                     idThreadWorkingOnIR, 
                                                     workerLocalQueue, 
                                                     roleUpdateStatus, 
                                                     controllerStateNIB, 
                                                     IRStatus, nextToSent, 
                                                     entryIndex, rowIndex, 
                                                     stepOfFailure_c >>
                          /\ UNCHANGED << switchLock, controllerLocalLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          installedBy, swFailedNum, swNumEvent, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          switchControllerRoleStatus, 
                                          switchGeneratedEventSet, 
                                          auxEventCounter, switchOrdering, 
                                          dependencyGraph, IR2SW, 
                                          MAX_IR_COUNTER, workerThreadRanking, 
                                          ofcSwSuspensionStatus, 
                                          processedEvents, localEventLog, 
                                          controllerRoleInSW, nibEventQueue, 
                                          isOfcEnabled, 
                                          setScheduledRoleUpdates, 
                                          ofcModuleInitStatus, 
                                          setRecoveredSwWithSlaveRole, 
                                          fetchedIRsBeforePassingToWorker, 
                                          eventSkipList, masterState, 
                                          NIBSwSuspensionStatus, IRQueueNIB, 
                                          subscribeList, SetScheduledIRs, 
                                          ofcFailoverStateNIB, NIBEventLog, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, 
                                          controllerSet_, nxtController_, 
                                          prevLockHolder_, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          controllerSet_s, nxtController_s, 
                                          prevLockHolder, eventMsg, 
                                          controllerSet, nxtController, 
                                          eventID, toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, subscriberOfcSet, 
                                          ofcID, event_, swSet, currSW, entry, 
                                          index, event, pulledNIBEventLog, 
                                          remainingEvents, receivedEventsCopy, 
                                          rowRemove, removeRow, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure_co, notifOFC, 
                                          isEventProcessed, msg, stepOfFailure, 
                                          controllerFailedModules >>

ControllerThreadReleaseSemaphoreAndScheduledSet(self) == /\ pc[self] = "ControllerThreadReleaseSemaphoreAndScheduledSet"
                                                         /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                            \/ controllerGlobalLock[1] = self[1]
                                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                         /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                                            \/ controllerLocalLock[self[1]] = self
                                                         /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                            \/ controllerGlobalLock[1] = self[1]
                                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                         /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                                         /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                                               THEN /\ \E num \in 0..4:
                                                                         stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                                               ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                                         /\ IF (stepOfFailure_c'[self] # 1)
                                                               THEN /\ IF idThreadWorkingOnIR[self[1]][entryIndex[self]] = self[2]
                                                                          THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![self[1]][entryIndex[self]] = IR_UNLOCK]
                                                                          ELSE /\ TRUE
                                                                               /\ UNCHANGED idThreadWorkingOnIR
                                                                    /\ IF (stepOfFailure_c'[self] # 2)
                                                                          THEN /\ IF nextToSent[self].type = INSTALL_FLOW
                                                                                     THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextToSent[self].to] = SetScheduledIRs[nextToSent[self].to]\{nextToSent[self].IR}]
                                                                                     ELSE /\ TRUE
                                                                                          /\ UNCHANGED SetScheduledIRs
                                                                               /\ IF (stepOfFailure_c'[self] # 3)
                                                                                     THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                                                          /\ IF (stepOfFailure_c'[self] # 4)
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
                                                               ELSE /\ TRUE
                                                                    /\ UNCHANGED << idThreadWorkingOnIR, 
                                                                                    workerLocalQueue, 
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
                                                         /\ UNCHANGED << switchLock, 
                                                                         controllerLocalLock, 
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
                                                                         swNumEvent, 
                                                                         NicAsic2OfaBuff, 
                                                                         Ofa2NicAsicBuff, 
                                                                         Installer2OfaBuff, 
                                                                         Ofa2InstallerBuff, 
                                                                         TCAM, 
                                                                         controlMsgCounter, 
                                                                         switchControllerRoleStatus, 
                                                                         switchGeneratedEventSet, 
                                                                         auxEventCounter, 
                                                                         switchOrdering, 
                                                                         dependencyGraph, 
                                                                         IR2SW, 
                                                                         irCounter, 
                                                                         MAX_IR_COUNTER, 
                                                                         workerThreadRanking, 
                                                                         ofcSwSuspensionStatus, 
                                                                         processedEvents, 
                                                                         localEventLog, 
                                                                         controllerRoleInSW, 
                                                                         nibEventQueue, 
                                                                         roleUpdateStatus, 
                                                                         isOfcEnabled, 
                                                                         setScheduledRoleUpdates, 
                                                                         ofcModuleTerminationStatus, 
                                                                         ofcModuleInitStatus, 
                                                                         setRecoveredSwWithSlaveRole, 
                                                                         fetchedIRsBeforePassingToWorker, 
                                                                         eventSkipList, 
                                                                         masterState, 
                                                                         IRStatus, 
                                                                         NIBSwSuspensionStatus, 
                                                                         subscribeList, 
                                                                         ofcFailoverStateNIB, 
                                                                         NIBEventLog, 
                                                                         ingressPkt, 
                                                                         ingressIR, 
                                                                         egressMsg, 
                                                                         ofaInMsg, 
                                                                         ofaOutConfirmation, 
                                                                         installerInIR, 
                                                                         statusMsg, 
                                                                         notFailedSet, 
                                                                         failedElem, 
                                                                         controllerSet_, 
                                                                         nxtController_, 
                                                                         prevLockHolder_, 
                                                                         failedSet, 
                                                                         statusResolveMsg, 
                                                                         recoveredElem, 
                                                                         controllerSet_s, 
                                                                         nxtController_s, 
                                                                         prevLockHolder, 
                                                                         eventMsg, 
                                                                         controllerSet, 
                                                                         nxtController, 
                                                                         eventID, 
                                                                         toBeScheduledIRs, 
                                                                         nextIR, 
                                                                         stepOfFailure_, 
                                                                         subscriberOfcSet, 
                                                                         ofcID, 
                                                                         event_, 
                                                                         swSet, 
                                                                         currSW, 
                                                                         entry, 
                                                                         index, 
                                                                         event, 
                                                                         pulledNIBEventLog, 
                                                                         remainingEvents, 
                                                                         receivedEventsCopy, 
                                                                         nextToSent, 
                                                                         entryIndex, 
                                                                         rowIndex, 
                                                                         monitoringEvent, 
                                                                         setIRsToReset, 
                                                                         resetIR, 
                                                                         stepOfFailure_co, 
                                                                         notifOFC, 
                                                                         isEventProcessed, 
                                                                         msg, 
                                                                         stepOfFailure, 
                                                                         controllerFailedModules >>

ControllerThreadRemoveQueue1(self) == /\ pc[self] = "ControllerThreadRemoveQueue1"
                                      /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                         \/ controllerGlobalLock[1] = self[1]
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                         \/ controllerLocalLock[self[1]] = self
                                      /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                         \/ controllerGlobalLock[1] = self[1]
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                      /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith((workerLocalQueue[self[1]]), nextToSent[self], self)]
                                      /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = removeFromSeq((workerLocalQueue[self[1]]), rowRemove'[self])]
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLocalLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      installedBy, swFailedNum, 
                                                      swNumEvent, 
                                                      NicAsic2OfaBuff, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      switchControllerRoleStatus, 
                                                      switchGeneratedEventSet, 
                                                      auxEventCounter, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      dependencyGraph, IR2SW, 
                                                      irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      ofcSwSuspensionStatus, 
                                                      processedEvents, 
                                                      localEventLog, 
                                                      controllerRoleInSW, 
                                                      nibEventQueue, 
                                                      roleUpdateStatus, 
                                                      isOfcEnabled, 
                                                      setScheduledRoleUpdates, 
                                                      ofcModuleTerminationStatus, 
                                                      ofcModuleInitStatus, 
                                                      setRecoveredSwWithSlaveRole, 
                                                      fetchedIRsBeforePassingToWorker, 
                                                      eventSkipList, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      NIBSwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      subscribeList, 
                                                      SetScheduledIRs, 
                                                      ofcFailoverStateNIB, 
                                                      NIBEventLog, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      controllerSet_, 
                                                      nxtController_, 
                                                      prevLockHolder_, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, 
                                                      controllerSet_s, 
                                                      nxtController_s, 
                                                      prevLockHolder, eventMsg, 
                                                      controllerSet, 
                                                      nxtController, eventID, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, 
                                                      subscriberOfcSet, ofcID, 
                                                      event_, swSet, currSW, 
                                                      entry, index, event, 
                                                      pulledNIBEventLog, 
                                                      remainingEvents, 
                                                      receivedEventsCopy, 
                                                      nextToSent, entryIndex, 
                                                      rowIndex, removeRow, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure_co, 
                                                      notifOFC, 
                                                      isEventProcessed, msg, 
                                                      stepOfFailure, 
                                                      controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ switchLock[1] \notin {SW_FAILURE_PROC, SW_RESOLVE_PROC}
                                   /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                      \/ controllerGlobalLock[1] = self[1]
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
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
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadReleaseSemaphoreAndScheduledSet"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ UNCHANGED << controllerLocalLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   installedBy, swFailedNum, 
                                                   swNumEvent, NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   switchControllerRoleStatus, 
                                                   switchGeneratedEventSet, 
                                                   auxEventCounter, 
                                                   switchOrdering, 
                                                   dependencyGraph, IR2SW, 
                                                   irCounter, MAX_IR_COUNTER, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   workerLocalQueue, 
                                                   ofcSwSuspensionStatus, 
                                                   processedEvents, 
                                                   localEventLog, 
                                                   controllerRoleInSW, 
                                                   nibEventQueue, 
                                                   roleUpdateStatus, 
                                                   isOfcEnabled, 
                                                   setScheduledRoleUpdates, 
                                                   ofcModuleTerminationStatus, 
                                                   ofcModuleInitStatus, 
                                                   setRecoveredSwWithSlaveRole, 
                                                   fetchedIRsBeforePassingToWorker, 
                                                   eventSkipList, masterState, 
                                                   IRStatus, 
                                                   NIBSwSuspensionStatus, 
                                                   IRQueueNIB, subscribeList, 
                                                   SetScheduledIRs, 
                                                   ofcFailoverStateNIB, 
                                                   NIBEventLog, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   controllerSet_, 
                                                   nxtController_, 
                                                   prevLockHolder_, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, 
                                                   controllerSet_s, 
                                                   nxtController_s, 
                                                   prevLockHolder, eventMsg, 
                                                   controllerSet, 
                                                   nxtController, eventID, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, 
                                                   subscriberOfcSet, ofcID, 
                                                   event_, swSet, currSW, 
                                                   entry, index, event, 
                                                   pulledNIBEventLog, 
                                                   remainingEvents, 
                                                   receivedEventsCopy, 
                                                   nextToSent, entryIndex, 
                                                   rowIndex, rowRemove, 
                                                   removeRow, monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure_co, notifOFC, 
                                                   isEventProcessed, msg, 
                                                   stepOfFailure, 
                                                   controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ isOfcEnabled[self[1]]
                                             /\ moduleIsUp(self)
                                             /\ IRQueueNIB # <<>>
                                             /\ canWorkerThreadContinue(self[1], self)
                                             /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                \/ controllerGlobalLock[1] = self[1]
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ \/ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                                \/ controllerGlobalLock'[1] = self[1]
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                                \/ controllerLocalLock[self[1]] = self
                                             /\ controllerLocalLock' = [controllerLocalLock EXCEPT ![self[1]] = <<NO_LOCK, NO_LOCK>>]
                                             /\ IF (controllerStateNIB[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (controllerStateNIB[self].next.type = INSTALL_FLOW)
                                                              THEN /\ IF (IRStatus[controllerStateNIB[self].next.IR] = IR_SENT)
                                                                         THEN /\ IRStatus' = [IRStatus EXCEPT ![controllerStateNIB[self].next.IR] = IR_NONE]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED IRStatus
                                                                   /\ UNCHANGED roleUpdateStatus
                                                              ELSE /\ IF (controllerStateNIB[self].next.type = ROLE_REQ)
                                                                         THEN /\ IF (roleUpdateStatus[self[1]][controllerStateNIB[self].next.to].status = IR_SENT)
                                                                                    THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][controllerStateNIB[self].next.to].status = IR_NONE]
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
                                                             swNumEvent, 
                                                             NicAsic2OfaBuff, 
                                                             Ofa2NicAsicBuff, 
                                                             Installer2OfaBuff, 
                                                             Ofa2InstallerBuff, 
                                                             TCAM, 
                                                             controlMsgCounter, 
                                                             switchControllerRoleStatus, 
                                                             switchGeneratedEventSet, 
                                                             auxEventCounter, 
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             switchOrdering, 
                                                             dependencyGraph, 
                                                             IR2SW, irCounter, 
                                                             MAX_IR_COUNTER, 
                                                             workerThreadRanking, 
                                                             workerLocalQueue, 
                                                             ofcSwSuspensionStatus, 
                                                             processedEvents, 
                                                             localEventLog, 
                                                             controllerRoleInSW, 
                                                             nibEventQueue, 
                                                             isOfcEnabled, 
                                                             setScheduledRoleUpdates, 
                                                             ofcModuleTerminationStatus, 
                                                             ofcModuleInitStatus, 
                                                             setRecoveredSwWithSlaveRole, 
                                                             fetchedIRsBeforePassingToWorker, 
                                                             eventSkipList, 
                                                             masterState, 
                                                             controllerStateNIB, 
                                                             NIBSwSuspensionStatus, 
                                                             IRQueueNIB, 
                                                             subscribeList, 
                                                             ofcFailoverStateNIB, 
                                                             NIBEventLog, 
                                                             ingressPkt, 
                                                             ingressIR, 
                                                             egressMsg, 
                                                             ofaInMsg, 
                                                             ofaOutConfirmation, 
                                                             installerInIR, 
                                                             statusMsg, 
                                                             notFailedSet, 
                                                             failedElem, 
                                                             controllerSet_, 
                                                             nxtController_, 
                                                             prevLockHolder_, 
                                                             failedSet, 
                                                             statusResolveMsg, 
                                                             recoveredElem, 
                                                             controllerSet_s, 
                                                             nxtController_s, 
                                                             prevLockHolder, 
                                                             eventMsg, 
                                                             controllerSet, 
                                                             nxtController, 
                                                             eventID, 
                                                             toBeScheduledIRs, 
                                                             nextIR, 
                                                             stepOfFailure_, 
                                                             subscriberOfcSet, 
                                                             ofcID, event_, 
                                                             swSet, currSW, 
                                                             entry, index, 
                                                             event, 
                                                             pulledNIBEventLog, 
                                                             remainingEvents, 
                                                             receivedEventsCopy, 
                                                             nextToSent, 
                                                             entryIndex, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             removeRow, 
                                                             stepOfFailure_c, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, 
                                                             stepOfFailure_co, 
                                                             notifOFC, 
                                                             isEventProcessed, 
                                                             msg, 
                                                             stepOfFailure, 
                                                             controllerFailedModules >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadReleaseSemaphoreAndScheduledSet(self)
                                    \/ ControllerThreadRemoveQueue1(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ IF ~shouldEventHandlerTerminate(self[1])
                                          THEN /\ isOfcEnabled[self[1]]
                                               /\ moduleIsUp(self)
                                               /\ swSeqChangedStatus[self[1]] # <<>>
                                               /\ Assert(ofcModuleInitStatus[self[1]][self[2]] \in {INIT_NONE, INIT_RUN, INIT_PROCESS}, 
                                                         "Failure of assertion at line 2218, column 10.")
                                               /\ ofcModuleInitStatus[self[1]][self[2]] \in {INIT_RUN, INIT_PROCESS}
                                               /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                  \/ controllerGlobalLock[1] = self[1]
                                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                               /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                                  \/ controllerLocalLock[self[1]] = self
                                               /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                  \/ controllerGlobalLock[1] = self[1]
                                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                               /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                               /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus[self[1]])]
                                               /\ IF ofcModuleInitStatus[self[1]][self[2]] = INIT_PROCESS
                                                     THEN /\ IF eventSkipList[self[1]][monitoringEvent'[self].swID] # <<>>
                                                                THEN /\ IF areEventsEquivalent(monitoringEvent'[self], Head(eventSkipList[self[1]][monitoringEvent'[self].swID]))
                                                                           THEN /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![self[1]] = Tail(swSeqChangedStatus[self[1]])]
                                                                                /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent'[self].swID] = SW_RUN
                                                                                      THEN /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]][monitoringEvent'[self].swID] = SW_SUSPEND]
                                                                                      ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent'[self].swID] = SW_SUSPEND
                                                                                                 THEN /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]][monitoringEvent'[self].swID] = SW_RUN]
                                                                                                 ELSE /\ TRUE
                                                                                                      /\ UNCHANGED ofcSwSuspensionStatus
                                                                           ELSE /\ TRUE
                                                                                /\ UNCHANGED << swSeqChangedStatus, 
                                                                                                ofcSwSuspensionStatus >>
                                                                     /\ eventSkipList' = [eventSkipList EXCEPT ![self[1]][monitoringEvent'[self].swID] = Tail(eventSkipList[self[1]][monitoringEvent'[self].swID])]
                                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                                     /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                                     controllerSubmoduleFailStat, 
                                                                                     workerLocalQueue, 
                                                                                     nibEventQueue, 
                                                                                     roleUpdateStatus, 
                                                                                     setScheduledRoleUpdates, 
                                                                                     controllerStateNIB, 
                                                                                     NIBSwSuspensionStatus, 
                                                                                     stepOfFailure_co, 
                                                                                     notifOFC, 
                                                                                     isEventProcessed >>
                                                                ELSE /\ isEventProcessed' = [isEventProcessed EXCEPT ![self] = 1]
                                                                     /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent'[self].swID] = SW_RUN
                                                                           THEN /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                                                                               controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                                                                      THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                                                                 /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                                                              \/ /\ TRUE
                                                                                                 /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                                                                      ELSE /\ TRUE
                                                                                           /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                                                           controllerSubmoduleFailStat >>
                                                                                /\ IF (controllerSubmoduleFailStat'[self] = NotFailed)
                                                                                      THEN /\ IF (masterState[self[1]] = ROLE_MASTER)
                                                                                                 THEN /\ NIBSwSuspensionStatus' = [NIBSwSuspensionStatus EXCEPT ![monitoringEvent'[self].swID] = SW_SUSPEND]
                                                                                                      /\ notifOFC' = [notifOFC EXCEPT ![self] = CHOOSE x \in ({ofc0, ofc1} \ {self[1]}): TRUE]
                                                                                                      /\ nibEventQueue' = [nibEventQueue EXCEPT ![notifOFC'[self]] = Append(nibEventQueue[notifOFC'[self]], [type |-> TOPO_MOD,
                                                                                                                                                                                                             sw |-> monitoringEvent'[self].swID,
                                                                                                                                                                                                             status |-> SW_SUSPEND])]
                                                                                                 ELSE /\ TRUE
                                                                                                      /\ UNCHANGED << nibEventQueue, 
                                                                                                                      NIBSwSuspensionStatus, 
                                                                                                                      notifOFC >>
                                                                                           /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]][monitoringEvent'[self].swID] = SW_SUSPEND]
                                                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                                                           /\ UNCHANGED << ofcSwSuspensionStatus, 
                                                                                                           nibEventQueue, 
                                                                                                           NIBSwSuspensionStatus, 
                                                                                                           notifOFC >>
                                                                                /\ UNCHANGED << workerLocalQueue, 
                                                                                                roleUpdateStatus, 
                                                                                                setScheduledRoleUpdates, 
                                                                                                controllerStateNIB, 
                                                                                                stepOfFailure_co >>
                                                                           ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ ofcSwSuspensionStatus[self[1]][monitoringEvent'[self].swID] = SW_SUSPEND
                                                                                      THEN /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                                                                                 THEN /\ \E num \in 0..3:
                                                                                                           stepOfFailure_co' = [stepOfFailure_co EXCEPT ![self] = num]
                                                                                                 ELSE /\ stepOfFailure_co' = [stepOfFailure_co EXCEPT ![self] = 0]
                                                                                           /\ IF (stepOfFailure_co'[self] = 1)
                                                                                                 THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                                                                      /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                                                                      /\ UNCHANGED << workerLocalQueue, 
                                                                                                                      ofcSwSuspensionStatus, 
                                                                                                                      nibEventQueue, 
                                                                                                                      roleUpdateStatus, 
                                                                                                                      setScheduledRoleUpdates, 
                                                                                                                      controllerStateNIB, 
                                                                                                                      NIBSwSuspensionStatus, 
                                                                                                                      notifOFC >>
                                                                                                 ELSE /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent'[self].swID]]
                                                                                                      /\ IF (stepOfFailure_co'[self] = 2)
                                                                                                            THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                                                                                 /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                                                                                 /\ UNCHANGED << workerLocalQueue, 
                                                                                                                                 ofcSwSuspensionStatus, 
                                                                                                                                 nibEventQueue, 
                                                                                                                                 roleUpdateStatus, 
                                                                                                                                 setScheduledRoleUpdates, 
                                                                                                                                 NIBSwSuspensionStatus, 
                                                                                                                                 notifOFC >>
                                                                                                            ELSE /\ IF (masterState[self[1]] = ROLE_MASTER)
                                                                                                                       THEN /\ NIBSwSuspensionStatus' = [NIBSwSuspensionStatus EXCEPT ![monitoringEvent'[self].swID] = SW_RUN]
                                                                                                                            /\ notifOFC' = [notifOFC EXCEPT ![self] = CHOOSE x \in ({ofc0, ofc1} \ {self[1]}): TRUE]
                                                                                                                            /\ nibEventQueue' = [nibEventQueue EXCEPT ![notifOFC'[self]] = Append(nibEventQueue[notifOFC'[self]], [type |-> TOPO_MOD,
                                                                                                                                                                                                                                   sw |-> monitoringEvent'[self].swID,
                                                                                                                                                                                                                                   status |-> SW_RUN])]
                                                                                                                       ELSE /\ TRUE
                                                                                                                            /\ UNCHANGED << nibEventQueue, 
                                                                                                                                            NIBSwSuspensionStatus, 
                                                                                                                                            notifOFC >>
                                                                                                                 /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]][monitoringEvent'[self].swID] = SW_RUN]
                                                                                                                 /\ IF (stepOfFailure_co'[self] = 3)
                                                                                                                       THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                                                                                            /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                                                                                            /\ UNCHANGED << workerLocalQueue, 
                                                                                                                                            roleUpdateStatus, 
                                                                                                                                            setScheduledRoleUpdates >>
                                                                                                                       ELSE /\ IF ~existsMonitoringEventHigherNum(monitoringEvent'[self], self[1])
                                                                                                                                  THEN /\ IF controllerRoleInSW[self[1]][monitoringEvent'[self].swID] # ROLE_MASTER
                                                                                                                                             THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][(monitoringEvent'[self].swID)] = [roletype |-> ROLE_MASTER, status |-> IR_NONE]]
                                                                                                                                                  /\ workerLocalQueue' = [workerLocalQueue EXCEPT ![self[1]] = Append((workerLocalQueue[self[1]]), [item |-> ([type |-> ROLE_REQ, roletype |-> ROLE_MASTER, to |-> (monitoringEvent'[self].swID)]), id |-> -1, tag |-> NO_TAG])]
                                                                                                                                                  /\ setScheduledRoleUpdates' = [setScheduledRoleUpdates EXCEPT ![self[1]] = setScheduledRoleUpdates[self[1]] \cup {(monitoringEvent'[self].swID)}]
                                                                                                                                             ELSE /\ TRUE
                                                                                                                                                  /\ UNCHANGED << workerLocalQueue, 
                                                                                                                                                                  roleUpdateStatus, 
                                                                                                                                                                  setScheduledRoleUpdates >>
                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                                                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                                                                                                       /\ UNCHANGED << workerLocalQueue, 
                                                                                                                                                       roleUpdateStatus, 
                                                                                                                                                       setScheduledRoleUpdates >>
                                                                                                                            /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                                                                                            controllerSubmoduleFailStat >>
                                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                                                           /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                                                           controllerSubmoduleFailStat, 
                                                                                                           workerLocalQueue, 
                                                                                                           ofcSwSuspensionStatus, 
                                                                                                           nibEventQueue, 
                                                                                                           roleUpdateStatus, 
                                                                                                           setScheduledRoleUpdates, 
                                                                                                           controllerStateNIB, 
                                                                                                           NIBSwSuspensionStatus, 
                                                                                                           stepOfFailure_co, 
                                                                                                           notifOFC >>
                                                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                                                     eventSkipList >>
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                          /\ UNCHANGED << swSeqChangedStatus, 
                                                                          controllerSubmoduleFailNum, 
                                                                          controllerSubmoduleFailStat, 
                                                                          workerLocalQueue, 
                                                                          ofcSwSuspensionStatus, 
                                                                          nibEventQueue, 
                                                                          roleUpdateStatus, 
                                                                          setScheduledRoleUpdates, 
                                                                          eventSkipList, 
                                                                          controllerStateNIB, 
                                                                          NIBSwSuspensionStatus, 
                                                                          stepOfFailure_co, 
                                                                          notifOFC, 
                                                                          isEventProcessed >>
                                               /\ UNCHANGED ofcModuleTerminationStatus
                                          ELSE /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]][self[2]] = TERMINATE_DONE]
                                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                                               /\ UNCHANGED << controllerGlobalLock, 
                                                               swSeqChangedStatus, 
                                                               controllerSubmoduleFailNum, 
                                                               controllerSubmoduleFailStat, 
                                                               workerLocalQueue, 
                                                               ofcSwSuspensionStatus, 
                                                               nibEventQueue, 
                                                               roleUpdateStatus, 
                                                               setScheduledRoleUpdates, 
                                                               eventSkipList, 
                                                               controllerStateNIB, 
                                                               NIBSwSuspensionStatus, 
                                                               monitoringEvent, 
                                                               stepOfFailure_co, 
                                                               notifOFC, 
                                                               isEventProcessed >>
                                    /\ UNCHANGED << switchLock, 
                                                    controllerLocalLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    installedBy, swFailedNum, 
                                                    swNumEvent, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    switchControllerRoleStatus, 
                                                    switchGeneratedEventSet, 
                                                    auxEventCounter, 
                                                    switchOrdering, 
                                                    dependencyGraph, IR2SW, 
                                                    irCounter, MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    processedEvents, 
                                                    localEventLog, 
                                                    controllerRoleInSW, 
                                                    isOfcEnabled, 
                                                    ofcModuleInitStatus, 
                                                    setRecoveredSwWithSlaveRole, 
                                                    fetchedIRsBeforePassingToWorker, 
                                                    masterState, IRStatus, 
                                                    IRQueueNIB, subscribeList, 
                                                    SetScheduledIRs, 
                                                    ofcFailoverStateNIB, 
                                                    NIBEventLog, ingressPkt, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    controllerSet_, 
                                                    nxtController_, 
                                                    prevLockHolder_, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, 
                                                    controllerSet_s, 
                                                    nxtController_s, 
                                                    prevLockHolder, eventMsg, 
                                                    controllerSet, 
                                                    nxtController, eventID, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, 
                                                    subscriberOfcSet, ofcID, 
                                                    event_, swSet, currSW, 
                                                    entry, index, event, 
                                                    pulledNIBEventLog, 
                                                    remainingEvents, 
                                                    receivedEventsCopy, 
                                                    nextToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    removeRow, stepOfFailure_c, 
                                                    setIRsToReset, resetIR, 
                                                    msg, stepOfFailure, 
                                                    controllerFailedModules >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                      \/ controllerGlobalLock[1] = self[1]
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                                      \/ controllerLocalLock[self[1]] = self
                                                   /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                      \/ controllerGlobalLock[1] = self[1]
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF isEventProcessed[self] = 1
                                                         THEN /\ processedEvents' = [processedEvents EXCEPT ![self[1]] = processedEvents[self[1]] \cup {monitoringEvent[self].auxNum}]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED processedEvents
                                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                                         THEN /\ \E num \in 0..2:
                                                                   stepOfFailure_co' = [stepOfFailure_co EXCEPT ![self] = num]
                                                         ELSE /\ stepOfFailure_co' = [stepOfFailure_co EXCEPT ![self] = 0]
                                                   /\ IF (stepOfFailure_co'[self] # 1)
                                                         THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                              /\ IF (stepOfFailure_co'[self] # 2)
                                                                    THEN /\ swSeqChangedStatus' = [swSeqChangedStatus EXCEPT ![self[1]] = Tail(swSeqChangedStatus[self[1]])]
                                                                         /\ IF masterState[self[1]] = ROLE_MASTER /\ isEventProcessed[self] = 1
                                                                               THEN /\ NIBEventLog' = [NIBEventLog EXCEPT ![monitoringEvent[self].swID] = Append(NIBEventLog[monitoringEvent[self].swID], monitoringEvent[self])]
                                                                               ELSE /\ TRUE
                                                                                    /\ UNCHANGED NIBEventLog
                                                                         /\ localEventLog' = [localEventLog EXCEPT ![self[1]][monitoringEvent[self].swID] = Append(localEventLog[self[1]][monitoringEvent[self].swID], monitoringEvent[self])]
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED << swSeqChangedStatus, 
                                                                                         localEventLog, 
                                                                                         NIBEventLog >>
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << swSeqChangedStatus, 
                                                                              localEventLog, 
                                                                              controllerStateNIB, 
                                                                              NIBEventLog >>
                                                   /\ isEventProcessed' = [isEventProcessed EXCEPT ![self] = 0]
                                                   /\ IF (stepOfFailure_co'[self] # 0)
                                                         THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                              /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                              /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                              controllerSubmoduleFailStat >>
                                                   /\ UNCHANGED << switchLock, 
                                                                   controllerLocalLock, 
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
                                                                   swNumEvent, 
                                                                   NicAsic2OfaBuff, 
                                                                   Ofa2NicAsicBuff, 
                                                                   Installer2OfaBuff, 
                                                                   Ofa2InstallerBuff, 
                                                                   TCAM, 
                                                                   controlMsgCounter, 
                                                                   switchControllerRoleStatus, 
                                                                   switchGeneratedEventSet, 
                                                                   auxEventCounter, 
                                                                   switchOrdering, 
                                                                   dependencyGraph, 
                                                                   IR2SW, 
                                                                   irCounter, 
                                                                   MAX_IR_COUNTER, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   workerLocalQueue, 
                                                                   ofcSwSuspensionStatus, 
                                                                   controllerRoleInSW, 
                                                                   nibEventQueue, 
                                                                   roleUpdateStatus, 
                                                                   isOfcEnabled, 
                                                                   setScheduledRoleUpdates, 
                                                                   ofcModuleTerminationStatus, 
                                                                   ofcModuleInitStatus, 
                                                                   setRecoveredSwWithSlaveRole, 
                                                                   fetchedIRsBeforePassingToWorker, 
                                                                   eventSkipList, 
                                                                   masterState, 
                                                                   IRStatus, 
                                                                   NIBSwSuspensionStatus, 
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
                                                                   controllerSet_, 
                                                                   nxtController_, 
                                                                   prevLockHolder_, 
                                                                   failedSet, 
                                                                   statusResolveMsg, 
                                                                   recoveredElem, 
                                                                   controllerSet_s, 
                                                                   nxtController_s, 
                                                                   prevLockHolder, 
                                                                   eventMsg, 
                                                                   controllerSet, 
                                                                   nxtController, 
                                                                   eventID, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   subscriberOfcSet, 
                                                                   ofcID, 
                                                                   event_, 
                                                                   swSet, 
                                                                   currSW, 
                                                                   entry, 
                                                                   index, 
                                                                   event, 
                                                                   pulledNIBEventLog, 
                                                                   remainingEvents, 
                                                                   receivedEventsCopy, 
                                                                   nextToSent, 
                                                                   entryIndex, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   removeRow, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   notifOFC, 
                                                                   msg, 
                                                                   stepOfFailure, 
                                                                   controllerFailedModules >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                              \/ controllerGlobalLock[1] = self[1]
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                              \/ controllerLocalLock[self[1]] = self
                           /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                              \/ controllerGlobalLock[1] = self[1]
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
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
                           /\ UNCHANGED << switchLock, controllerLocalLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, installedBy, 
                                           swFailedNum, swNumEvent, 
                                           NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                           Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           switchControllerRoleStatus, 
                                           switchGeneratedEventSet, 
                                           auxEventCounter, switchOrdering, 
                                           dependencyGraph, IR2SW, irCounter, 
                                           MAX_IR_COUNTER, idThreadWorkingOnIR, 
                                           workerThreadRanking, 
                                           workerLocalQueue, 
                                           ofcSwSuspensionStatus, 
                                           processedEvents, localEventLog, 
                                           controllerRoleInSW, nibEventQueue, 
                                           roleUpdateStatus, isOfcEnabled, 
                                           setScheduledRoleUpdates, 
                                           ofcModuleTerminationStatus, 
                                           ofcModuleInitStatus, 
                                           setRecoveredSwWithSlaveRole, 
                                           fetchedIRsBeforePassingToWorker, 
                                           eventSkipList, masterState, 
                                           controllerStateNIB, IRStatus, 
                                           NIBSwSuspensionStatus, IRQueueNIB, 
                                           subscribeList, SetScheduledIRs, 
                                           ofcFailoverStateNIB, NIBEventLog, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, 
                                           controllerSet_, nxtController_, 
                                           prevLockHolder_, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           controllerSet_s, nxtController_s, 
                                           prevLockHolder, eventMsg, 
                                           controllerSet, nxtController, 
                                           eventID, toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, subscriberOfcSet, 
                                           ofcID, event_, swSet, currSW, entry, 
                                           index, event, pulledNIBEventLog, 
                                           remainingEvents, receivedEventsCopy, 
                                           nextToSent, entryIndex, rowIndex, 
                                           rowRemove, removeRow, 
                                           stepOfFailure_c, monitoringEvent, 
                                           resetIR, stepOfFailure_co, notifOFC, 
                                           isEventProcessed, msg, 
                                           stepOfFailure, 
                                           controllerFailedModules >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                        \/ controllerGlobalLock[1] = self[1]
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                        \/ controllerLocalLock[self[1]] = self
                     /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                        \/ controllerGlobalLock[1] = self[1]
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
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
                     /\ UNCHANGED << switchLock, controllerLocalLock, 
                                     FirstInstall, sw_fail_ordering_var, 
                                     ContProcSet, SwProcSet, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, switchStatus, 
                                     installedIRs, installedBy, swFailedNum, 
                                     swNumEvent, NicAsic2OfaBuff, 
                                     Ofa2NicAsicBuff, Installer2OfaBuff, 
                                     Ofa2InstallerBuff, TCAM, 
                                     controlMsgCounter, 
                                     switchControllerRoleStatus, 
                                     switchGeneratedEventSet, auxEventCounter, 
                                     switchOrdering, dependencyGraph, IR2SW, 
                                     irCounter, MAX_IR_COUNTER, 
                                     idThreadWorkingOnIR, workerThreadRanking, 
                                     workerLocalQueue, ofcSwSuspensionStatus, 
                                     processedEvents, localEventLog, 
                                     controllerRoleInSW, nibEventQueue, 
                                     roleUpdateStatus, isOfcEnabled, 
                                     setScheduledRoleUpdates, 
                                     ofcModuleTerminationStatus, 
                                     ofcModuleInitStatus, 
                                     setRecoveredSwWithSlaveRole, 
                                     fetchedIRsBeforePassingToWorker, 
                                     eventSkipList, masterState, 
                                     controllerStateNIB, NIBSwSuspensionStatus, 
                                     IRQueueNIB, subscribeList, 
                                     SetScheduledIRs, ofcFailoverStateNIB, 
                                     NIBEventLog, ingressPkt, ingressIR, 
                                     egressMsg, ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, controllerSet_, 
                                     nxtController_, prevLockHolder_, 
                                     failedSet, statusResolveMsg, 
                                     recoveredElem, controllerSet_s, 
                                     nxtController_s, prevLockHolder, eventMsg, 
                                     controllerSet, nxtController, eventID, 
                                     toBeScheduledIRs, nextIR, stepOfFailure_, 
                                     subscriberOfcSet, ofcID, event_, swSet, 
                                     currSW, entry, index, event, 
                                     pulledNIBEventLog, remainingEvents, 
                                     receivedEventsCopy, nextToSent, 
                                     entryIndex, rowIndex, rowRemove, 
                                     removeRow, stepOfFailure_c, 
                                     monitoringEvent, stepOfFailure_co, 
                                     notifOFC, isEventProcessed, msg, 
                                     stepOfFailure, controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ isOfcEnabled[self[1]]
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus[self[1]] # <<>>
                                                   /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                      \/ controllerGlobalLock[1] = self[1]
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                                      \/ controllerLocalLock[self[1]] = self
                                                   /\ controllerLocalLock' = [controllerLocalLock EXCEPT ![self[1]] = <<NO_LOCK, NO_LOCK>>]
                                                   /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                      \/ controllerGlobalLock[1] = self[1]
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (controllerStateNIB[self].type = START_RESET_IR)
                                                         THEN /\ IF (masterState[self[1]] = ROLE_MASTER)
                                                                    THEN /\ NIBSwSuspensionStatus' = [NIBSwSuspensionStatus EXCEPT ![self[1]][controllerStateNIB[self].sw] = SW_SUSPEND]
                                                                         /\ notifOFC' = [notifOFC EXCEPT ![self] = CHOOSE x \in ({ofc0, ofc1} \ {self[1]}): TRUE]
                                                                         /\ nibEventQueue' = [nibEventQueue EXCEPT ![notifOFC'[self]] = Append(nibEventQueue[notifOFC'[self]], [type |-> TOPO_MOD,
                                                                                                                                                                                sw |-> monitoringEvent[self].swID,
                                                                                                                                                                                status |-> SW_SUSPEND])]
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED << nibEventQueue, 
                                                                                         NIBSwSuspensionStatus, 
                                                                                         notifOFC >>
                                                              /\ ofcSwSuspensionStatus' = [ofcSwSuspensionStatus EXCEPT ![self[1]][controllerStateNIB[self].sw] = SW_SUSPEND]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << ofcSwSuspensionStatus, 
                                                                              nibEventQueue, 
                                                                              NIBSwSuspensionStatus, 
                                                                              notifOFC >>
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
                                                                   swNumEvent, 
                                                                   NicAsic2OfaBuff, 
                                                                   Ofa2NicAsicBuff, 
                                                                   Installer2OfaBuff, 
                                                                   Ofa2InstallerBuff, 
                                                                   TCAM, 
                                                                   controlMsgCounter, 
                                                                   switchControllerRoleStatus, 
                                                                   switchGeneratedEventSet, 
                                                                   auxEventCounter, 
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
                                                                   processedEvents, 
                                                                   localEventLog, 
                                                                   controllerRoleInSW, 
                                                                   roleUpdateStatus, 
                                                                   isOfcEnabled, 
                                                                   setScheduledRoleUpdates, 
                                                                   ofcModuleTerminationStatus, 
                                                                   ofcModuleInitStatus, 
                                                                   setRecoveredSwWithSlaveRole, 
                                                                   fetchedIRsBeforePassingToWorker, 
                                                                   eventSkipList, 
                                                                   masterState, 
                                                                   controllerStateNIB, 
                                                                   IRStatus, 
                                                                   IRQueueNIB, 
                                                                   subscribeList, 
                                                                   SetScheduledIRs, 
                                                                   ofcFailoverStateNIB, 
                                                                   NIBEventLog, 
                                                                   ingressPkt, 
                                                                   ingressIR, 
                                                                   egressMsg, 
                                                                   ofaInMsg, 
                                                                   ofaOutConfirmation, 
                                                                   installerInIR, 
                                                                   statusMsg, 
                                                                   notFailedSet, 
                                                                   failedElem, 
                                                                   controllerSet_, 
                                                                   nxtController_, 
                                                                   prevLockHolder_, 
                                                                   failedSet, 
                                                                   statusResolveMsg, 
                                                                   recoveredElem, 
                                                                   controllerSet_s, 
                                                                   nxtController_s, 
                                                                   prevLockHolder, 
                                                                   eventMsg, 
                                                                   controllerSet, 
                                                                   nxtController, 
                                                                   eventID, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   subscriberOfcSet, 
                                                                   ofcID, 
                                                                   event_, 
                                                                   swSet, 
                                                                   currSW, 
                                                                   entry, 
                                                                   index, 
                                                                   event, 
                                                                   pulledNIBEventLog, 
                                                                   remainingEvents, 
                                                                   receivedEventsCopy, 
                                                                   nextToSent, 
                                                                   entryIndex, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   removeRow, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure_co, 
                                                                   isEventProcessed, 
                                                                   msg, 
                                                                   stepOfFailure, 
                                                                   controllerFailedModules >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ IF ~shouldMonitoringServerTerminate(self[1])
                                             THEN /\ isOfcEnabled[self[1]]
                                                  /\ moduleIsUp(self)
                                                  /\ switch2Controller[self[1]] # <<>>
                                                  /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                     \/ controllerGlobalLock[1] = self[1]
                                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                  /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                                     \/ controllerLocalLock[self[1]] = self
                                                  /\ controllerLocalLock' = [controllerLocalLock EXCEPT ![self[1]] = <<NO_LOCK, NO_LOCK>>]
                                                  /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                                     \/ controllerGlobalLock[1] = self[1]
                                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                  /\ controllerGlobalLock' = <<NO_LOCK, NO_LOCK>>
                                                  /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller[self[1]])]
                                                  /\ Assert(\/ /\ msg'[self].type = INSTALLED_SUCCESSFULLY
                                                               /\ msg'[self].from = IR2SW[msg'[self].IR]
                                                            \/ msg'[self].type \in {ROLE_REPLY, BAD_REQUEST}, 
                                                            "Failure of assertion at line 2444, column 9.")
                                                  /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                                        THEN /\ \E num \in 0..2:
                                                                  stepOfFailure' = [stepOfFailure EXCEPT ![self] = num]
                                                        ELSE /\ stepOfFailure' = [stepOfFailure EXCEPT ![self] = 0]
                                                  /\ IF msg'[self].type = INSTALLED_SUCCESSFULLY
                                                        THEN /\ IF (stepOfFailure'[self] # 1)
                                                                   THEN /\ FirstInstall' = [FirstInstall EXCEPT ![msg'[self].IR] = 1]
                                                                        /\ IRStatus' = [IRStatus EXCEPT ![msg'[self].IR] = IR_DONE]
                                                                   ELSE /\ TRUE
                                                                        /\ UNCHANGED << FirstInstall, 
                                                                                        IRStatus >>
                                                             /\ UNCHANGED << controllerRoleInSW, 
                                                                             roleUpdateStatus >>
                                                        ELSE /\ IF msg'[self].type = ROLE_REPLY
                                                                   THEN /\ IF (stepOfFailure'[self] # 1)
                                                                              THEN /\ IF roleUpdateStatus[self[1]][msg'[self].from].roletype = msg'[self].roletype
                                                                                         THEN /\ roleUpdateStatus' = [roleUpdateStatus EXCEPT ![self[1]][msg'[self].from].status = IR_DONE]
                                                                                         ELSE /\ TRUE
                                                                                              /\ UNCHANGED roleUpdateStatus
                                                                                   /\ controllerRoleInSW' = [controllerRoleInSW EXCEPT ![self[1]][msg'[self].from] = msg'[self].roletype]
                                                                              ELSE /\ TRUE
                                                                                   /\ UNCHANGED << controllerRoleInSW, 
                                                                                                   roleUpdateStatus >>
                                                                   ELSE /\ IF msg'[self].type = BAD_REQUEST
                                                                              THEN /\ TRUE
                                                                              ELSE /\ Assert(FALSE, 
                                                                                             "Failure of assertion at line 2467, column 13.")
                                                                        /\ UNCHANGED << controllerRoleInSW, 
                                                                                        roleUpdateStatus >>
                                                             /\ UNCHANGED << FirstInstall, 
                                                                             IRStatus >>
                                                  /\ IF (stepOfFailure'[self] # 2)
                                                        THEN /\ switch2Controller' = [switch2Controller EXCEPT ![self[1]] = Tail(switch2Controller[self[1]])]
                                                        ELSE /\ TRUE
                                                             /\ UNCHANGED switch2Controller
                                                  /\ IF (stepOfFailure'[self] # 0)
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                                  /\ UNCHANGED ofcModuleTerminationStatus
                                             ELSE /\ ofcModuleTerminationStatus' = [ofcModuleTerminationStatus EXCEPT ![self[1]][self[2]] = TERMINATE_DONE]
                                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                  /\ UNCHANGED << controllerLocalLock, 
                                                                  controllerGlobalLock, 
                                                                  FirstInstall, 
                                                                  switch2Controller, 
                                                                  controllerRoleInSW, 
                                                                  roleUpdateStatus, 
                                                                  IRStatus, 
                                                                  msg, 
                                                                  stepOfFailure >>
                                       /\ UNCHANGED << switchLock, 
                                                       sw_fail_ordering_var, 
                                                       ContProcSet, SwProcSet, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switchStatus, 
                                                       installedIRs, 
                                                       installedBy, 
                                                       swFailedNum, swNumEvent, 
                                                       NicAsic2OfaBuff, 
                                                       Ofa2NicAsicBuff, 
                                                       Installer2OfaBuff, 
                                                       Ofa2InstallerBuff, TCAM, 
                                                       controlMsgCounter, 
                                                       switchControllerRoleStatus, 
                                                       switchGeneratedEventSet, 
                                                       auxEventCounter, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       switchOrdering, 
                                                       dependencyGraph, IR2SW, 
                                                       irCounter, 
                                                       MAX_IR_COUNTER, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       workerLocalQueue, 
                                                       ofcSwSuspensionStatus, 
                                                       processedEvents, 
                                                       localEventLog, 
                                                       nibEventQueue, 
                                                       isOfcEnabled, 
                                                       setScheduledRoleUpdates, 
                                                       ofcModuleInitStatus, 
                                                       setRecoveredSwWithSlaveRole, 
                                                       fetchedIRsBeforePassingToWorker, 
                                                       eventSkipList, 
                                                       masterState, 
                                                       controllerStateNIB, 
                                                       NIBSwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       subscribeList, 
                                                       SetScheduledIRs, 
                                                       ofcFailoverStateNIB, 
                                                       NIBEventLog, ingressPkt, 
                                                       ingressIR, egressMsg, 
                                                       ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, 
                                                       controllerSet_, 
                                                       nxtController_, 
                                                       prevLockHolder_, 
                                                       failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, 
                                                       controllerSet_s, 
                                                       nxtController_s, 
                                                       prevLockHolder, 
                                                       eventMsg, controllerSet, 
                                                       nxtController, eventID, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       subscriberOfcSet, ofcID, 
                                                       event_, swSet, currSW, 
                                                       entry, index, event, 
                                                       pulledNIBEventLog, 
                                                       remainingEvents, 
                                                       receivedEventsCopy, 
                                                       nextToSent, entryIndex, 
                                                       rowIndex, rowRemove, 
                                                       removeRow, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure_co, 
                                                       notifOFC, 
                                                       isEventProcessed, 
                                                       controllerFailedModules >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)

ControllerWatchDogProc(self) == /\ pc[self] = "ControllerWatchDogProc"
                                /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                   \/ controllerGlobalLock[1] = self[1]
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ \/ controllerLocalLock[self[1]] = <<NO_LOCK, NO_LOCK>>
                                   \/ controllerLocalLock[self[1]] = self
                                /\ controllerFailedModules' = [controllerFailedModules EXCEPT ![self] = returnControllerFailedModules(self[1])]
                                /\ Cardinality(controllerFailedModules'[self]) > 0
                                /\ \E module \in controllerFailedModules'[self]:
                                     /\ Assert(controllerSubmoduleFailStat[module] = Failed, 
                                               "Failure of assertion at line 2506, column 13.")
                                     /\ controllerLocalLock' = module
                                     /\ controllerGlobalLock' = module
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
                                                swNumEvent, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchControllerRoleStatus, 
                                                switchGeneratedEventSet, 
                                                auxEventCounter, 
                                                controllerSubmoduleFailNum, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                ofcSwSuspensionStatus, 
                                                processedEvents, localEventLog, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                roleUpdateStatus, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                ofcModuleInitStatus, 
                                                setRecoveredSwWithSlaveRole, 
                                                fetchedIRsBeforePassingToWorker, 
                                                eventSkipList, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                NIBSwSuspensionStatus, 
                                                IRQueueNIB, subscribeList, 
                                                SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                NIBEventLog, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                controllerSet_, nxtController_, 
                                                prevLockHolder_, failedSet, 
                                                statusResolveMsg, 
                                                recoveredElem, controllerSet_s, 
                                                nxtController_s, 
                                                prevLockHolder, eventMsg, 
                                                controllerSet, nxtController, 
                                                eventID, toBeScheduledIRs, 
                                                nextIR, stepOfFailure_, 
                                                subscriberOfcSet, ofcID, 
                                                event_, swSet, currSW, entry, 
                                                index, event, 
                                                pulledNIBEventLog, 
                                                remainingEvents, 
                                                receivedEventsCopy, nextToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure_co, 
                                                notifOFC, isEventProcessed, 
                                                msg, stepOfFailure >>

watchDog(self) == ControllerWatchDogProc(self)

OfcFailoverNewMasterInitialization(self) == /\ pc[self] = "OfcFailoverNewMasterInitialization"
                                            /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                               \/ controllerGlobalLock[1] = self[1]
                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                            /\ SHOULD_FAILOVER = 1
                                            /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![ofc1] = FAILOVER_INIT]
                                            /\ pc' = [pc EXCEPT ![self] = "ofcFailoverCurrMasterTerminate"]
                                            /\ UNCHANGED << switchLock, 
                                                            controllerLocalLock, 
                                                            controllerGlobalLock, 
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
                                                            swNumEvent, 
                                                            NicAsic2OfaBuff, 
                                                            Ofa2NicAsicBuff, 
                                                            Installer2OfaBuff, 
                                                            Ofa2InstallerBuff, 
                                                            TCAM, 
                                                            controlMsgCounter, 
                                                            switchControllerRoleStatus, 
                                                            switchGeneratedEventSet, 
                                                            auxEventCounter, 
                                                            controllerSubmoduleFailNum, 
                                                            controllerSubmoduleFailStat, 
                                                            switchOrdering, 
                                                            dependencyGraph, 
                                                            IR2SW, irCounter, 
                                                            MAX_IR_COUNTER, 
                                                            idThreadWorkingOnIR, 
                                                            workerThreadRanking, 
                                                            workerLocalQueue, 
                                                            ofcSwSuspensionStatus, 
                                                            processedEvents, 
                                                            localEventLog, 
                                                            controllerRoleInSW, 
                                                            nibEventQueue, 
                                                            roleUpdateStatus, 
                                                            isOfcEnabled, 
                                                            setScheduledRoleUpdates, 
                                                            ofcModuleTerminationStatus, 
                                                            ofcModuleInitStatus, 
                                                            setRecoveredSwWithSlaveRole, 
                                                            fetchedIRsBeforePassingToWorker, 
                                                            eventSkipList, 
                                                            masterState, 
                                                            controllerStateNIB, 
                                                            IRStatus, 
                                                            NIBSwSuspensionStatus, 
                                                            IRQueueNIB, 
                                                            subscribeList, 
                                                            SetScheduledIRs, 
                                                            NIBEventLog, 
                                                            ingressPkt, 
                                                            ingressIR, 
                                                            egressMsg, 
                                                            ofaInMsg, 
                                                            ofaOutConfirmation, 
                                                            installerInIR, 
                                                            statusMsg, 
                                                            notFailedSet, 
                                                            failedElem, 
                                                            controllerSet_, 
                                                            nxtController_, 
                                                            prevLockHolder_, 
                                                            failedSet, 
                                                            statusResolveMsg, 
                                                            recoveredElem, 
                                                            controllerSet_s, 
                                                            nxtController_s, 
                                                            prevLockHolder, 
                                                            eventMsg, 
                                                            controllerSet, 
                                                            nxtController, 
                                                            eventID, 
                                                            toBeScheduledIRs, 
                                                            nextIR, 
                                                            stepOfFailure_, 
                                                            subscriberOfcSet, 
                                                            ofcID, event_, 
                                                            swSet, currSW, 
                                                            entry, index, 
                                                            event, 
                                                            pulledNIBEventLog, 
                                                            remainingEvents, 
                                                            receivedEventsCopy, 
                                                            nextToSent, 
                                                            entryIndex, 
                                                            rowIndex, 
                                                            rowRemove, 
                                                            removeRow, 
                                                            stepOfFailure_c, 
                                                            monitoringEvent, 
                                                            setIRsToReset, 
                                                            resetIR, 
                                                            stepOfFailure_co, 
                                                            notifOFC, 
                                                            isEventProcessed, 
                                                            msg, stepOfFailure, 
                                                            controllerFailedModules >>

ofcFailoverCurrMasterTerminate(self) == /\ pc[self] = "ofcFailoverCurrMasterTerminate"
                                        /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                           \/ controllerGlobalLock[1] = self[1]
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ ofcFailoverStateNIB[ofc1] = FAILOVER_READY
                                        /\ ofcFailoverStateNIB' = [ofcFailoverStateNIB EXCEPT ![ofc0] = FAILOVER_TERMINATE]
                                        /\ pc' = [pc EXCEPT ![self] = "ofcFailoverChangeRoles"]
                                        /\ UNCHANGED << switchLock, 
                                                        controllerLocalLock, 
                                                        controllerGlobalLock, 
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
                                                        swNumEvent, 
                                                        NicAsic2OfaBuff, 
                                                        Ofa2NicAsicBuff, 
                                                        Installer2OfaBuff, 
                                                        Ofa2InstallerBuff, 
                                                        TCAM, 
                                                        controlMsgCounter, 
                                                        switchControllerRoleStatus, 
                                                        switchGeneratedEventSet, 
                                                        auxEventCounter, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        dependencyGraph, IR2SW, 
                                                        irCounter, 
                                                        MAX_IR_COUNTER, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        workerLocalQueue, 
                                                        ofcSwSuspensionStatus, 
                                                        processedEvents, 
                                                        localEventLog, 
                                                        controllerRoleInSW, 
                                                        nibEventQueue, 
                                                        roleUpdateStatus, 
                                                        isOfcEnabled, 
                                                        setScheduledRoleUpdates, 
                                                        ofcModuleTerminationStatus, 
                                                        ofcModuleInitStatus, 
                                                        setRecoveredSwWithSlaveRole, 
                                                        fetchedIRsBeforePassingToWorker, 
                                                        eventSkipList, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        IRStatus, 
                                                        NIBSwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        subscribeList, 
                                                        SetScheduledIRs, 
                                                        NIBEventLog, 
                                                        ingressPkt, ingressIR, 
                                                        egressMsg, ofaInMsg, 
                                                        ofaOutConfirmation, 
                                                        installerInIR, 
                                                        statusMsg, 
                                                        notFailedSet, 
                                                        failedElem, 
                                                        controllerSet_, 
                                                        nxtController_, 
                                                        prevLockHolder_, 
                                                        failedSet, 
                                                        statusResolveMsg, 
                                                        recoveredElem, 
                                                        controllerSet_s, 
                                                        nxtController_s, 
                                                        prevLockHolder, 
                                                        eventMsg, 
                                                        controllerSet, 
                                                        nxtController, eventID, 
                                                        toBeScheduledIRs, 
                                                        nextIR, stepOfFailure_, 
                                                        subscriberOfcSet, 
                                                        ofcID, event_, swSet, 
                                                        currSW, entry, index, 
                                                        event, 
                                                        pulledNIBEventLog, 
                                                        remainingEvents, 
                                                        receivedEventsCopy, 
                                                        nextToSent, entryIndex, 
                                                        rowIndex, rowRemove, 
                                                        removeRow, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure_co, 
                                                        notifOFC, 
                                                        isEventProcessed, msg, 
                                                        stepOfFailure, 
                                                        controllerFailedModules >>

ofcFailoverChangeRoles(self) == /\ pc[self] = "ofcFailoverChangeRoles"
                                /\ \/ controllerGlobalLock = <<NO_LOCK, NO_LOCK>>
                                   \/ controllerGlobalLock[1] = self[1]
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ ofcFailoverStateNIB[ofc0] = FAILOVER_TERMINATE_DONE
                                /\ masterState' = [masterState EXCEPT ![ofc0] = ROLE_SLAVE,
                                                                      ![ofc1] = ROLE_MASTER]
                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << switchLock, 
                                                controllerLocalLock, 
                                                controllerGlobalLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                installedBy, swFailedNum, 
                                                swNumEvent, NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                switchControllerRoleStatus, 
                                                switchGeneratedEventSet, 
                                                auxEventCounter, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                workerLocalQueue, 
                                                ofcSwSuspensionStatus, 
                                                processedEvents, localEventLog, 
                                                controllerRoleInSW, 
                                                nibEventQueue, 
                                                roleUpdateStatus, isOfcEnabled, 
                                                setScheduledRoleUpdates, 
                                                ofcModuleTerminationStatus, 
                                                ofcModuleInitStatus, 
                                                setRecoveredSwWithSlaveRole, 
                                                fetchedIRsBeforePassingToWorker, 
                                                eventSkipList, 
                                                controllerStateNIB, IRStatus, 
                                                NIBSwSuspensionStatus, 
                                                IRQueueNIB, subscribeList, 
                                                SetScheduledIRs, 
                                                ofcFailoverStateNIB, 
                                                NIBEventLog, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                controllerSet_, nxtController_, 
                                                prevLockHolder_, failedSet, 
                                                statusResolveMsg, 
                                                recoveredElem, controllerSet_s, 
                                                nxtController_s, 
                                                prevLockHolder, eventMsg, 
                                                controllerSet, nxtController, 
                                                eventID, toBeScheduledIRs, 
                                                nextIR, stepOfFailure_, 
                                                subscriberOfcSet, ofcID, 
                                                event_, swSet, currSW, entry, 
                                                index, event, 
                                                pulledNIBEventLog, 
                                                remainingEvents, 
                                                receivedEventsCopy, nextToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, removeRow, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure_co, 
                                                notifOFC, isEventProcessed, 
                                                msg, stepOfFailure, 
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
           \/ (\E self \in ({ASYNC_NET_EVE_GEN} \X SW): asyncNetworkEventGenerator(self))
           \/ (\E self \in ({GHOST_UNLOCK_PROC} \X SW): ghostUnlockProcess(self))
           \/ (\E self \in ({rc0} \X {CONT_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}): nibEventHandler(self))
           \/ (\E self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}): ofcFailoverHandler(self))
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
        /\ \A self \in ({ASYNC_NET_EVE_GEN} \X SW) : WF_vars(asyncNetworkEventGenerator(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_vars(ghostUnlockProcess(self))
        /\ \A self \in ({rc0} \X {CONT_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({ofc0, ofc1} \X {NIB_EVENT_HANDLER}) : WF_vars(nibEventHandler(self))
        /\ \A self \in ({ofc0, ofc1} \X {FAILOVER_HANDLER}) : WF_vars(ofcFailoverHandler(self))
        /\ \A self \in ({ofc0, ofc1} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0, ofc1} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0, ofc1} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in (({ofc0, ofc1} \cup {rc0}) \X {WATCH_DOG}) : WF_vars(watchDog(self))
        /\ \A self \in ( {"proc"} \X {OFC_FAILOVER}) : WF_vars(failoverProc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3ab37b3414028eb72298924a69fce531
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
                      "ControllerThreadReleaseSemaphoreAndScheduledSet",
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
                                                 "SetScheduledIRs"}, 
                           SchedulerMechanism |-> {"SetScheduledIRs"},
                           ScheduleTheIR |-> {"IRQueueNIB"}, 
                           sendIRQueueModNotification |-> {"nibEventQueue"}, 
                           sequencerApplyFailure |-> {}, \* locked the above three into a sequence of back-to-back Ops
                           ControllerSeqStateReconciliation |-> {"SetScheduledIRs"},
                           \*************************************************************************
                           NibEventHandlerProc |-> {"ofcFailoverStateNIB",
                                                    "masterState",
                                                    "nibEventQueue",
                                                    "controllerRoleInSW"},
                           ScheduleRoleUpdateEqual |-> {"workerLocalQueue"},
                           WaitForSwitchUpdateRoleAck |-> {"subscribeList",
                                                           "IRQueueNIB",
                                                           "controllerRoleInSW"},
                           QueryIRQueueNIB |-> {"workerLocalQueue",
                                                "ofcFailoverStateNIB"},
                           WaitForRoleMaster |-> {"masterState"},
                           WaitForWorkersTermination |-> {"ofcModuleTerminationStatus"},
                           WaitForAllModulesTermination |-> {"ofcModuleTerminationStatus"},
                           \*************************************************************************
                           ControllerThread |-> {"SwSuspensionStatus",
                                                  "IRStatus"},
                           ControllerThreadRemoveQueue1 |-> {"IRQueueNIB"},
                           ControllerThreadForwardIR |-> {"controller2Switch"},
                           WaitForIRToHaveCorrectStatus |-> {"SwSuspensionStatus"},
                           ReScheduleifIRNone |-> {"IRStatus"},
                           ControllerThreadReleaseSemaphoreAndScheduledSet |-> {"idThreadWorkingOnIR",
                                                                                "SetScheduledIRs"},
                           ControllerThreadStateReconciliation |-> {"IRStatus",
                                                                    "idThreadWorkingOnIR",
                                                                    "SetScheduledIRs"},
                           \*************************************************************************
                           ControllerEventHandlerProc |-> {"SwSuspensionStatus",
                                                           "swSeqChangedStatus"},
                           getIRsToBeChecked |-> {"IRStatus"},
                           ResetAllIRs |-> {"IRStatus"},
                           ControllerEvenHanlderRemoveEventFromQueue |-> {"swSeqChangedStatus"},
                           ControllerEventHandlerStateReconciliation |-> {"SwSuspensionStatus"},
                           \*************************************************************************
                           ControllerMonitorCheckIfMastr |-> {"switch2Controller",
                                                              "IRStatus",
                                                              "roleUpdateStatus",
                                                              "controllerRoleInSw",
                                                              "switch2Controller"},
                           \*************************************************************************
                           ControllerWatchDogProc |-> {}]

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

eventProcessed(e) == \E x \in DOMAIN processedEvents: e \in processedEvents[x]

AllEventsProcessedEventually == <>[] (\A e \in 1..auxEventCounter: eventProcessed(e))

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
AllEventsAtMostOnceINV == ~\E e \in 1..auxEventCounter: /\ e \in processedEvents[ofc0]
                                                        /\ e \in processedEvents[ofc1]
=============================================================================
\* Modification History
\* Last modified Mon Mar 01 16:05:04 PST 2021 by root
\* Created Thu Dec 03 11:41:24 PST 2020 by root


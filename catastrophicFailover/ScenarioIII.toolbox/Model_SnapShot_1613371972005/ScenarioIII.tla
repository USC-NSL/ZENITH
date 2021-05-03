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
CONSTANTS ofc0, \* OFC thread identifiers
          OFC_FAILOVER

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
CONSTANTS rc0, \* RC thread identifiers
          RC_FAILOVER \* used in the RC failover process 
        
(***************************************************************************)
(******************************** Control Plane Failure ********************)
(***************************************************************************)
(***************************************************************************)       
CONSTANTS RC_OFC_NIB_FAILURE, 
          \* process name to simulate catastrophic failure (OFC+RC+NIB)
          OFC_FAILURE,
          RC_FAILURE,
          NIB_FAILURE
          
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
          \* id for NIB event handler in RC (type: model value) 
          
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
          NIBT_IR_QUEUE,
          NIBT_IR_STATUS,
          NIBT_FIRST_INSTALL

(***************************************************************************)
(*********************** NIB MODULES IDs ****************************)
(***************************************************************************)
CONSTANTS CONT_NIB_OFC_EVENT,
          \* id for OFC event handler in NIB (type: model value) 
          CONT_NIB_RC_EVENT,
          \* id for RC event handler in NIB (type: model value) 
          CONT_NIB_FAILOVER
          
          
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
          Failed,
          InReconciliation           

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
              FirstInstallOFC = [x \in 1..MaxNumIRs |-> 0],
              FirstInstallNIB = [x \in 1..MaxNumIRs |-> 0],
              sw_fail_ordering_var = SW_FAIL_ORDERING,
              ContProcSet = (({rc0} \X {CONT_SEQ}))\cup (({rc0} \X {CONT_RC_NIB_EVENT})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) 
                            \cup (({ofc0} \X {CONT_OFC_NIB_EVENT}))
                            \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))
                            \cup (({nib0} \X {CONT_NIB_RC_EVENT}))
                            \cup (({nib0} \X {CONT_NIB_OFC_EVENT})),
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
              controllerSubmoduleFailNum = [x \in {ofc0, rc0, nib0} |-> 0],
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
              \* used by the NIB event handler to notify sequencer to recompute tobescheduled-IRs
              NIBUpdateForRC = FALSE,
              \* Copy of NIB states at RC
              controllerStateRC = [x \in ContProcSet |-> [type |-> NO_STATUS]], 
              IRStatusRC = [x \in 1..MaxNumIRs |-> IR_NONE],
              IRQueueRC = <<>>,
              SwSuspensionStatusRC = [x \in SW |-> SW_RUN],
              SetScheduledIRsRC = [y \in SW |-> {}],
              FlagRCNIBEventHandlerFailover = FALSE,
              FlagRCSequencerFailover = FALSE,
              RC_READY = FALSE,
              
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
              \* Copy of NIB states at OFC
              controllerStateOFC = [x \in ContProcSet |-> [type |-> NO_STATUS]], 
              IRStatusOFC = [x \in 1..MaxNumIRs |-> IR_NONE],
              IRQueueOFC = <<>>,
              SwSuspensionStatusOFC = [x \in SW |-> SW_RUN],
              SetScheduledIRsOFC = [y \in SW |-> {}],
              FlagOFCWorkerFailover = FALSE,
              FlagOFCMonitorFailover = FALSE,
              FlagOFCNIBEventHandlerFailover = FALSE,
              \* This assumes that there is only one worker thread
              OFCThreadID = <<ofc0,CHOOSE x \in CONTROLLER_THREAD_POOL : TRUE>>,
               \* used during catastrophic failure
              OFC_READY = FALSE;

              (********************* NIB Vars *****************************)
              (********************* Message format ***********************)
              (********************* NIB transactions *********************)
              (* <<[op |-> Read, key|-> IR, value|-> IR_DONE],  []>>      *)
              (************************************************************)
              \************** Message queues ****************
              \* used by OFC (NIB) to receive (send) messages
              \* currently, NIB2OFC = IRQueueNIB
              NIB2OFC = <<>>,
              \* used by RC (NIB) to receive messages
              NIB2RC = <<>>,
              \* used by NIB (RC and OFC) to receive messages
              X2NIB = <<>>,
              OFC2NIB = <<>>,
              RC2NIB = <<>>,
              FlagNIBFailover = FALSE,
              FlagNIBRCEventhandlerFailover = FALSE,
              FlagNIBOFCEventhandlerFailover = FALSE,
              \* used during catastrophic failover
              NIB_READY_FOR_RC = FALSE;
              \* used during catastrophic failover
              NIB_READY_FOR_OFC = FALSE;
              
           
              \********************** Tables *************************************
              masterState = [ofc0 |-> "primary", rc0 |-> "primary"],
              controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]],
              IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
              SwSuspensionStatus = [x \in SW |-> SW_RUN],
              IRQueueNIB = <<>>,
              \* notificationNIB = [y \in {c0, c1} |-> [RCS |-> [IRQueueNIB |-> <<>>]]], 
              SetScheduledIRs = [y \in SW |-> {}],
              \* @Pooria, consider moving this variable to RC
              (*************** Debug Vars ***********************)
              X2NIB_len = 0,
              \********************** Control plane threads *************************************
              NIBThreadID = <<nib0, CONT_NIB_RC_EVENT>>,
              RCThreadID = <<rc0, CONT_SEQ>>,
\*              OFCThreadID = <<ofc0, CONTROLLER_THREAD_POOL[0]>>
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
                                                      
        (************************* Controller functions ********************************)                              
        moduleIsUp(threadID) == controllerSubmoduleFailStat[threadID] = NotFailed
        controllerIsMaster(controllerID) == CASE controllerID = rc0 -> masterState.rc0 = "primary"
                                              [] controllerID = ofc0 -> masterState.ofc0 = "primary"
        getMaxNumSubModuleFailure(controllerID) == CASE controllerID = rc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.rc0
                                                     [] controllerID = ofc0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.ofc0 
                                                     [] controllerID = nib0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.nib0 
        \* This function is to check if the whole OFC is up, not individual modules inside OFC
        \* This function assumes that there is only one worker at OFC
\*        /\ controllerSubmoduleFailStat[<<ofc0,CONT_EVENT>>] = NotFailed
        isOFCUp(threadID) == /\ controllerSubmoduleFailStat[OFCThreadID] = NotFailed 
                             /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = NotFailed  
                             /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = NotFailed     
        isOFCFailed(threadID) == /\ controllerSubmoduleFailStat[OFCThreadID] = Failed 
                             /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = Failed          
                             /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = Failed
        isOFCReconciliation(threadID) == /\ controllerSubmoduleFailStat[OFCThreadID] = InReconciliation 
                             /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = InReconciliation          
                             /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = InReconciliation  
        
                                                 
        (****************************** NIB functions **********************************)
        \* The following four expression help using tagged buffer in NIB
        \* Please see modifiedRead, modifiedWrite, modifiedRemove
        NoEntryTaggedWith(threadID, IRQueue) == ~\E x \in rangeSeq(IRQueue): x.tag = threadID 
        FirstUntaggedEntry(num, IRQueue) == ~\E x \in DOMAIN IRQueue: /\ IRQueue[x].tag = NO_TAG
                                                                                /\ x < num
\*        getFirstIRIndexToRead(threadID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: \/ IRQueue[x].tag = threadID
\*                                                                           \/ /\ NoEntryTaggedWith(threadID, IRQueue)
\*                                                                              /\ FirstUntaggedEntry(x, IRQueue)
\*                                                                              /\ IRQueue[x].tag = NO_TAG
        getFirstIRIndexToRead(threadID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: TRUE                                                                     
\*        getFirstIndexWith(RID, threadID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: /\ IRQueue[x].tag = threadID
\*                                                                            /\ IRQueue[x].IR = RID
        getFirstIndexWith(RID, threadID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: IRQueue[x].IR = RID                                                                    
        getFirstIndexWithNIB(RID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: IRQueue[x].IR = RID
        isNIBUp(threadID) == controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
                             controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed 
        isNIBFailed(threadID) == controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = Failed /\
                             controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = Failed                                                                  
        isNIBReconciliation(threadID) == controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = InReconciliation /\
                             controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = InReconciliation                                                          
        (****************** RC (routing controller) **************************)
        \*************************** Sequencer *******************************
        isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                             /\ IRStatus[y] # IR_DONE
        isDependencySatisfiedRC(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                             /\ IRStatusRC[y] # IR_DONE                                                     
        getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                                  /\ isDependencySatisfied(x)
                                                                  /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRs[IR2SW[x]]}
\*                                                                  \*/\ idThreadWorkingOnIR[x] = IR_UNLOCK}
        getSetIRsCanBeScheduledNextRC(CID)  == {x \in 1..MaxNumIRs: /\ IRStatusRC[x] = IR_NONE
                                                                  /\ isDependencySatisfiedRC(x)
                                                                  /\ SwSuspensionStatusRC[IR2SW[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRsRC[IR2SW[x]]}                                                          
        removeInstalledIR(IRSet) == IF IRSet = {} 
                                    THEN IRSet
                                    ELSE {ir \in IRSet: IRStatusRC[ir] # IR_DONE}
        isRCFailed(id) == controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = Failed
                    /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed
        isRCUp(id) == controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = NotFailed
                    /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
        isRCReconciliation(id) == controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = InReconciliation
                    /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = InReconciliation
        (****************** OFC (openflow controller) ************************)
        \*************************** Workers *********************************
        isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
        \* following four expressions used for verification optimization reasons
        \* between all the threads attempting to get the IR, the one with lowest 
        \* id always gets it. 
        setFreeThreads(CID, IRQueue) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>, IRQueue)
                                                              /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}        
        printIRQueue(IRQueue) == IRQueue
        canWorkerThreadContinue(CID, threadID, IRQueue) == \/ \E x \in rangeSeq(IRQueue): x.tag = threadID
                                                  \/ /\ \E x \in rangeSeq(IRQueue): x.tag = NO_TAG 
                                                     /\ NoEntryTaggedWith(threadID, IRQueue) 
                                                     /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID, IRQueue)})
        \* TODO(@mingyang): check with Pooria
\*        setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
\*                                                                                                                        /\ y.tag = <<CID, x>>
\*                                                                                         /\ pc[<<CID, x>>] = "ControllerThread"}
        setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
                                                                                                                        /\ y.tag = <<CID, x>>}                                                                                 
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
    
    \* ===== Copy NIB states =========
    macro updateIRQueueAtOFC()
    begin
\*        controllerStateOFC := NIBMsg.value.controllerStateNIB;
        IRQueueOFC := NIBMsg.value.IRQueueNIB;
\*        SetScheduledIRsOFC := NIBMsg.value.SetScheduledIRsNIB;
    end macro;
    \* ===== Sending the entry =========
    (*******************************************************************)
    (*                          RC Macros                              *)
    (*******************************************************************)
    macro copyEntireNIB2RC()
    begin
        \* Since RC is the authority for SetScheduledIRs, RC should not need to query
        \* SetScheduledIRs from NIB (only during reconciliation).
\*        controllerStateRC := NIBMsg.value.controllerStateNIB;
        IRStatusRC := NIBMsg.value.IRStatusNIB;
        IRQueueRC := NIBMsg.value.IRQueueNIB;
        SwSuspensionStatusRC := NIBMsg.value.SwSuspensionStatusNIB;
    end macro;
    
    macro RCRemoveIRFromScheduledSet()
    begin
        SetScheduledIRsRC := [sw \in SW |-> IF SetScheduledIRsRC[sw] = {}
                                            THEN SetScheduledIRsRC[sw]
                                            ELSE {ir \in SetScheduledIRsRC[sw]: 
                                                    IRStatusRC[ir] # IR_DONE}];
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
    
    macro modifiedRead(IRQueue)
    begin
        rowIndex := getFirstIRIndexToRead(self, IRQueue);
        nextIRToSent := IRQueue[rowIndex].IR;
        IRQueue[rowIndex].tag := self;
    end macro;
    
    macro NIBStateCopy()
    begin
\*        value := [controllerStateNIB |-> controllerStateNIB, 
\*                        IRStatusNIB |-> IRStatus, 
\*                        IRQueueNIB |->IRQueueNIB,
\*                        SetScheduledIRsNIB |-> SetScheduledIRs, 
\*                        SwSuspensionStatusNIB |-> SwSuspensionStatus];
        value := [IRStatusNIB |-> IRStatus, 
                        IRQueueNIB |->IRQueueNIB,
                        SetScheduledIRsNIB |-> SetScheduledIRs, 
                        SwSuspensionStatusNIB |-> SwSuspensionStatus];
    end macro;
    
    macro prepareIRTransaction()
    begin
        assert nextTrans.ops[1].table = NIBT_CONTROLLER_STATE;
        assert Len(nextTrans.ops[1].key) = 2;
        controllerStateNIB[nextTrans.ops[1].key] := nextTrans.ops[1].value;
        assert nextTrans.ops[2].table = NIBT_SET_SCHEDULED_IRS;
        SetScheduledIRs[nextTrans.ops[2].key] := nextTrans.ops[2].value;
    end macro;
    
    macro scheduleIRTransaction()
    begin
        assert nextTrans.ops[1].table = NIBT_IR_QUEUE;
        IRQueueNIB := Append(IRQueueNIB, nextTrans.ops[1].value);
        assert nextTrans.ops[2].table = NIBT_CONTROLLER_STATE;
        assert Len(nextTrans.ops[2].key) = 2;
        controllerStateNIB[nextTrans.ops[2].key] := nextTrans.ops[2].value;
    end macro;
    
    macro ScheduleIRInOneStepTransaction()
    begin
        assert nextTrans.ops[1].table = NIBT_IR_QUEUE;
        IRQueueNIB := Append(IRQueueNIB, nextTrans.ops[1].value);
    end macro;
    
    
    macro getSetIRsCanBeScheduledNextTransaction()
    begin
        value := getSetIRsCanBeScheduledNext(self[1]);
    end macro;
    
    macro NIBProcessTransaction()
    begin
        if (nextTrans.name = "PrepareIR") then \* submitted by the Sequencer in RC 
            prepareIRTransaction();
        elsif (nextTrans.name = "ScheduleIR") then \* submitted by the Sequencer in RC 
            scheduleIRTransaction();
            NIBStateCopy();
            send_NIB_back := "NIB2OFC";
        elsif (nextTrans.name = "RCScheduleIRInOneStep") then \* submitted by the simplified Sequencer in RC 
            ScheduleIRInOneStepTransaction();
            NIBStateCopy();
            send_NIB_back := "NIB2OFC";
        elsif (nextTrans.name = "SeqReadNIBStates") then \* submitted by the Sequencer in RC 
            NIBStateCopy();
            send_NIB_back := "NIB2RC";
        elsif (nextTrans.name = "OFCOverrideIRStatus") then
            IRStatus := nextTrans.ops[1];
            FirstInstallNIB := nextTrans.ops[2];
            NIBStateCopy();
            send_NIB_back := "NIB2RC";
        elsif (nextTrans.name = "OFCReadNIBStates") then
                NIBStateCopy();
                send_NIB_back := "NIB2OFC";
        elsif (nextTrans.name = "UpdateControllerState") then
                assert nextTrans.ops[1].table = NIBT_CONTROLLER_STATE;
                assert Len(nextTrans.ops[1].key) = 2;
                controllerStateNIB[nextTrans.ops[1].key] := nextTrans.ops[1].value;
        elsif (nextTrans.name = "RemoveIR") then \* OFC sent this transaction
                assert nextTrans.ops[1].table = NIBT_IR_QUEUE;
                IR2Remove := nextTrans.ops[1].key;
                \* it is possible that IR has been deleted by RC during NIB reconciliation
                if \E i \in DOMAIN IRQueueNIB: IRQueueNIB[i].IR = IR2Remove then
                    rowRemove := getFirstIndexWithNIB(IR2Remove, IRQueueNIB);
                    IRQueueNIB := removeFromSeq(IRQueueNIB, rowRemove);
                end if;
        elsif (nextTrans.name = "OFCChangeIRStatus2Sent") then \* submitted by the worker in OFC
                assert nextTrans.ops[1].table = NIBT_IR_STATUS;
                assert Len(nextTrans.ops) = 1;
                IRStatus[nextTrans.ops[1].key] := nextTrans.ops[1].value;
                NIBStateCopy();
                send_NIB_back := "NIB2RC";
        elsif (nextTrans.name = "ChangeSetScheduledIRs") then
                assert nextTrans.ops[1].table = NIBT_SET_SCHEDULED_IRS;
                assert Len(nextTrans.ops) = 1;
                SetScheduledIRs[nextTrans.ops[1].key] := nextTrans.ops[1].value;
        elsif (nextTrans.name = "UpdateIRTag") then
                assert nextTrans.ops[1].table = NIBT_IR_QUEUE;
                assert Len(nextTrans.ops) = 1;
                assert Len(IRQueueNIB) > 0;
                IRIndex := CHOOSE x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans.ops[1].key;
                assert IRIndex # -1;
                IRQueueNIB[IRIndex].tag := nextTrans.ops[1].value;
        elsif (nextTrans.name = "FirstInstallIR") then \* submitted by the monitor server in OFC 
                assert Len(nextTrans.ops) = 2;
                assert nextTrans.ops[1].table = NIBT_IR_STATUS;
                IRStatus[nextTrans.ops[1].key] := nextTrans.ops[1].value;
                assert nextTrans.ops[2].table = NIBT_FIRST_INSTALL;
                FirstInstallNIB[nextTrans.ops[2].key] := nextTrans.ops[2].value;
                NIBStateCopy();
                send_NIB_back := "NIB2RC";
        end if;
    end macro;
    
    macro modifiedRemove(IRQueue)
    begin
        rowRemove := getFirstIndexWith(nextIRToSent, self, IRQueue);
        IRQueueNIB := removeFromSeq(IRQueueNIB, rowRemove);
        \*notificationNIB[self[1]].RCS.IRQueueNIB := Append(notificationNIB[self[1]].RCS.IRQueueNIB, 
        \*                                                    [type |-> NIB_DELETE, IR |-> nextIRToSent]);
    end macro;
    \* =================================
    
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
        \* Switch check if OFC is up; if not wait until it is up
        \* Why do we allow isOFCFailed()?
        \* This is to create the failure detection delay at sw side.
        \* This can simulate the scenario where switch detects OFC failure 
        \* after OFC has failed some time.
        await isOFCUp(OFCThreadID) \/ isOFCFailed(OFCThreadID);
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
    (********************** Network Information Base *******************)
    (*******************************************************************)
    \* ============ NIB event handler for RC ==========
\*    fair process NIBRCEventHandler \in ({nib0} \X {CONT_NIB_RC_EVENT})
\*    variables nextTrans = [name |-> ""], value = NULL, rowRemove=0,
\*              IR2Remove = 0, send_NIB_back = "", stepOfFailure = 0,
\*              IRIndex = -1, debug = -1;
\*    begin
\*    NIBEventHandling:
\*    while TRUE do
\*        NIBDequeueTransaction:
\*        if moduleIsUp(self) then
\*            await X2NIB # <<>>;
\*            nextTrans := Head(X2NIB);
\*            X2NIB := Tail(X2NIB);
\*        else
\*            FlagNIBFailover := TRUE;
\*            goto NIBReconciliation;
\*        end if; 
\*        
\*        NIBProcessTransaction:   
\*        if moduleIsUp(self) then
\*            NIBProcessTransaction();
\*            debug := 0;
\*        else
\*            FlagNIBFailover := TRUE;
\*            goto NIBReconciliation;
\*        end if; 
\*            
\*        NIBSendBackIfAny:   
\*        if moduleIsUp(self) then
\*            if send_NIB_back = "NIB2RC" then
\*                await isRCUp(RCThreadID);
\*                NIB2RC := Append(NIB2RC, [value |-> value]);
\*            elsif send_NIB_back = "NIB2OFC" then
\*                await isOFCUp(RCThreadID);
\*                NIB2OFC := Append(NIB2OFC, [value |-> value]);    
\*            end if;
\*            send_NIB_back := "";
\*        else
\*            FlagNIBFailover := TRUE;
\*            goto NIBReconciliation;
\*        end if;             
\*    end while;
\*    
\*    \* Think about if we need to make X2NIB empty for failover
\*    NIBReconciliation:
\*        \* Change the mode of the NIB to InReconciliation (failover), 
\*        \* which means that it is not ready to accept/process any message transactions
\*        controllerSubmoduleFailStat[self] := InReconciliation;
\*        await FlagRCNIBEventHandlerFailover;
\*        \* NIB should start from empty states
\*        NIB2RC := <<>>;
\*        NIB2OFC := <<>>;
\*        X2NIB := <<>>;
\*        send_NIB_back := "";
\*        
\*        NIBFailoverReadOFC:
\*            await OFC_READY \/ isOFCUp(OFCThreadID);
\*            \* Read OFC states: get up-to-date data plane states
\*            IRStatus := IRStatusOFC;
\*            SwSuspensionStatus := SwSuspensionStatusOFC;
\*            \* Make NIB ready for RC to ready data plane states
\*            NIB_READY_FOR_RC := TRUE;
\*        
\*        NIBFailoverReadRC:
\*            await RC_READY \/ isRCUp(RCThreadID);
\*            IRQueueNIB := IRQueueRC;
\*            SetScheduledIRs := SetScheduledIRsRC; 
\*            NIB_READY_FOR_OFC := TRUE;        
\*        
\*        ChangeNIBStatusToNormal:
\*           controllerSubmoduleFailStat[self] := NotFailed;
\*           NIBStateCopy();  
\*           NIB2RC := Append(NIB2RC, [value |-> value]);
\*           NIB2OFC := Append(NIB2OFC, [value |-> value]);
\*           goto NIBEventHandling;      
\*    end process
    
    
    \* ======== NIB failover =====
    \*
    fair process NIBFailoverProc \in ({"proc"} \X {CONT_NIB_FAILOVER})
    variables value = NULL;
    begin 
        \* Change the mode of the NIB to InReconciliation (failover), 
        \* which means that it is not ready to accept/process any message transactions
        NIBFailoverResetStates:
        await controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = Failed /\
                    controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = Failed;
        controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] := InReconciliation ||
        controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] := InReconciliation;
        await FlagNIBOFCEventhandlerFailover /\ FlagNIBRCEventhandlerFailover;
        \* NIB should start from empty states
        NIB2RC := <<>>;
        NIB2OFC := <<>>;
\*        X2NIB := <<>>;
        OFC2NIB := <<>>;
        RC2NIB := <<>>;
        
        NIBFailoverReadOFC:
            await OFC_READY \/ isOFCUp(OFCThreadID);
            \* Read OFC states: get up-to-date data plane states
            IRStatus := IRStatusOFC;
            SwSuspensionStatus := SwSuspensionStatusOFC;
            \* Make NIB ready for RC to ready data plane states
            NIB_READY_FOR_RC := TRUE;
        
        NIBFailoverReadRC:
            await RC_READY \/ isRCUp(RCThreadID);
            IRQueueNIB := IRQueueRC;
            SetScheduledIRs := SetScheduledIRsRC; 
            NIB_READY_FOR_OFC := TRUE;        
        
        ChangeNIBStatusToNormal:
           controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] := NotFailed ||
           controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] := NotFailed;
           NIBStateCopy();  
           NIB2RC := Append(NIB2RC, [value |-> value]);
           NIB2OFC := Append(NIB2OFC, [value |-> value]);
    end process    
    \* ==========================
    
    \* ============ NIB event handler for RC ==========
    fair process NIBRCEventHandler \in ({nib0} \X {CONT_NIB_RC_EVENT})
    variables nextTrans = [name |-> ""], value = NULL, rowRemove=0,
              IR2Remove = 0, send_NIB_back = "", stepOfFailure = 0,
              IRIndex = -1, debug = -1;
    begin
    NIBHandleRCTransactions:
    while TRUE do
        NIBDequeueRCTransaction:
        send_NIB_back := "";
        if moduleIsUp(self) then
            await RC2NIB # <<>>;
            nextTrans := Head(RC2NIB);
            RC2NIB := Tail(RC2NIB);
        else
            FlagNIBRCEventhandlerFailover := TRUE;
            goto NIBForRCReconciliation;
        end if; 
        
        NIBProcessRCTransaction:   
        if moduleIsUp(self) then
            NIBProcessTransaction();
            debug := 0;
        else
            FlagNIBRCEventhandlerFailover := TRUE;
            goto NIBForRCReconciliation;
        end if; 
            
        NIBUpdateRCIfAny:   
        if moduleIsUp(self) then
            if send_NIB_back = "NIB2RC" then
                await isRCUp(RCThreadID) \/ isRCFailed(RCThreadID);
                NIB2RC := Append(NIB2RC, [value |-> value]);
            elsif send_NIB_back = "NIB2OFC" then
                await isOFCUp(RCThreadID) \/ isOFCFailed(RCThreadID);
                NIB2OFC := Append(NIB2OFC, [value |-> value]);    
            end if;
            send_NIB_back := "";
        else
            FlagNIBRCEventhandlerFailover := TRUE;
            goto NIBForRCReconciliation;
        end if;             
    end while;
    
    \* Think about if we need to make X2NIB empty for failover
    NIBForRCReconciliation:
        controllerWaitForLockFree();
        await controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
              controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed;
        goto NIBHandleRCTransactions;      
    end process
    
    \* ============ NIB event handler for OFC ==========
    fair process NIBOFCEventHandler \in ({nib0} \X {CONT_NIB_OFC_EVENT})
    variables nextTrans = [name |-> ""], value = NULL, rowRemove=0,
              IR2Remove = 0, send_NIB_back = "", stepOfFailure = 0,
              IRIndex = -1, debug = -1;
    begin
    NIBHandleOFCTransactions:
    while TRUE do
        NIBDequeueOFCTransaction:
        send_NIB_back := "";
        if moduleIsUp(self) then
            await OFC2NIB # <<>>;
            nextTrans := Head(OFC2NIB);
            OFC2NIB := Tail(OFC2NIB);
        else
            FlagNIBOFCEventhandlerFailover := TRUE;
            goto NIBForOFCReconciliation;
        end if; 
        
        NIBProcessTransaction:   
        if moduleIsUp(self) then
            NIBProcessTransaction();
            debug := 0;
        else
            FlagNIBOFCEventhandlerFailover := TRUE;
            goto NIBForOFCReconciliation;
        end if; 
            
        NIBSendBackIfAny:   
        if moduleIsUp(self) then
            if send_NIB_back = "NIB2RC" then
                await isRCUp(RCThreadID) \/ isRCFailed(RCThreadID);
                NIB2RC := Append(NIB2RC, [value |-> value]);
            elsif send_NIB_back = "NIB2OFC" then
                await isOFCUp(RCThreadID) \/ isOFCFailed(RCThreadID);
                NIB2OFC := Append(NIB2OFC, [value |-> value]);    
            end if;
            send_NIB_back := "";
        else
            FlagNIBOFCEventhandlerFailover := TRUE;
            goto NIBForOFCReconciliation;
        end if;             
    end while;
    
    \* Think about if we need to make X2NIB empty for failover
    NIBForOFCReconciliation:
        controllerWaitForLockFree();
        await controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
              controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed;
        goto NIBHandleOFCTransactions;            
    end process
    
    
    \* ======== RC failover =====
    \*
    fair process RCFailoverProc \in ({"proc"} \X {RC_FAILOVER})
    begin 
        RCFailoverResetStates:
            controllerWaitForLockFree();
            \* LSF (Logic for simulating failures)
            \* step 1
            await controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = Failed /\
                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed;
            controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] := InReconciliation ||
            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] := InReconciliation;
            \* step 2: make sure modules in RC fail together
            await FlagRCNIBEventHandlerFailover /\ FlagRCSequencerFailover;
            \* step 3: Clear old messages sent to the old RC
            NIB2RC := <<>>;
            \* step 4: empty local tables
            SetScheduledIRsRC := [y \in SW |-> {}];
            IRQueueRC := <<>>;
            \* step 5: make RC unready
            RC_READY := FALSE;
            
            RCReadNIB:
                \* RC reads from NIB assuming that NIB has a dedicated thread for RC failover
                \* such that RC can get NIB tables immediately
                await NIB_READY_FOR_RC \/ isNIBUp(NIBThreadID);
                IRStatusRC := IRStatus;
                SwSuspensionStatusRC := SwSuspensionStatus;
                RC_READY := TRUE;
                
\*            RCRecomputeIRQueue
\*                \* Since NIB knows that RC fails, at current moment, OFC is the authority for IRQueue
\*\*                IRQueueRC := IRQueueNIB;
\*                RC_READY := TRUE;
                
            
            \* Change RC status to up
            RCBack2Normal:
            controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] := NotFailed ||
            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] := NotFailed;
            NIBUpdateForRC := TRUE;
    end process    
    \* ==========================
    
    \* ============ RC NIB Event Handler ==========
    fair process RCNIBEventHandler \in ({rc0} \X {CONT_RC_NIB_EVENT})
    variables NIBMsg = [value |-> [x |-> <<>>]], isBootStrap = TRUE;
    begin
    RCNIBEventHanderProc:
        while TRUE do
            controllerWaitForLockFree();
            if isRCFailed(self) then
                FlagRCNIBEventHandlerFailover := TRUE;
                goto RCNIBEventHandlerFailover;
            else
                \* NIB failure detection modeling:
                \* Since NIB failure and reconciliation are in two steps
                \* between which RC can continue to work, which models the delayed failure detection. 
                \* In the reconciliation step, NIB2RC is set to <<>> to model 
                \* that RC should discard all msgs from the old NIB master.
                \* So after the reconciliation step, RC will be blocked since no msg to be processed at RC.
                \* So we do not need an explicit failure detection here.
                await NIB2RC # <<>>;
                NIBMsg := Head(NIB2RC);
                NIB2RC := Tail(NIB2RC);
                if isBootStrap = TRUE then
                    IRStatusRC := [x \in 1..MaxNumIRs |-> IR_NONE];
                    IRQueueRC := <<>>;
                    SetScheduledIRsRC := [y \in SW |-> {}];
\*                    IRStatusRC := NIBMsg.value.IRStatusNIB;
\*                    IRQueueRC := NIBMsg.value.IRQueueNIB;
                    SwSuspensionStatusRC := NIBMsg.value.SwSuspensionStatusNIB;
                    \* SetScheduledIRsRC is as initialized
                    NIBUpdateForRC := TRUE;
                    isBootStrap := FALSE;
                \* If local and remote tables are different
                elsif IRStatusRC # NIBMsg.value.IRStatusNIB 
                    \/ SwSuspensionStatusRC # NIBMsg.value.SwSuspensionStatusNIB then
                    \* update RC locally
                    IRStatusRC := NIBMsg.value.IRStatusNIB;
                    SwSuspensionStatusRC := NIBMsg.value.SwSuspensionStatusNIB;
                    \* remove DONE IR from SetScheduledIRsRC
                    SetScheduledIRsRC := [sw \in SW |-> IF SetScheduledIRsRC[sw] = {}
                                            THEN SetScheduledIRsRC[sw]
                                            ELSE {ir \in SetScheduledIRsRC[sw]: 
                                                    IRStatusRC[ir] # IR_DONE}];
                    \* remove DONE IR from IRQueueRC
                    IRQueueRC := SelectSeq(IRQueueRC, LAMBDA i: IRStatusRC[i.IR] # IR_DONE);
                    NIBUpdateForRC := TRUE;
                end if;
            end if;
        end while;    
    RCNIBEventHandlerFailover:
        controllerWaitForLockFree();
        await controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = NotFailed /\
                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed;
        isBootStrap := FALSE;
        goto RCNIBEventHanderProc;
    end process
 
    
    \* ============ Simplified Sequencer ==========
    \* Sequencer periodically gets all the valid IRs (those with satisfied
    \* dependencies), run its scheduling mechanism to decide the order of
    \* scheduling and then, schedule the IR
    fair process controllerSequencer \in ({rc0} \X {CONT_SEQ})
    variables toBeScheduledIRs = {}, key = "", op1 = [table |-> ""], 
                op2 = [table |-> ""],
                transaction = <<>>, 
                nextIR = 0, stepOfFailure = 0;
    begin
    \* Read states from NIB
    RCSendReadTransaction:
            \* RC needs NIB to 1) notify OFC and 2) get IRStatus
            \* Therefore, if NIB is Failed, RC will stop scheduling new IRs
        controllerWaitForLockFree();
        if isRCFailed(self) then
           FlagRCSequencerFailover := TRUE;
           goto RCSequencerFailover;
        else
            await isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID);
            transaction := [name |-> "SeqReadNIBStates"];
            RC2NIB := RC2NIB \o <<transaction>>;
        end if;
        
    SequencerProc:
    while TRUE do    
        controllerWaitForLockFree();
        \* ControlSeqProc consists of one operation;
        \* 1) Retrieving the set of valid IRs
        await controllerIsMaster(self[1]);
\*        await moduleIsUp(self);
        if isRCFailed(self) then
           FlagRCSequencerFailover := TRUE;
           goto RCSequencerFailover;
        end if;
        
        RCComputeNextIR2Schedule:
            controllerWaitForLockFree();
            if isRCFailed(self) then
                FlagRCSequencerFailover := TRUE;
                goto RCSequencerFailover;
            else
                await NIBUpdateForRC;
                toBeScheduledIRs := getSetIRsCanBeScheduledNextRC(self[1]);
                NIBUpdateForRC := FALSE;
                if toBeScheduledIRs = {} then
                    goto RCComputeNextIR2Schedule;
                end if;
           end if;
        
        SchedulerMechanism:
        while TRUE do \* while toBeScheduledIRs # {} do
            controllerWaitForLockFree();
            if isRCFailed(self) then
                FlagRCSequencerFailover := TRUE;
                goto RCSequencerFailover;
            else
                nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                SetScheduledIRsRC[IR2SW[nextIR]] := SetScheduledIRsRC[IR2SW[nextIR]] \cup {nextIR};
                toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                IRQueueRC := Append(IRQueueRC, [IR |-> nextIR, tag |-> NO_TAG]);
            end if;     
            
            \* Send RCScheduleIRInOneStep transaction to NIB
            RCSendPrepareIR2NIB:
            controllerWaitForLockFree();
            if isRCFailed(self) then
                FlagRCSequencerFailover := TRUE;
                goto RCSequencerFailover;
            else
                await isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID);
                op1 := [table |-> NIBT_IR_QUEUE, key |-> NULL, value |-> [IR |-> nextIR, tag |-> NO_TAG]];
                transaction := [name |-> "RCScheduleIRInOneStep", ops |-> <<op1>>];
                RC2NIB := RC2NIB \o <<transaction>>;  
            
                if toBeScheduledIRs = {} then
                    goto SequencerProc;
                end if;
            end if;             
        end while;                                                
    end while;
    
    \* TODO(@mingyang): change the following to transactions. Since we do not consider failures now,
    \* below logic will not be triggered for now.
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
        goto SequencerProc;
        
    RCSequencerFailover:
        controllerWaitForLockFree();
        toBeScheduledIRs := {};
        await controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = NotFailed /\
                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed;
        goto SequencerProc;
    
    end process
    
    
    (*******************************************************************)
    (*                     OFC (OpenFlow Controller)                   *)
    (*******************************************************************)
    
    (*******************************************************************)
    (*                      Catastrophic failure                            *)
    (*******************************************************************)  
    \* ======== OFC + NIB + RC failure =====
\*    fair process ControlPlaneFailureProc \in ( {"proc"} \X {RC_OFC_NIB_FAILURE})
\*    begin 
\*        CatastrophicFailure:
\*            controllerWaitForLockFree();
\*            controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] := Failed ||
\*            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] := Failed ||
\*            controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] := Failed ||
\*            controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] := Failed ||
\*            controllerSubmoduleFailStat[OFCThreadID] := Failed ||
\*            controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] := Failed ||
\*            controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] := Failed;        
\*    end process    
    \* ==========================
    
    \* ======== OFC failure =====
    fair process OFCFailureProc \in ( {"proc"} \X {OFC_FAILURE})
    begin 
        OFCFailure:
            controllerWaitForLockFree();
            controllerSubmoduleFailStat[OFCThreadID] := Failed ||
            controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] := Failed ||
            controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] := Failed;        
    end process    
    \* ==========================
    
    \* ======== NIB failure =====
\*    fair process NIBFailureProc \in ( {"proc"} \X {NIB_FAILURE})
\*    begin 
\*        NIBFailure:
\*            controllerWaitForLockFree();
\*            controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] := Failed ||
\*            controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] := Failed;        
\*    end process    
    \* ==========================
    
    \* ======== RC failure =====
\*    fair process RCFailureProc \in ( {"proc"} \X {RC_FAILURE})
\*    begin 
\*        RCFailure:
\*            controllerWaitForLockFree();
\*             controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] := Failed ||
\*            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] := Failed;      
\*    end process    
    \* ==========================
    
    \* ======== OFC failover =====
    \*
    fair process OFCFailoverProc \in ({"proc"} \X {OFC_FAILOVER})
    variables transaction = <<>>, IRQueueTmp = <<>>;
    begin 
        OFCFailoverResetStates:
            controllerWaitForLockFree();
            \* LSF (Logic for simulating failures)
            \* step 1
            await controllerSubmoduleFailStat[OFCThreadID] = Failed 
                    /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = Failed
                    /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = Failed;
                    
            controllerSubmoduleFailStat[OFCThreadID] := InReconciliation ||
            controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] := InReconciliation ||
            controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] := InReconciliation;
            
            \* step 2: make sure modules in OFC fail together
            await FlagOFCNIBEventHandlerFailover /\ FlagOFCMonitorFailover /\ FlagOFCWorkerFailover;
            \* step 3: Clear old messages sent to the old OFC
            NIB2OFC := <<>>;
            OFC2NIB := <<>>;
            \* step 4: empty local tables
            IRQueueOFC := <<>>;
            IRStatusOFC := [x \in 1..MaxNumIRs |-> IR_NONE];
            switch2Controller := <<>>;
            controller2Switch := [x\in SW |-> <<>>];
            \* step 5: make OFC unready
            OFC_READY := FALSE;
            
            \* when only OFC fails, NIB is the authority for IR_SENT
            \* OFC needs to learn from NIB about IR_SENT otherwise it could trigger deadlock
\*            OFCReadNIBForIRSent:
\*                await isNIBUp(NIBThreadID) \/ isNIBReconciliation(NIBThreadID);
\*                \* Read NIB to get 
\*                IRStatusOFC := [x \in 1..MaxNumIRs |-> IF IRStatus[x] = IR_SENT 
\*                                                       THEN IR_SENT
\*                                                       ELSE IRStatusOFC[x]];
            
            
            \* We are assuming a dedicated connection between switch and OFC for failover
            OFCReadSwitches:
                IRStatusOFC := [x \in 1..MaxNumIRs |-> IF x \in rangeSeq(installedIRs) 
                                                       THEN IR_DONE
                                                       ELSE IRStatusOFC[x]];
                FirstInstallOFC := [x \in 1..MaxNumIRs |-> IF IRStatusOFC[x] = IR_DONE
                                                           THEN FirstInstallOFC[x] + 1
                                                           ELSE FirstInstallOFC[x]];                                       
                OFC_READY := TRUE;

            OFCReadNIB:
                \* If NIB is up, OFC can read it directly; 
                \* otherwise, OFC waits until it comes up
                await NIB_READY_FOR_OFC \/ isNIBUp(NIBThreadID);
                \* hardcode: assume at most three IR
\*                IRQueueTmp := <<[tag |-> NO_TAG, IR |-> 1],
\*                                [tag |-> NO_TAG, IR |-> 2], 
\*                                [tag |-> NO_TAG, IR |-> 3]>>;
\*                IRQueueOFC := IRQueueTmp(IRQueueTmp, LAMBDA i: IRStatusOFC[i.IR] = IR_SENT \/ (i \in rangeSeq(IRQueueNIB) /\ IRStatusOFC[i.IR] # IR_DONE));
                IRQueueOFC := SelectSeq(IRQueueRC, LAMBDA i: IRStatusOFC[i.IR] # IR_DONE);
              
                
                

            \* Change RC status to up
            OFCBack2Normal:
\*                IRStatus := IRStatusOFC;
                await isNIBUp(NIBThreadID) \/ isNIBReconciliation(NIBThreadID);
                transaction := [name |-> "OFCOverrideIRStatus", 
                                        ops |-> <<IRStatusOFC, FirstInstallOFC>>];
                OFC2NIB := OFC2NIB \o <<transaction>>;
                controllerSubmoduleFailStat[OFCThreadID] := NotFailed ||
                controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] := NotFailed || 
                controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] := NotFailed;
    end process    
    \* ==========================
    
    \* ============ OFC NIB Event Handler ==========
    fair process OFCNIBEventHandler \in ({ofc0} \X {CONT_OFC_NIB_EVENT})
    variables NIBMsg = [value |-> [x |-> <<>>]], isBootStrap = TRUE,
              localIRSet = {}, NIBIRSet = {};
    begin
    OFCNIBEventHanderProc:
        while TRUE do
            controllerWaitForLockFree();
            if isOFCFailed(self) then
                FlagOFCNIBEventHandlerFailover := TRUE;
                goto OFCNIBEventHandlerFailover;
            else
                await NIB2OFC # <<>>;
                NIBMsg := Head(NIB2OFC);
                NIB2OFC := Tail(NIB2OFC);
                localIRSet := {IRQueueOFC[i].IR: i \in DOMAIN IRQueueOFC};
                NIBIRSet := {NIBMsg.value.IRQueueNIB[i].IR: i \in DOMAIN NIBMsg.value.IRQueueNIB};
                if localIRSet # NIBIRSet then
                \* enqueue new IRs to be scheduled
                    IRQueueOFC := SelectSeq(NIBMsg.value.IRQueueNIB, LAMBDA i: IRStatusOFC[i.IR] = IR_NONE);
                    assert Len(IRQueueOFC) <= MaxNumIRs;
                end if;
            end if;
        end while;    
    OFCNIBEventHandlerFailover:
        controllerWaitForLockFree();
        await isOFCUp(OFCThreadID);
        goto OFCNIBEventHanderProc;
    end process
    
    \* ====== OFC Worker Pool ======= 
    \* Workers 
    fair process controllerWorkerThreads \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    variables nextIRToSent = 0, rowIndex = -1, rowRemove = -1, stepOfFailure = 0,
              transaction = <<>>, NIBMsg = [value |-> [x |-> <<>>]], 
              op1 = [table |-> ""], IRQueue = <<>>, 
              op_ir_status_change = [table |-> ""],
              removeIR = FALSE; 
    begin
    ControllerThread:
    while TRUE do
        await controllerIsMaster(self[1]);
\*        await moduleIsUp(self);
\*        await canWorkerThreadContinue(self[1], self, IRQueueOFC);
        controllerWaitForLockFree();

        \* Controller thread consists of 3 Ops: 
        \* 1. modified read from IRQueue in the NIB (which gives the 
        \*    next IR to install)
        \* 2. update the state of db to locking mode
        \* 3. try to lock the IR to avoid two workers working on the same IR
        \*      (Note that sequence may fail in the middle of scheduling and
        \*       may reschedule the IR wrongly)
        \* (worker may fail between these Ops)

        OFCThreadGetNextIR:
        \* Step 1. get next IR to send
        \* TODO(@mingyang): tag the IR in IRQueueNIB to self 
            controllerWaitForLockFree();
            if isOFCFailed(self) then
                FlagOFCWorkerFailover := TRUE;
                goto OFCWorkerFailover;
            else
                await Len(IRQueueOFC) > 0;
                rowIndex := getFirstIRIndexToRead(self, IRQueueOFC);
                nextIRToSent := IRQueueOFC[rowIndex].IR;
                IRQueueOFC[rowIndex].tag := self;
                \* This is only useful during OFC failover to prevent redundant IR scheduling
                if IRStatusOFC[nextIRToSent] = IR_DONE then
                   goto OFCRemoveIRFromIRQueueOFCLocal;
                end if;
            end if;
        
        
        OFCThreadSendIR:
            controllerWaitForLockFree();
            if isOFCFailed(self) then
                FlagOFCWorkerFailover := TRUE;
                goto OFCWorkerFailover;
            else
                if IRStatusOFC[nextIRToSent] = IR_DONE then
                   \* This is only useful during OFC failover to prevent redundant IR scheduling
                   goto OFCRemoveIRFromIRQueueOFCLocal;
                else
                    IRStatusOFC[nextIRToSent] := IR_SENT;
                end if;
            end if;
            
        OFCThreadNotifyNIBIRSent:  
            controllerWaitForLockFree();
            if isOFCFailed(self) then
                FlagOFCWorkerFailover := TRUE;
                goto OFCWorkerFailover;
            else
                await isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID);
                op_ir_status_change := [table |-> NIBT_IR_STATUS, key |-> nextIRToSent, value |-> IR_SENT];
                transaction := [name |-> "OFCChangeIRStatus2Sent", ops |-> <<op_ir_status_change>>];
                OFC2NIB := OFC2NIB \o <<transaction>>;
            end if;
            
        ControllerThreadForwardIRInner:
            controllerWaitForLockFree();
            if isOFCFailed(self) then
                FlagOFCWorkerFailover := TRUE;
                goto OFCWorkerFailover;
            else
                controllerSendIR(nextIRToSent);
            end if;
            
        OFCRemoveIRFromIRQueueOFCLocal:
            controllerWaitForLockFree();
            if isOFCFailed(self) then
                  FlagOFCWorkerFailover := TRUE;
                        goto OFCWorkerFailover;
            else
                        if \E i \in DOMAIN IRQueueOFC: IRQueueOFC[i].IR = nextIRToSent then
                            rowRemove := getFirstIndexWith(nextIRToSent, self, IRQueueOFC);
                            IRQueueOFC := removeFromSeq(IRQueueOFC, rowRemove);
                            removeIR := TRUE;
                        end if;
            end if;
        OFCRemoveIRFromIRQueueRemote:
            controllerWaitForLockFree();
            if isOFCFailed(self) then
                        FlagOFCWorkerFailover := TRUE;
                        goto OFCWorkerFailover;
            else
                        if removeIR = TRUE then
                            await isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID);
                            op1 := [table |-> NIBT_IR_QUEUE, key |-> nextIRToSent];
                            transaction := [name |-> "RemoveIR", ops |-> <<op1>>];
                            OFC2NIB := OFC2NIB \o <<transaction>>;
                            removeIR := FALSE;
                        end if;
            end if;
    end while;
    
    OFCWorkerFailover:
        controllerWaitForLockFree();
        await isOFCUp(OFCThreadID);
        goto ControllerThread;
    end process
    \* ==========================


    
    \* ===== Event Handler ======
    \* TODO(@mingyang): OFC should be the authorative of SwSuspensionStatus 
    \* Add the local copy of SwSuspensionStatus at OFC
    \* Since my current goal is to make codes work without considering failures, 
    \* I have not make transactions to EH yet.
\*    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
\*    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, resetIR = 0, stepOfFailure = 0;
\*    begin
\*    ControllerEventHandlerProc:
\*    while TRUE do 
\*         await controllerIsMaster(self[1]);
\*         await moduleIsUp(self);   
\*         await swSeqChangedStatus # <<>>;
\*         controllerWaitForLockFree();
\*         \* Controller event handler process consists of two operations;
\*         \* 1. Picking the first event from the event queue
\*         \* 2. Check whether the event is a switch failure or a switch recovery
\*         monitoringEvent := Head(swSeqChangedStatus);
\*          
\*         \* instead of querying the NIB
\*         if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_RUN then
\*         
\*            \* ControllerSuspendSW only suspends the SW (so the rest of the system does not work on
\*            \* the tasks related to this switch anymore).
\*            \* Here, Due to performance reasons, we defere the task of resetting status of IRs to 
\*            \* the time that the switch is recovered (Lazy evaluation) because; First, it might not
\*            \* be necessary (for example, the switch may have installed the IR). Second, the switch
\*            \* may have faced a permanent failure in which these IRs are not valid anymore.                 
\*            ControllerSuspendSW: 
\*                controllerWaitForLockFree();
\*                controllerModuleFailOrNot();
\*                if (controllerSubmoduleFailStat[self] = NotFailed) then
\*                    SwSuspensionStatus[monitoringEvent.swID] := SW_SUSPEND;        
\*                else
\*                    goto ControllerEventHandlerStateReconciliation;
\*                end if;
\*                
\*         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
\*            \*call suspendInSchedulingIRs(monitoringEvent.swID);
\*            
\*            \* ControllerFreeSuspendedSW consists of three operations; 
\*            \* 1. Save on db that it is going to reset the IRs
\*            \* 2. Change the SW status to SW_RUN (so all the corresponding IRs going to be scheduled immediately)
\*            \* (event handler may fail between any of these Ops.)
\*            ControllerFreeSuspendedSW: 
\*                controllerWaitForLockFree();
\*                whichStepToFail(2);
\*                if (stepOfFailure # 1) then 
\*                    \* Step 1: save state on NIB
\*                    controllerStateNIB[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
\*                    if (stepOfFailure # 2) then
\*                        \* Step 2: change switch status to SW_RUN
\*                        SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;  
\*                    end if;
\*                end if;
\*                
\*                if (stepOfFailure # 0) then
\*                    controllerModuleFails();
\*                    goto ControllerEventHandlerStateReconciliation;
\*                end if;
\*            
\*            \* ControllerCheckIfThisIsLastEvent consists of 3 operations;
\*            \* 1. Check if this is the last event for the corresponding sw (if it is not, then, maybe the switch
\*            \*      has failed again and resetting the IRs is not necessary). Note that we have to process the 
\*            \*      event and change the status of SW anyway. Otherwise, it may result in discarding the subsequent
\*            \*      events (one of the failures!!!!)   
\*            \* 2. GetIRsToBeChecked 
\*            \* 3. ResetAllIRs
\*            ControllerCheckIfThisIsLastEvent:
\*                controllerWaitForLockFree();
\*                controllerModuleFailOrNot();
\*                if (controllerSubmoduleFailStat[self] = NotFailed) then
\*                    if ~existsMonitoringEventHigherNum(monitoringEvent) then                        
\*                        \* getIRsToBeChecked retrieves all the IRs need to reset
\*                        getIRsToBeChecked:
\*                            controllerWaitForLockFree();
\*                            controllerModuleFailOrNot();
\*                            if (controllerSubmoduleFailStat[self] = NotFailed) then
\*                                setIRsToReset := getIRSetToReset(monitoringEvent.swID);
\*                                if (setIRsToReset = {}) then \* Do not do the operations in ResetAllIRs label if setIRsToReset is Empty *\
\*                                    goto ControllerEvenHanlderRemoveEventFromQueue;
\*                                end if;
\*                            else
\*                                goto ControllerEventHandlerStateReconciliation;
\*                            end if;
\*                            
\*                        \* ResetAllIRs reset all the IRs in IR_SENT mode to IR_NONE one by one
\*                        ResetAllIRs:
\*                            while TRUE do \* Initially: while setIRsToReset # {} do
\*                                controllerWaitForLockFree();
\*                                controllerModuleFailOrNot();
\*                                if (controllerSubmoduleFailStat[self] = NotFailed) then
\*                                    resetIR := CHOOSE x \in setIRsToReset: TRUE;
\*                                    setIRsToReset := setIRsToReset \ {resetIR};
\*                                    
\*                                    \* the following operation (if -- end if;) should be done atomically
\*                                    \* using CAS operation
\*                                    if IRStatus[resetIR] # IR_DONE then
\*                                        IRStatus[resetIR] := IR_NONE;
\*                                    end if;
\*                                    
\*                                    if setIRsToReset = {} then \* End of while *\
\*                                        goto ControllerEvenHanlderRemoveEventFromQueue;
\*                                    end if;
\*                                else
\*                                    goto ControllerEventHandlerStateReconciliation;
\*                                end if;
\*                            end while;
\*                    end if;
\*                else
\*                    goto ControllerEventHandlerStateReconciliation;
\*                end if;
\*         end if;
\*         
\*         \* ControllerEventHandlerRemoveEventFromQueue consists of 2 operations;
\*         \* 1. Clear the state on db
\*         \* 2. Remove the event from queue (Lazy removal procedure)
\*         \* event handler may fail between these Ops. 
\*         ControllerEvenHanlderRemoveEventFromQueue:
\*            controllerWaitForLockFree();
\*            whichStepToFail(2);
\*            if (stepOfFailure # 1) then 
\*                \* Step 1: clear state on NIB
\*                controllerStateNIB[self] := [type |-> NO_STATUS]; 
\*                if (stepOfFailure # 2) then
\*                    \* Step 2: remove from event queue
\*                    swSeqChangedStatus := Tail(swSeqChangedStatus);
\*                end if;
\*            end if;
\*            
\*            if (stepOfFailure # 0) then
\*                controllerModuleFails();
\*                goto ControllerEventHandlerStateReconciliation;
\*            end if;
\*    end while;
\*    
\*    
\*    \* After that the event handler failed and the watchdog has restarted it.
\*    \* Worker starts by calling the reconciliation function in which
\*    \* it undoes some of the operations.
\*    
\*    \* it is pretty straight forward here, if event handler is in START_RESET_IR
\*    \* status, it means we are not sure whether we have reset all the IRs or not
\*    \* so, event handler changes the SW status back to SW_SUSPEND and starts its
\*    \* normal execution in which it will first pick the first event in the queue.
\*    \* Note that due to lazy removal policy, the first event in the queu is exactly
\*    \* the sw recovery event. 
\*    ControllerEventHandlerStateReconciliation:
\*         await controllerIsMaster(self[1]);
\*         await moduleIsUp(self);   
\*         await swSeqChangedStatus # <<>>; 
\*         controllerReleaseLock(self);
\*         if (controllerStateNIB[self].type = START_RESET_IR) then
\*            SwSuspensionStatus[controllerStateNIB[self].sw] := SW_SUSPEND;
\*         end if;
\*        goto ControllerEventHandlerProc;
\*    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    \* monitroing server does not need a reconciliation phase. 
    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = [type |-> 0], 
            op_ir_status_change = [table |-> ""], 
            op_first_install = [table |-> ""], 
            transaction = <<>>;
    begin
    OFCMonitorCheckIfMastr:
    while TRUE do
        \* ControllerMonitor 
        \* 1. Picks the first packet from the packets received from the switches
        \* 2. Checks the message type;
        \***** 2.1. type = INSTALLED_SUCCESSFULLY -> sw has successfully installed the IR
        \***** 2.2. type = RECONCILIATION_RESPONCE -> sw's responce to the reconciliation 
        \*****              request. 
        await controllerIsMaster(self[1]);
        if isOFCFailed(self) then
            FlagOFCMonitorFailover := TRUE;
            goto OFCMonitorFailover;
        else
            await switch2Controller # <<>>;
            controllerReleaseLock(self);
            msg := Head(switch2Controller);
            assert msg.from = IR2SW[msg.IR];
            assert msg.type \in {RECONCILIATION_RESPONSE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY};
        end if;
        
        OFCMonitorUpdateIRDone:
        if msg.type = INSTALLED_SUCCESSFULLY then
                \* If msg type is INSTALLED_SUCCESSFULLY, we have to change the IR status
                \* to IR_DONE. 
                OFCUpdateIRDone:
                    controllerWaitForLockFree(); 
                    if isOFCFailed(self) then
                        FlagOFCMonitorFailover := TRUE;
                        goto OFCMonitorFailover;
                    else
                        IRStatusOFC[msg.IR] := IR_DONE; 
                        FirstInstallOFC[msg.IR] := 1;
                    end if;
                \* update NIB
                OFCUpdateNIBIRDONE:
                    if isOFCFailed(self) then
                        FlagOFCMonitorFailover := TRUE;
                        goto OFCMonitorFailover;
                    else
                        await isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID);
                        op_ir_status_change := [table |-> NIBT_IR_STATUS, key |-> msg.IR, value |-> IR_DONE];
                        op_first_install  := [table |-> NIBT_FIRST_INSTALL, key |-> msg.IR, value |-> 1];
                        transaction := [name |-> "FirstInstallIR", 
                                        ops |-> <<op_ir_status_change, op_first_install>>];
                        OFC2NIB := OFC2NIB \o <<transaction>>;
                    end if;

        else 
            assert FALSE;
        end if;
        
        \*end if;
        
        \* MonitoringServerRemoveFromQueue lazily removes the msg from queue. 
        MonitoringServerRemoveFromQueue:
            controllerWaitForLockFree();
            controllerModuleFailOrNot();
            if (controllerSubmoduleFailStat[self] = NotFailed) then
                switch2Controller := Tail(switch2Controller);
            else
                goto OFCMonitorCheckIfMastr;
            end if; 
    end while;
    OFCMonitorFailover:
        controllerWaitForLockFree();
        await isOFCUp(OFCThreadID);
        goto OFCMonitorCheckIfMastr;
    end process
    
    \* ==========================
    
    
\*    (*******************************************************************)
\*    (*                     Shared (OFC and RC)                         *)
\*    (*******************************************************************)
\*    \* there are two watchdogs, one in RC, the other in OFC
\*    \* ======== Watchdog ======== 
\*    fair process watchDog \in ({ofc0, rc0} \X {WATCH_DOG})
\*    \* Watchdog in each iteration finds all the failed submodules 
\*    \* and creates branches in each of which one of the failed 
\*    \* submodules is restarted. 
\*    variable controllerFailedModules = {};
\*    begin
\*    ControllerWatchDogProc:
\*    while TRUE do
\*        controllerWaitForLockFree();
\*        controllerFailedModules := returnControllerFailedModules(self[1]);
\*        await Cardinality(controllerFailedModules) > 0;
\*        with module \in controllerFailedModules do
\*            assert controllerSubmoduleFailStat[module] = Failed;
\*            controllerLock := module;
\*            controllerSubmoduleFailStat[module] := NotFailed;   
\*        end with;
\*        
\*    end while; 
\*    end process
    \* ==========================
       
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9127619cdc4f88afed7c37e8130af8cd (chksum(pcal) = "cb8e9368" /\ chksum(tla) = "9d4abbb1") (chksum(pcal) = "693f78c9" /\ chksum(tla) = "df5ffee9") (chksum(pcal) \in STRING /\ chksum(tla) \in STRING) (chksum(pcal) = "1bcf2871" /\ chksum(tla) = "c11ffdac")
\* Process variable value of process NIBFailoverProc at line 1508 col 15 changed to value_
\* Process variable nextTrans of process NIBRCEventHandler at line 1550 col 15 changed to nextTrans_
\* Process variable value of process NIBRCEventHandler at line 1550 col 42 changed to value_N
\* Process variable rowRemove of process NIBRCEventHandler at line 1550 col 56 changed to rowRemove_
\* Process variable IR2Remove of process NIBRCEventHandler at line 1551 col 15 changed to IR2Remove_
\* Process variable send_NIB_back of process NIBRCEventHandler at line 1551 col 30 changed to send_NIB_back_
\* Process variable stepOfFailure of process NIBRCEventHandler at line 1551 col 50 changed to stepOfFailure_
\* Process variable IRIndex of process NIBRCEventHandler at line 1552 col 15 changed to IRIndex_
\* Process variable debug of process NIBRCEventHandler at line 1552 col 29 changed to debug_
\* Process variable rowRemove of process NIBOFCEventHandler at line 1602 col 56 changed to rowRemove_N
\* Process variable stepOfFailure of process NIBOFCEventHandler at line 1603 col 50 changed to stepOfFailure_N
\* Process variable NIBMsg of process RCNIBEventHandler at line 1699 col 15 changed to NIBMsg_
\* Process variable isBootStrap of process RCNIBEventHandler at line 1699 col 50 changed to isBootStrap_
\* Process variable op1 of process controllerSequencer at line 1759 col 48 changed to op1_
\* Process variable transaction of process controllerSequencer at line 1761 col 17 changed to transaction_
\* Process variable stepOfFailure of process controllerSequencer at line 1762 col 29 changed to stepOfFailure_c
\* Process variable transaction of process OFCFailoverProc at line 1924 col 15 changed to transaction_O
\* Process variable NIBMsg of process OFCNIBEventHandler at line 2000 col 15 changed to NIBMsg_O
\* Process variable transaction of process controllerWorkerThreads at line 2032 col 15 changed to transaction_c
\* Process variable op_ir_status_change of process controllerWorkerThreads at line 2034 col 15 changed to op_ir_status_change_
VARIABLES switchLock, controllerLock, FirstInstallOFC, FirstInstallNIB, 
          sw_fail_ordering_var, ContProcSet, SwProcSet, swSeqChangedStatus, 
          controller2Switch, switch2Controller, switchStatus, installedIRs, 
          NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
          Ofa2InstallerBuff, TCAM, controlMsgCounter, 
          controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
          switchOrdering, dependencyGraph, IR2SW, NIBUpdateForRC, 
          controllerStateRC, IRStatusRC, IRQueueRC, SwSuspensionStatusRC, 
          SetScheduledIRsRC, FlagRCNIBEventHandlerFailover, 
          FlagRCSequencerFailover, RC_READY, idThreadWorkingOnIR, 
          workerThreadRanking, controllerStateOFC, IRStatusOFC, IRQueueOFC, 
          SwSuspensionStatusOFC, SetScheduledIRsOFC, FlagOFCWorkerFailover, 
          FlagOFCMonitorFailover, FlagOFCNIBEventHandlerFailover, OFCThreadID, 
          OFC_READY, NIB2OFC, NIB2RC, X2NIB, OFC2NIB, RC2NIB, FlagNIBFailover, 
          FlagNIBRCEventhandlerFailover, FlagNIBOFCEventhandlerFailover, 
          NIB_READY_FOR_RC, NIB_READY_FOR_OFC, masterState, 
          controllerStateNIB, IRStatus, SwSuspensionStatus, IRQueueNIB, 
          SetScheduledIRs, X2NIB_len, NIBThreadID, RCThreadID, pc

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
                                             [] controllerID = nib0 -> MAX_NUM_CONTROLLER_SUB_FAILURE.nib0



isOFCUp(threadID) == /\ controllerSubmoduleFailStat[OFCThreadID] = NotFailed
                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = NotFailed
                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = NotFailed
isOFCFailed(threadID) == /\ controllerSubmoduleFailStat[OFCThreadID] = Failed
                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = Failed
                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = Failed
isOFCReconciliation(threadID) == /\ controllerSubmoduleFailStat[OFCThreadID] = InReconciliation
                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = InReconciliation
                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = InReconciliation





NoEntryTaggedWith(threadID, IRQueue) == ~\E x \in rangeSeq(IRQueue): x.tag = threadID
FirstUntaggedEntry(num, IRQueue) == ~\E x \in DOMAIN IRQueue: /\ IRQueue[x].tag = NO_TAG
                                                                        /\ x < num




getFirstIRIndexToRead(threadID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: TRUE


getFirstIndexWith(RID, threadID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: IRQueue[x].IR = RID
getFirstIndexWithNIB(RID, IRQueue) == CHOOSE x \in DOMAIN IRQueue: IRQueue[x].IR = RID
isNIBUp(threadID) == controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
                     controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed
isNIBFailed(threadID) == controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = Failed /\
                     controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = Failed
isNIBReconciliation(threadID) == controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = InReconciliation /\
                     controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = InReconciliation


isDependencySatisfied(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                     /\ IRStatus[y] # IR_DONE
isDependencySatisfiedRC(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
                                                     /\ IRStatusRC[y] # IR_DONE
getSetIRsCanBeScheduledNext(CID)  == {x \in 1..MaxNumIRs: /\ IRStatus[x] = IR_NONE
                                                          /\ isDependencySatisfied(x)
                                                          /\ SwSuspensionStatus[IR2SW[x]] = SW_RUN
                                                          /\ x \notin SetScheduledIRs[IR2SW[x]]}

getSetIRsCanBeScheduledNextRC(CID)  == {x \in 1..MaxNumIRs: /\ IRStatusRC[x] = IR_NONE
                                                          /\ isDependencySatisfiedRC(x)
                                                          /\ SwSuspensionStatusRC[IR2SW[x]] = SW_RUN
                                                          /\ x \notin SetScheduledIRsRC[IR2SW[x]]}
removeInstalledIR(IRSet) == IF IRSet = {}
                            THEN IRSet
                            ELSE {ir \in IRSet: IRStatusRC[ir] # IR_DONE}
isRCFailed(id) == controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = Failed
            /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed
isRCUp(id) == controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = NotFailed
            /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
isRCReconciliation(id) == controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = InReconciliation
            /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = InReconciliation


isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND



setFreeThreads(CID, IRQueue) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>, IRQueue)
                                                      /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}
printIRQueue(IRQueue) == IRQueue
canWorkerThreadContinue(CID, threadID, IRQueue) == \/ \E x \in rangeSeq(IRQueue): x.tag = threadID
                                          \/ /\ \E x \in rangeSeq(IRQueue): x.tag = NO_TAG
                                             /\ NoEntryTaggedWith(threadID, IRQueue)
                                             /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID, IRQueue)})




setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
                                                                                                                /\ y.tag = <<CID, x>>}
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
          statusResolveMsg, recoveredElem, value_, nextTrans_, value_N, 
          rowRemove_, IR2Remove_, send_NIB_back_, stepOfFailure_, IRIndex_, 
          debug_, nextTrans, value, rowRemove_N, IR2Remove, send_NIB_back, 
          stepOfFailure_N, IRIndex, debug, NIBMsg_, isBootStrap_, 
          toBeScheduledIRs, key, op1_, op2, transaction_, nextIR, 
          stepOfFailure_c, transaction_O, IRQueueTmp, NIBMsg_O, isBootStrap, 
          localIRSet, NIBIRSet, nextIRToSent, rowIndex, rowRemove, 
          stepOfFailure, transaction_c, NIBMsg, op1, IRQueue, 
          op_ir_status_change_, removeIR, msg, op_ir_status_change, 
          op_first_install, transaction

vars == << switchLock, controllerLock, FirstInstallOFC, FirstInstallNIB, 
           sw_fail_ordering_var, ContProcSet, SwProcSet, swSeqChangedStatus, 
           controller2Switch, switch2Controller, switchStatus, installedIRs, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
           Ofa2InstallerBuff, TCAM, controlMsgCounter, 
           controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
           switchOrdering, dependencyGraph, IR2SW, NIBUpdateForRC, 
           controllerStateRC, IRStatusRC, IRQueueRC, SwSuspensionStatusRC, 
           SetScheduledIRsRC, FlagRCNIBEventHandlerFailover, 
           FlagRCSequencerFailover, RC_READY, idThreadWorkingOnIR, 
           workerThreadRanking, controllerStateOFC, IRStatusOFC, IRQueueOFC, 
           SwSuspensionStatusOFC, SetScheduledIRsOFC, FlagOFCWorkerFailover, 
           FlagOFCMonitorFailover, FlagOFCNIBEventHandlerFailover, 
           OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
           FlagNIBFailover, FlagNIBRCEventhandlerFailover, 
           FlagNIBOFCEventhandlerFailover, NIB_READY_FOR_RC, 
           NIB_READY_FOR_OFC, masterState, controllerStateNIB, IRStatus, 
           SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, X2NIB_len, 
           NIBThreadID, RCThreadID, pc, ingressPkt, ingressIR, egressMsg, 
           ofaInMsg, ofaOutConfirmation, installerInIR, statusMsg, 
           notFailedSet, failedElem, failedSet, statusResolveMsg, 
           recoveredElem, value_, nextTrans_, value_N, rowRemove_, IR2Remove_, 
           send_NIB_back_, stepOfFailure_, IRIndex_, debug_, nextTrans, value, 
           rowRemove_N, IR2Remove, send_NIB_back, stepOfFailure_N, IRIndex, 
           debug, NIBMsg_, isBootStrap_, toBeScheduledIRs, key, op1_, op2, 
           transaction_, nextIR, stepOfFailure_c, transaction_O, IRQueueTmp, 
           NIBMsg_O, isBootStrap, localIRSet, NIBIRSet, nextIRToSent, 
           rowIndex, rowRemove, stepOfFailure, transaction_c, NIBMsg, op1, 
           IRQueue, op_ir_status_change_, removeIR, msg, op_ir_status_change, 
           op_first_install, transaction >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({"proc"} \X {CONT_NIB_FAILOVER})) \cup (({nib0} \X {CONT_NIB_RC_EVENT})) \cup (({nib0} \X {CONT_NIB_OFC_EVENT})) \cup (({"proc"} \X {RC_FAILOVER})) \cup (({rc0} \X {CONT_RC_NIB_EVENT})) \cup (({rc0} \X {CONT_SEQ})) \cup (( {"proc"} \X {OFC_FAILURE})) \cup (({"proc"} \X {OFC_FAILOVER})) \cup (({ofc0} \X {CONT_OFC_NIB_EVENT})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_MONITOR}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstallOFC = [x \in 1..MaxNumIRs |-> 0]
        /\ FirstInstallNIB = [x \in 1..MaxNumIRs |-> 0]
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ ContProcSet = ((({rc0} \X {CONT_SEQ}))\cup (({rc0} \X {CONT_RC_NIB_EVENT})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL))
                          \cup (({ofc0} \X {CONT_OFC_NIB_EVENT}))
                          \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))
                          \cup (({nib0} \X {CONT_NIB_RC_EVENT}))
                          \cup (({nib0} \X {CONT_NIB_OFC_EVENT})))
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
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0, nib0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ switchOrdering = (CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ IR2SW = (CHOOSE x \in [1..MaxNumIRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z
                                                                              /\ switchOrdering[x[y]] =< switchOrdering[x[z]])
        /\ NIBUpdateForRC = FALSE
        /\ controllerStateRC = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatusRC = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ IRQueueRC = <<>>
        /\ SwSuspensionStatusRC = [x \in SW |-> SW_RUN]
        /\ SetScheduledIRsRC = [y \in SW |-> {}]
        /\ FlagRCNIBEventHandlerFailover = FALSE
        /\ FlagRCSequencerFailover = FALSE
        /\ RC_READY = FALSE
        /\ idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK]
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ controllerStateOFC = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatusOFC = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ IRQueueOFC = <<>>
        /\ SwSuspensionStatusOFC = [x \in SW |-> SW_RUN]
        /\ SetScheduledIRsOFC = [y \in SW |-> {}]
        /\ FlagOFCWorkerFailover = FALSE
        /\ FlagOFCMonitorFailover = FALSE
        /\ FlagOFCNIBEventHandlerFailover = FALSE
        /\ OFCThreadID = <<ofc0,CHOOSE x \in CONTROLLER_THREAD_POOL : TRUE>>
        /\ OFC_READY = FALSE
        /\ NIB2OFC = <<>>
        /\ NIB2RC = <<>>
        /\ X2NIB = <<>>
        /\ OFC2NIB = <<>>
        /\ RC2NIB = <<>>
        /\ FlagNIBFailover = FALSE
        /\ FlagNIBRCEventhandlerFailover = FALSE
        /\ FlagNIBOFCEventhandlerFailover = FALSE
        /\ NIB_READY_FOR_RC = FALSE
        /\ NIB_READY_FOR_OFC = FALSE
        /\ masterState = [ofc0 |-> "primary", rc0 |-> "primary"]
        /\ controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ X2NIB_len = 0
        /\ NIBThreadID = <<nib0, CONT_NIB_RC_EVENT>>
        /\ RCThreadID = <<rc0, CONT_SEQ>>
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
        (* Process NIBFailoverProc *)
        /\ value_ = [self \in ({"proc"} \X {CONT_NIB_FAILOVER}) |-> NULL]
        (* Process NIBRCEventHandler *)
        /\ nextTrans_ = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> [name |-> ""]]
        /\ value_N = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> NULL]
        /\ rowRemove_ = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> 0]
        /\ IR2Remove_ = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> 0]
        /\ send_NIB_back_ = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> ""]
        /\ stepOfFailure_ = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> 0]
        /\ IRIndex_ = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> -1]
        /\ debug_ = [self \in ({nib0} \X {CONT_NIB_RC_EVENT}) |-> -1]
        (* Process NIBOFCEventHandler *)
        /\ nextTrans = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> [name |-> ""]]
        /\ value = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> NULL]
        /\ rowRemove_N = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> 0]
        /\ IR2Remove = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> 0]
        /\ send_NIB_back = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> ""]
        /\ stepOfFailure_N = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> 0]
        /\ IRIndex = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> -1]
        /\ debug = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> -1]
        (* Process RCNIBEventHandler *)
        /\ NIBMsg_ = [self \in ({rc0} \X {CONT_RC_NIB_EVENT}) |-> [value |-> [x |-> <<>>]]]
        /\ isBootStrap_ = [self \in ({rc0} \X {CONT_RC_NIB_EVENT}) |-> TRUE]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_SEQ}) |-> {}]
        /\ key = [self \in ({rc0} \X {CONT_SEQ}) |-> ""]
        /\ op1_ = [self \in ({rc0} \X {CONT_SEQ}) |-> [table |-> ""]]
        /\ op2 = [self \in ({rc0} \X {CONT_SEQ}) |-> [table |-> ""]]
        /\ transaction_ = [self \in ({rc0} \X {CONT_SEQ}) |-> <<>>]
        /\ nextIR = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        /\ stepOfFailure_c = [self \in ({rc0} \X {CONT_SEQ}) |-> 0]
        (* Process OFCFailoverProc *)
        /\ transaction_O = [self \in ({"proc"} \X {OFC_FAILOVER}) |-> <<>>]
        /\ IRQueueTmp = [self \in ({"proc"} \X {OFC_FAILOVER}) |-> <<>>]
        (* Process OFCNIBEventHandler *)
        /\ NIBMsg_O = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> [value |-> [x |-> <<>>]]]
        /\ isBootStrap = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> TRUE]
        /\ localIRSet = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> {}]
        /\ NIBIRSet = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> {}]
        (* Process controllerWorkerThreads *)
        /\ nextIRToSent = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ rowIndex = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ rowRemove = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ stepOfFailure = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ transaction_c = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> <<>>]
        /\ NIBMsg = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> [value |-> [x |-> <<>>]]]
        /\ op1 = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> [table |-> ""]]
        /\ IRQueue = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> <<>>]
        /\ op_ir_status_change_ = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> [table |-> ""]]
        /\ removeIR = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> FALSE]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [type |-> 0]]
        /\ op_ir_status_change = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [table |-> ""]]
        /\ op_first_install = [self \in ({ofc0} \X {CONT_MONITOR}) |-> [table |-> ""]]
        /\ transaction = [self \in ({ofc0} \X {CONT_MONITOR}) |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({NIC_ASIC_IN} \X SW) -> "SwitchRcvPacket"
                                        [] self \in ({NIC_ASIC_OUT} \X SW) -> "SwitchFromOFAPacket"
                                        [] self \in ({OFA_IN} \X SW) -> "SwitchOfaProcIn"
                                        [] self \in ({OFA_OUT} \X SW) -> "SwitchOfaProcOut"
                                        [] self \in ({INSTALLER} \X SW) -> "SwitchInstallerProc"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({"proc"} \X {CONT_NIB_FAILOVER}) -> "NIBFailoverResetStates"
                                        [] self \in ({nib0} \X {CONT_NIB_RC_EVENT}) -> "NIBHandleRCTransactions"
                                        [] self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) -> "NIBHandleOFCTransactions"
                                        [] self \in ({"proc"} \X {RC_FAILOVER}) -> "RCFailoverResetStates"
                                        [] self \in ({rc0} \X {CONT_RC_NIB_EVENT}) -> "RCNIBEventHanderProc"
                                        [] self \in ({rc0} \X {CONT_SEQ}) -> "RCSendReadTransaction"
                                        [] self \in ( {"proc"} \X {OFC_FAILURE}) -> "OFCFailure"
                                        [] self \in ({"proc"} \X {OFC_FAILOVER}) -> "OFCFailoverResetStates"
                                        [] self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) -> "OFCNIBEventHanderProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "OFCMonitorCheckIfMastr"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ isOFCUp(OFCThreadID) \/ isOFCFailed(OFCThreadID)
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type = INSTALL_FLOW, 
                                       "Failure of assertion at line 1120, column 9.")
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ installedIRs' = Append(installedIRs, ingressPkt'[self].IR)
                             /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], ingressPkt'[self].IR)]
                             /\ switch2Controller' = Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                                                from |-> self[2],
                                                                                IR |-> ingressPkt'[self].IR])
                             /\ Assert(\/ switchLock[2] = self[2]
                                       \/ switchLock[2] = NO_LOCK, 
                                       "Failure of assertion at line 841, column 9 of macro called at line 1127, column 9.")
                             /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                             FirstInstallNIB, 
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
                                             IR2SW, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             IRQueueRC, SwSuspensionStatusRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             controllerStateOFC, IRStatusOFC, 
                                             IRQueueOFC, SwSuspensionStatusOFC, 
                                             SetScheduledIRsOFC, 
                                             FlagOFCWorkerFailover, 
                                             FlagOFCMonitorFailover, 
                                             FlagOFCNIBEventHandlerFailover, 
                                             OFCThreadID, OFC_READY, NIB2OFC, 
                                             NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                             FlagNIBFailover, 
                                             FlagNIBRCEventhandlerFailover, 
                                             FlagNIBOFCEventhandlerFailover, 
                                             NIB_READY_FOR_RC, 
                                             NIB_READY_FOR_OFC, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             value_, nextTrans_, value_N, 
                                             rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug, NIBMsg_, 
                                             isBootStrap_, toBeScheduledIRs, 
                                             key, op1_, op2, transaction_, 
                                             nextIR, stepOfFailure_c, 
                                             transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure, 
                                             transaction_c, NIBMsg, op1, 
                                             IRQueue, op_ir_status_change_, 
                                             removeIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(\/ ingressIR'[self].type = RECONCILIATION_REQUEST
                                   \/ ingressIR'[self].type = INSTALL_FLOW, 
                                   "Failure of assertion at line 1152, column 9.")
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, 
                                         swSeqChangedStatus, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         IRQueueRC, SwSuspensionStatusRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         controllerStateOFC, IRStatusOFC, 
                                         IRQueueOFC, SwSuspensionStatusOFC, 
                                         SetScheduledIRsOFC, 
                                         FlagOFCWorkerFailover, 
                                         FlagOFCMonitorFailover, 
                                         FlagOFCNIBEventHandlerFailover, 
                                         OFCThreadID, OFC_READY, NIB2OFC, 
                                         NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                         FlagNIBFailover, 
                                         FlagNIBRCEventhandlerFailover, 
                                         FlagNIBOFCEventhandlerFailover, 
                                         NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug, 
                                         NIBMsg_, isBootStrap_, 
                                         toBeScheduledIRs, key, op1_, op2, 
                                         transaction_, nextIR, stepOfFailure_c, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure, transaction_c, NIBMsg, 
                                         op1, IRQueue, op_ir_status_change_, 
                                         removeIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

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
                                                      FirstInstallOFC, 
                                                      FirstInstallNIB, 
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
                                                      NIBUpdateForRC, 
                                                      controllerStateRC, 
                                                      IRStatusRC, IRQueueRC, 
                                                      SwSuspensionStatusRC, 
                                                      SetScheduledIRsRC, 
                                                      FlagRCNIBEventHandlerFailover, 
                                                      FlagRCSequencerFailover, 
                                                      RC_READY, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      controllerStateOFC, 
                                                      IRStatusOFC, IRQueueOFC, 
                                                      SwSuspensionStatusOFC, 
                                                      SetScheduledIRsOFC, 
                                                      FlagOFCWorkerFailover, 
                                                      FlagOFCMonitorFailover, 
                                                      FlagOFCNIBEventHandlerFailover, 
                                                      OFCThreadID, OFC_READY, 
                                                      NIB2OFC, NIB2RC, X2NIB, 
                                                      OFC2NIB, RC2NIB, 
                                                      FlagNIBFailover, 
                                                      FlagNIBRCEventhandlerFailover, 
                                                      FlagNIBOFCEventhandlerFailover, 
                                                      NIB_READY_FOR_RC, 
                                                      NIB_READY_FOR_OFC, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      X2NIB_len, NIBThreadID, 
                                                      RCThreadID, ingressPkt, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, value_, 
                                                      nextTrans_, value_N, 
                                                      rowRemove_, IR2Remove_, 
                                                      send_NIB_back_, 
                                                      stepOfFailure_, IRIndex_, 
                                                      debug_, nextTrans, value, 
                                                      rowRemove_N, IR2Remove, 
                                                      send_NIB_back, 
                                                      stepOfFailure_N, IRIndex, 
                                                      debug, NIBMsg_, 
                                                      isBootStrap_, 
                                                      toBeScheduledIRs, key, 
                                                      op1_, op2, transaction_, 
                                                      nextIR, stepOfFailure_c, 
                                                      transaction_O, 
                                                      IRQueueTmp, NIBMsg_O, 
                                                      isBootStrap, localIRSet, 
                                                      NIBIRSet, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure, 
                                                      transaction_c, NIBMsg, 
                                                      op1, IRQueue, 
                                                      op_ir_status_change_, 
                                                      removeIR, msg, 
                                                      op_ir_status_change, 
                                                      op_first_install, 
                                                      transaction >>

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
                                       "Failure of assertion at line 1180, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                             FirstInstallNIB, 
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
                                             IR2SW, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             IRQueueRC, SwSuspensionStatusRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             controllerStateOFC, IRStatusOFC, 
                                             IRQueueOFC, SwSuspensionStatusOFC, 
                                             SetScheduledIRsOFC, 
                                             FlagOFCWorkerFailover, 
                                             FlagOFCMonitorFailover, 
                                             FlagOFCNIBEventHandlerFailover, 
                                             OFCThreadID, OFC_READY, NIB2OFC, 
                                             NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                             FlagNIBFailover, 
                                             FlagNIBRCEventhandlerFailover, 
                                             FlagNIBOFCEventhandlerFailover, 
                                             NIB_READY_FOR_RC, 
                                             NIB_READY_FOR_OFC, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             value_, nextTrans_, value_N, 
                                             rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug, NIBMsg_, 
                                             isBootStrap_, toBeScheduledIRs, 
                                             key, op1_, op2, transaction_, 
                                             nextIR, stepOfFailure_c, 
                                             transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure, 
                                             transaction_c, NIBMsg, op1, 
                                             IRQueue, op_ir_status_change_, 
                                             removeIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 841, column 9 of macro called at line 1189, column 17.")
                                            /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ switch2Controller' = Append(switch2Controller, egressMsg[self])
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED egressMsg
                                       ELSE /\ egressMsg' = [egressMsg EXCEPT ![self] = [type |-> 0]]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED << switchLock, 
                                                            switch2Controller >>
                                 /\ UNCHANGED << controllerLock, 
                                                 FirstInstallOFC, 
                                                 FirstInstallNIB, 
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
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 IRQueueRC, 
                                                 SwSuspensionStatusRC, 
                                                 SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 controllerStateOFC, 
                                                 IRStatusOFC, IRQueueOFC, 
                                                 SwSuspensionStatusOFC, 
                                                 SetScheduledIRsOFC, 
                                                 FlagOFCWorkerFailover, 
                                                 FlagOFCMonitorFailover, 
                                                 FlagOFCNIBEventHandlerFailover, 
                                                 OFCThreadID, OFC_READY, 
                                                 NIB2OFC, NIB2RC, X2NIB, 
                                                 OFC2NIB, RC2NIB, 
                                                 FlagNIBFailover, 
                                                 FlagNIBRCEventhandlerFailover, 
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, value_, 
                                                 nextTrans_, value_N, 
                                                 rowRemove_, IR2Remove_, 
                                                 send_NIB_back_, 
                                                 stepOfFailure_, IRIndex_, 
                                                 debug_, nextTrans, value, 
                                                 rowRemove_N, IR2Remove, 
                                                 send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug, NIBMsg_, isBootStrap_, 
                                                 toBeScheduledIRs, key, op1_, 
                                                 op2, transaction_, nextIR, 
                                                 stepOfFailure_c, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure, 
                                                 transaction_c, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

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
                                   "Failure of assertion at line 1217, column 9.")
                         /\ Assert(ofaInMsg'[self].IR  \in 1..MaxNumIRs, 
                                   "Failure of assertion at line 1218, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         IRQueueRC, SwSuspensionStatusRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         controllerStateOFC, IRStatusOFC, 
                                         IRQueueOFC, SwSuspensionStatusOFC, 
                                         SetScheduledIRsOFC, 
                                         FlagOFCWorkerFailover, 
                                         FlagOFCMonitorFailover, 
                                         FlagOFCNIBEventHandlerFailover, 
                                         OFCThreadID, OFC_READY, NIB2OFC, 
                                         NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                         FlagNIBFailover, 
                                         FlagNIBRCEventhandlerFailover, 
                                         FlagNIBOFCEventhandlerFailover, 
                                         NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug, 
                                         NIBMsg_, isBootStrap_, 
                                         toBeScheduledIRs, key, op1_, op2, 
                                         transaction_, nextIR, stepOfFailure_c, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure, transaction_c, NIBMsg, 
                                         op1, IRQueue, op_ir_status_change_, 
                                         removeIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                           /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           /\ switchLock' = <<INSTALLER, self[2]>>
                                           /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                                 THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], ofaInMsg[self].IR)]
                                                 ELSE /\ Assert(FALSE, 
                                                                "Failure of assertion at line 1231, column 21.")
                                                      /\ UNCHANGED Ofa2InstallerBuff
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED ofaInMsg
                                      ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED << switchLock, 
                                                           Ofa2InstallerBuff >>
                                /\ UNCHANGED << controllerLock, 
                                                FirstInstallOFC, 
                                                FirstInstallNIB, 
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
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                IRQueueRC, 
                                                SwSuspensionStatusRC, 
                                                SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                controllerStateOFC, 
                                                IRStatusOFC, IRQueueOFC, 
                                                SwSuspensionStatusOFC, 
                                                SetScheduledIRsOFC, 
                                                FlagOFCWorkerFailover, 
                                                FlagOFCMonitorFailover, 
                                                FlagOFCNIBEventHandlerFailover, 
                                                OFCThreadID, OFC_READY, 
                                                NIB2OFC, NIB2RC, X2NIB, 
                                                OFC2NIB, RC2NIB, 
                                                FlagNIBFailover, 
                                                FlagNIBRCEventhandlerFailover, 
                                                FlagNIBOFCEventhandlerFailover, 
                                                NIB_READY_FOR_RC, 
                                                NIB_READY_FOR_OFC, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, X2NIB_len, 
                                                NIBThreadID, RCThreadID, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug, NIBMsg_, 
                                                isBootStrap_, toBeScheduledIRs, 
                                                key, op1_, op2, transaction_, 
                                                nextIR, stepOfFailure_c, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure, 
                                                transaction_c, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, msg, 
                                                op_ir_status_change, 
                                                op_first_install, transaction >>

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
                                    "Failure of assertion at line 1252, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                          FirstInstallNIB, 
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
                                          IR2SW, NIBUpdateForRC, 
                                          controllerStateRC, IRStatusRC, 
                                          IRQueueRC, SwSuspensionStatusRC, 
                                          SetScheduledIRsRC, 
                                          FlagRCNIBEventHandlerFailover, 
                                          FlagRCSequencerFailover, RC_READY, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          controllerStateOFC, IRStatusOFC, 
                                          IRQueueOFC, SwSuspensionStatusOFC, 
                                          SetScheduledIRsOFC, 
                                          FlagOFCWorkerFailover, 
                                          FlagOFCMonitorFailover, 
                                          FlagOFCNIBEventHandlerFailover, 
                                          OFCThreadID, OFC_READY, NIB2OFC, 
                                          NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                          FlagNIBFailover, 
                                          FlagNIBRCEventhandlerFailover, 
                                          FlagNIBOFCEventhandlerFailover, 
                                          NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                          masterState, controllerStateNIB, 
                                          IRStatus, SwSuspensionStatus, 
                                          IRQueueNIB, SetScheduledIRs, 
                                          X2NIB_len, NIBThreadID, RCThreadID, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          value_, nextTrans_, value_N, 
                                          rowRemove_, IR2Remove_, 
                                          send_NIB_back_, stepOfFailure_, 
                                          IRIndex_, debug_, nextTrans, value, 
                                          rowRemove_N, IR2Remove, 
                                          send_NIB_back, stepOfFailure_N, 
                                          IRIndex, debug, NIBMsg_, 
                                          isBootStrap_, toBeScheduledIRs, key, 
                                          op1_, op2, transaction_, nextIR, 
                                          stepOfFailure_c, transaction_O, 
                                          IRQueueTmp, NIBMsg_O, isBootStrap, 
                                          localIRSet, NIBIRSet, nextIRToSent, 
                                          rowIndex, rowRemove, stepOfFailure, 
                                          transaction_c, NIBMsg, op1, IRQueue, 
                                          op_ir_status_change_, removeIR, msg, 
                                          op_ir_status_change, 
                                          op_first_install, transaction >>

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
                                                      FirstInstallOFC, 
                                                      FirstInstallNIB, 
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
                                                      NIBUpdateForRC, 
                                                      controllerStateRC, 
                                                      IRStatusRC, IRQueueRC, 
                                                      SwSuspensionStatusRC, 
                                                      SetScheduledIRsRC, 
                                                      FlagRCNIBEventHandlerFailover, 
                                                      FlagRCSequencerFailover, 
                                                      RC_READY, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      controllerStateOFC, 
                                                      IRStatusOFC, IRQueueOFC, 
                                                      SwSuspensionStatusOFC, 
                                                      SetScheduledIRsOFC, 
                                                      FlagOFCWorkerFailover, 
                                                      FlagOFCMonitorFailover, 
                                                      FlagOFCNIBEventHandlerFailover, 
                                                      OFCThreadID, OFC_READY, 
                                                      NIB2OFC, NIB2RC, X2NIB, 
                                                      OFC2NIB, RC2NIB, 
                                                      FlagNIBFailover, 
                                                      FlagNIBRCEventhandlerFailover, 
                                                      FlagNIBOFCEventhandlerFailover, 
                                                      NIB_READY_FOR_RC, 
                                                      NIB_READY_FOR_OFC, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      X2NIB_len, NIBThreadID, 
                                                      RCThreadID, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, installerInIR, 
                                                      statusMsg, notFailedSet, 
                                                      failedElem, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, value_, 
                                                      nextTrans_, value_N, 
                                                      rowRemove_, IR2Remove_, 
                                                      send_NIB_back_, 
                                                      stepOfFailure_, IRIndex_, 
                                                      debug_, nextTrans, value, 
                                                      rowRemove_N, IR2Remove, 
                                                      send_NIB_back, 
                                                      stepOfFailure_N, IRIndex, 
                                                      debug, NIBMsg_, 
                                                      isBootStrap_, 
                                                      toBeScheduledIRs, key, 
                                                      op1_, op2, transaction_, 
                                                      nextIR, stepOfFailure_c, 
                                                      transaction_O, 
                                                      IRQueueTmp, NIBMsg_O, 
                                                      isBootStrap, localIRSet, 
                                                      NIBIRSet, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure, 
                                                      transaction_c, NIBMsg, 
                                                      op1, IRQueue, 
                                                      op_ir_status_change_, 
                                                      removeIR, msg, 
                                                      op_ir_status_change, 
                                                      op_first_install, 
                                                      transaction >>

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
                                       "Failure of assertion at line 1284, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                             FirstInstallNIB, 
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
                                             IR2SW, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             IRQueueRC, SwSuspensionStatusRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             controllerStateOFC, IRStatusOFC, 
                                             IRQueueOFC, SwSuspensionStatusOFC, 
                                             SetScheduledIRsOFC, 
                                             FlagOFCWorkerFailover, 
                                             FlagOFCMonitorFailover, 
                                             FlagOFCNIBEventHandlerFailover, 
                                             OFCThreadID, OFC_READY, NIB2OFC, 
                                             NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                             FlagNIBFailover, 
                                             FlagNIBRCEventhandlerFailover, 
                                             FlagNIBOFCEventhandlerFailover, 
                                             NIB_READY_FOR_RC, 
                                             NIB_READY_FOR_OFC, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             statusMsg, notFailedSet, 
                                             failedElem, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             value_, nextTrans_, value_N, 
                                             rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug, NIBMsg_, 
                                             isBootStrap_, toBeScheduledIRs, 
                                             key, op1_, op2, transaction_, 
                                             nextIR, stepOfFailure_c, 
                                             transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure, 
                                             transaction_c, NIBMsg, op1, 
                                             IRQueue, op_ir_status_change_, 
                                             removeIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

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
                                                    FirstInstallOFC, 
                                                    FirstInstallNIB, 
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
                                                    NIBUpdateForRC, 
                                                    controllerStateRC, 
                                                    IRStatusRC, IRQueueRC, 
                                                    SwSuspensionStatusRC, 
                                                    SetScheduledIRsRC, 
                                                    FlagRCNIBEventHandlerFailover, 
                                                    FlagRCSequencerFailover, 
                                                    RC_READY, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    controllerStateOFC, 
                                                    IRStatusOFC, IRQueueOFC, 
                                                    SwSuspensionStatusOFC, 
                                                    SetScheduledIRsOFC, 
                                                    FlagOFCWorkerFailover, 
                                                    FlagOFCMonitorFailover, 
                                                    FlagOFCNIBEventHandlerFailover, 
                                                    OFCThreadID, OFC_READY, 
                                                    NIB2OFC, NIB2RC, X2NIB, 
                                                    OFC2NIB, RC2NIB, 
                                                    FlagNIBFailover, 
                                                    FlagNIBRCEventhandlerFailover, 
                                                    FlagNIBOFCEventhandlerFailover, 
                                                    NIB_READY_FOR_RC, 
                                                    NIB_READY_FOR_OFC, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, X2NIB_len, 
                                                    NIBThreadID, RCThreadID, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, value_, 
                                                    nextTrans_, value_N, 
                                                    rowRemove_, IR2Remove_, 
                                                    send_NIB_back_, 
                                                    stepOfFailure_, IRIndex_, 
                                                    debug_, nextTrans, value, 
                                                    rowRemove_N, IR2Remove, 
                                                    send_NIB_back, 
                                                    stepOfFailure_N, IRIndex, 
                                                    debug, NIBMsg_, 
                                                    isBootStrap_, 
                                                    toBeScheduledIRs, key, 
                                                    op1_, op2, transaction_, 
                                                    nextIR, stepOfFailure_c, 
                                                    transaction_O, IRQueueTmp, 
                                                    NIBMsg_O, isBootStrap, 
                                                    localIRSet, NIBIRSet, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure, 
                                                    transaction_c, NIBMsg, op1, 
                                                    IRQueue, 
                                                    op_ir_status_change_, 
                                                    removeIR, msg, 
                                                    op_ir_status_change, 
                                                    op_first_install, 
                                                    transaction >>

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
                                                         FirstInstallOFC, 
                                                         FirstInstallNIB, 
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
                                                         IR2SW, NIBUpdateForRC, 
                                                         controllerStateRC, 
                                                         IRStatusRC, IRQueueRC, 
                                                         SwSuspensionStatusRC, 
                                                         SetScheduledIRsRC, 
                                                         FlagRCNIBEventHandlerFailover, 
                                                         FlagRCSequencerFailover, 
                                                         RC_READY, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         controllerStateOFC, 
                                                         IRStatusOFC, 
                                                         IRQueueOFC, 
                                                         SwSuspensionStatusOFC, 
                                                         SetScheduledIRsOFC, 
                                                         FlagOFCWorkerFailover, 
                                                         FlagOFCMonitorFailover, 
                                                         FlagOFCNIBEventHandlerFailover, 
                                                         OFCThreadID, 
                                                         OFC_READY, NIB2OFC, 
                                                         NIB2RC, X2NIB, 
                                                         OFC2NIB, RC2NIB, 
                                                         FlagNIBFailover, 
                                                         FlagNIBRCEventhandlerFailover, 
                                                         FlagNIBOFCEventhandlerFailover, 
                                                         NIB_READY_FOR_RC, 
                                                         NIB_READY_FOR_OFC, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         X2NIB_len, 
                                                         NIBThreadID, 
                                                         RCThreadID, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, value_, 
                                                         nextTrans_, value_N, 
                                                         rowRemove_, 
                                                         IR2Remove_, 
                                                         send_NIB_back_, 
                                                         stepOfFailure_, 
                                                         IRIndex_, debug_, 
                                                         nextTrans, value, 
                                                         rowRemove_N, 
                                                         IR2Remove, 
                                                         send_NIB_back, 
                                                         stepOfFailure_N, 
                                                         IRIndex, debug, 
                                                         NIBMsg_, isBootStrap_, 
                                                         toBeScheduledIRs, key, 
                                                         op1_, op2, 
                                                         transaction_, nextIR, 
                                                         stepOfFailure_c, 
                                                         transaction_O, 
                                                         IRQueueTmp, NIBMsg_O, 
                                                         isBootStrap, 
                                                         localIRSet, NIBIRSet, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure, 
                                                         transaction_c, NIBMsg, 
                                                         op1, IRQueue, 
                                                         op_ir_status_change_, 
                                                         removeIR, msg, 
                                                         op_ir_status_change, 
                                                         op_first_install, 
                                                         transaction >>

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
                                 "Failure of assertion at line 595, column 9 of macro called at line 1336, column 9.")
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{(self[2])})>> \o Tail(sw_fail_ordering_var)
                       /\ \E elem \in notFailedSet'[self]:
                            failedElem' = [failedElem EXCEPT ![self] = elem]
                       /\ IF failedElem'[self] = "cpu"
                             THEN /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                                  /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                            "Failure of assertion at line 668, column 9 of macro called at line 1345, column 17.")
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
                                                       "Failure of assertion at line 720, column 9 of macro called at line 1348, column 17.")
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
                                                                  "Failure of assertion at line 764, column 9 of macro called at line 1351, column 17.")
                                                        /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                        /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                              THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                             "Failure of assertion at line 767, column 13 of macro called at line 1351, column 17.")
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
                                                                             "Failure of assertion at line 614, column 9 of macro called at line 1354, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                   /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                swID |-> self[2],
                                                                                                                num |-> controlMsgCounter'[self[2]]]]
                                                                   /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                                              ELSE /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 1355, column 14.")
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
                                       FirstInstallOFC, FirstInstallNIB, 
                                       ContProcSet, SwProcSet, 
                                       switch2Controller, installedIRs, TCAM, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       NIBUpdateForRC, controllerStateRC, 
                                       IRStatusRC, IRQueueRC, 
                                       SwSuspensionStatusRC, SetScheduledIRsRC, 
                                       FlagRCNIBEventHandlerFailover, 
                                       FlagRCSequencerFailover, RC_READY, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, controllerStateOFC, 
                                       IRStatusOFC, IRQueueOFC, 
                                       SwSuspensionStatusOFC, 
                                       SetScheduledIRsOFC, 
                                       FlagOFCWorkerFailover, 
                                       FlagOFCMonitorFailover, 
                                       FlagOFCNIBEventHandlerFailover, 
                                       OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, 
                                       X2NIB, OFC2NIB, RC2NIB, FlagNIBFailover, 
                                       FlagNIBRCEventhandlerFailover, 
                                       FlagNIBOFCEventhandlerFailover, 
                                       NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                       masterState, controllerStateNIB, 
                                       IRStatus, SwSuspensionStatus, 
                                       IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                       NIBThreadID, RCThreadID, ingressPkt, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, value_, nextTrans_, 
                                       value_N, rowRemove_, IR2Remove_, 
                                       send_NIB_back_, stepOfFailure_, 
                                       IRIndex_, debug_, nextTrans, value, 
                                       rowRemove_N, IR2Remove, send_NIB_back, 
                                       stepOfFailure_N, IRIndex, debug, 
                                       NIBMsg_, isBootStrap_, toBeScheduledIRs, 
                                       key, op1_, op2, transaction_, nextIR, 
                                       stepOfFailure_c, transaction_O, 
                                       IRQueueTmp, NIBMsg_O, isBootStrap, 
                                       localIRSet, NIBIRSet, nextIRToSent, 
                                       rowIndex, rowRemove, stepOfFailure, 
                                       transaction_c, NIBMsg, op1, IRQueue, 
                                       op_ir_status_change_, removeIR, msg, 
                                       op_ir_status_change, op_first_install, 
                                       transaction >>

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
                                                   "Failure of assertion at line 695, column 9 of macro called at line 1380, column 39.")
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
                                                              "Failure of assertion at line 640, column 9 of macro called at line 1381, column 46.")
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
                                                                         "Failure of assertion at line 742, column 9 of macro called at line 1382, column 42.")
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
                                                                                    "Failure of assertion at line 786, column 9 of macro called at line 1383, column 48.")
                                                                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                               "Failure of assertion at line 789, column 13 of macro called at line 1383, column 48.")
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
                                                                                    "Failure of assertion at line 1384, column 14.")
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
                                              FirstInstallOFC, FirstInstallNIB, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              switch2Controller, installedIRs, 
                                              TCAM, controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, dependencyGraph, 
                                              IR2SW, NIBUpdateForRC, 
                                              controllerStateRC, IRStatusRC, 
                                              IRQueueRC, SwSuspensionStatusRC, 
                                              SetScheduledIRsRC, 
                                              FlagRCNIBEventHandlerFailover, 
                                              FlagRCSequencerFailover, 
                                              RC_READY, idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              controllerStateOFC, IRStatusOFC, 
                                              IRQueueOFC, 
                                              SwSuspensionStatusOFC, 
                                              SetScheduledIRsOFC, 
                                              FlagOFCWorkerFailover, 
                                              FlagOFCMonitorFailover, 
                                              FlagOFCNIBEventHandlerFailover, 
                                              OFCThreadID, OFC_READY, NIB2OFC, 
                                              NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                              FlagNIBFailover, 
                                              FlagNIBRCEventhandlerFailover, 
                                              FlagNIBOFCEventhandlerFailover, 
                                              NIB_READY_FOR_RC, 
                                              NIB_READY_FOR_OFC, masterState, 
                                              controllerStateNIB, IRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, X2NIB_len, 
                                              NIBThreadID, RCThreadID, 
                                              ingressPkt, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, value_, 
                                              nextTrans_, value_N, rowRemove_, 
                                              IR2Remove_, send_NIB_back_, 
                                              stepOfFailure_, IRIndex_, debug_, 
                                              nextTrans, value, rowRemove_N, 
                                              IR2Remove, send_NIB_back, 
                                              stepOfFailure_N, IRIndex, debug, 
                                              NIBMsg_, isBootStrap_, 
                                              toBeScheduledIRs, key, op1_, op2, 
                                              transaction_, nextIR, 
                                              stepOfFailure_c, transaction_O, 
                                              IRQueueTmp, NIBMsg_O, 
                                              isBootStrap, localIRSet, 
                                              NIBIRSet, nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure, 
                                              transaction_c, NIBMsg, op1, 
                                              IRQueue, op_ir_status_change_, 
                                              removeIR, msg, 
                                              op_ir_status_change, 
                                              op_first_install, transaction >>

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
                             "Failure of assertion at line 841, column 9 of macro called at line 1418, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                   FirstInstallNIB, sw_fail_ordering_var, 
                                   ContProcSet, SwProcSet, swSeqChangedStatus, 
                                   controller2Switch, switch2Controller, 
                                   switchStatus, installedIRs, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   dependencyGraph, IR2SW, NIBUpdateForRC, 
                                   controllerStateRC, IRStatusRC, IRQueueRC, 
                                   SwSuspensionStatusRC, SetScheduledIRsRC, 
                                   FlagRCNIBEventHandlerFailover, 
                                   FlagRCSequencerFailover, RC_READY, 
                                   idThreadWorkingOnIR, workerThreadRanking, 
                                   controllerStateOFC, IRStatusOFC, IRQueueOFC, 
                                   SwSuspensionStatusOFC, SetScheduledIRsOFC, 
                                   FlagOFCWorkerFailover, 
                                   FlagOFCMonitorFailover, 
                                   FlagOFCNIBEventHandlerFailover, OFCThreadID, 
                                   OFC_READY, NIB2OFC, NIB2RC, X2NIB, OFC2NIB, 
                                   RC2NIB, FlagNIBFailover, 
                                   FlagNIBRCEventhandlerFailover, 
                                   FlagNIBOFCEventhandlerFailover, 
                                   NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                   masterState, controllerStateNIB, IRStatus, 
                                   SwSuspensionStatus, IRQueueNIB, 
                                   SetScheduledIRs, X2NIB_len, NIBThreadID, 
                                   RCThreadID, ingressPkt, ingressIR, 
                                   egressMsg, ofaInMsg, ofaOutConfirmation, 
                                   installerInIR, statusMsg, notFailedSet, 
                                   failedElem, failedSet, statusResolveMsg, 
                                   recoveredElem, value_, nextTrans_, value_N, 
                                   rowRemove_, IR2Remove_, send_NIB_back_, 
                                   stepOfFailure_, IRIndex_, debug_, nextTrans, 
                                   value, rowRemove_N, IR2Remove, 
                                   send_NIB_back, stepOfFailure_N, IRIndex, 
                                   debug, NIBMsg_, isBootStrap_, 
                                   toBeScheduledIRs, key, op1_, op2, 
                                   transaction_, nextIR, stepOfFailure_c, 
                                   transaction_O, IRQueueTmp, NIBMsg_O, 
                                   isBootStrap, localIRSet, NIBIRSet, 
                                   nextIRToSent, rowIndex, rowRemove, 
                                   stepOfFailure, transaction_c, NIBMsg, op1, 
                                   IRQueue, op_ir_status_change_, removeIR, 
                                   msg, op_ir_status_change, op_first_install, 
                                   transaction >>

ghostUnlockProcess(self) == ghostProc(self)

NIBFailoverResetStates(self) == /\ pc[self] = "NIBFailoverResetStates"
                                /\ controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = Failed /\
                                         controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = Failed
                                /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<nib0,CONT_NIB_OFC_EVENT>>] = InReconciliation,
                                                                                                      ![<<nib0,CONT_NIB_RC_EVENT>>] = InReconciliation]
                                /\ FlagNIBOFCEventhandlerFailover /\ FlagNIBRCEventhandlerFailover
                                /\ NIB2RC' = <<>>
                                /\ NIB2OFC' = <<>>
                                /\ OFC2NIB' = <<>>
                                /\ RC2NIB' = <<>>
                                /\ pc' = [pc EXCEPT ![self] = "NIBFailoverReadOFC"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstallOFC, 
                                                FirstInstallNIB, 
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
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                IRQueueRC, 
                                                SwSuspensionStatusRC, 
                                                SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                controllerStateOFC, 
                                                IRStatusOFC, IRQueueOFC, 
                                                SwSuspensionStatusOFC, 
                                                SetScheduledIRsOFC, 
                                                FlagOFCWorkerFailover, 
                                                FlagOFCMonitorFailover, 
                                                FlagOFCNIBEventHandlerFailover, 
                                                OFCThreadID, OFC_READY, X2NIB, 
                                                FlagNIBFailover, 
                                                FlagNIBRCEventhandlerFailover, 
                                                FlagNIBOFCEventhandlerFailover, 
                                                NIB_READY_FOR_RC, 
                                                NIB_READY_FOR_OFC, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, X2NIB_len, 
                                                NIBThreadID, RCThreadID, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug, NIBMsg_, 
                                                isBootStrap_, toBeScheduledIRs, 
                                                key, op1_, op2, transaction_, 
                                                nextIR, stepOfFailure_c, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure, 
                                                transaction_c, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, msg, 
                                                op_ir_status_change, 
                                                op_first_install, transaction >>

NIBFailoverReadOFC(self) == /\ pc[self] = "NIBFailoverReadOFC"
                            /\ OFC_READY \/ isOFCUp(OFCThreadID)
                            /\ IRStatus' = IRStatusOFC
                            /\ SwSuspensionStatus' = SwSuspensionStatusOFC
                            /\ NIB_READY_FOR_RC' = TRUE
                            /\ pc' = [pc EXCEPT ![self] = "NIBFailoverReadRC"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            IRQueueRC, SwSuspensionStatusRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            controllerStateOFC, IRStatusOFC, 
                                            IRQueueOFC, SwSuspensionStatusOFC, 
                                            SetScheduledIRsOFC, 
                                            FlagOFCWorkerFailover, 
                                            FlagOFCMonitorFailover, 
                                            FlagOFCNIBEventHandlerFailover, 
                                            OFCThreadID, OFC_READY, NIB2OFC, 
                                            NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                            FlagNIBFailover, 
                                            FlagNIBRCEventhandlerFailover, 
                                            FlagNIBOFCEventhandlerFailover, 
                                            NIB_READY_FOR_OFC, masterState, 
                                            controllerStateNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug, NIBMsg_, 
                                            isBootStrap_, toBeScheduledIRs, 
                                            key, op1_, op2, transaction_, 
                                            nextIR, stepOfFailure_c, 
                                            transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, nextIRToSent, rowIndex, 
                                            rowRemove, stepOfFailure, 
                                            transaction_c, NIBMsg, op1, 
                                            IRQueue, op_ir_status_change_, 
                                            removeIR, msg, op_ir_status_change, 
                                            op_first_install, transaction >>

NIBFailoverReadRC(self) == /\ pc[self] = "NIBFailoverReadRC"
                           /\ RC_READY \/ isRCUp(RCThreadID)
                           /\ IRQueueNIB' = IRQueueRC
                           /\ SetScheduledIRs' = SetScheduledIRsRC
                           /\ NIB_READY_FOR_OFC' = TRUE
                           /\ pc' = [pc EXCEPT ![self] = "ChangeNIBStatusToNormal"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstallOFC, FirstInstallNIB, 
                                           sw_fail_ordering_var, ContProcSet, 
                                           SwProcSet, swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           IR2SW, NIBUpdateForRC, 
                                           controllerStateRC, IRStatusRC, 
                                           IRQueueRC, SwSuspensionStatusRC, 
                                           SetScheduledIRsRC, 
                                           FlagRCNIBEventHandlerFailover, 
                                           FlagRCSequencerFailover, RC_READY, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, 
                                           controllerStateOFC, IRStatusOFC, 
                                           IRQueueOFC, SwSuspensionStatusOFC, 
                                           SetScheduledIRsOFC, 
                                           FlagOFCWorkerFailover, 
                                           FlagOFCMonitorFailover, 
                                           FlagOFCNIBEventHandlerFailover, 
                                           OFCThreadID, OFC_READY, NIB2OFC, 
                                           NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                           FlagNIBFailover, 
                                           FlagNIBRCEventhandlerFailover, 
                                           FlagNIBOFCEventhandlerFailover, 
                                           NIB_READY_FOR_RC, masterState, 
                                           controllerStateNIB, IRStatus, 
                                           SwSuspensionStatus, X2NIB_len, 
                                           NIBThreadID, RCThreadID, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, value_, nextTrans_, 
                                           value_N, rowRemove_, IR2Remove_, 
                                           send_NIB_back_, stepOfFailure_, 
                                           IRIndex_, debug_, nextTrans, value, 
                                           rowRemove_N, IR2Remove, 
                                           send_NIB_back, stepOfFailure_N, 
                                           IRIndex, debug, NIBMsg_, 
                                           isBootStrap_, toBeScheduledIRs, key, 
                                           op1_, op2, transaction_, nextIR, 
                                           stepOfFailure_c, transaction_O, 
                                           IRQueueTmp, NIBMsg_O, isBootStrap, 
                                           localIRSet, NIBIRSet, nextIRToSent, 
                                           rowIndex, rowRemove, stepOfFailure, 
                                           transaction_c, NIBMsg, op1, IRQueue, 
                                           op_ir_status_change_, removeIR, msg, 
                                           op_ir_status_change, 
                                           op_first_install, transaction >>

ChangeNIBStatusToNormal(self) == /\ pc[self] = "ChangeNIBStatusToNormal"
                                 /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed,
                                                                                                       ![<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed]
                                 /\ value_' = [value_ EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                              IRQueueNIB |->IRQueueNIB,
                                                                              SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                              SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                 /\ NIB2RC' = Append(NIB2RC, [value |-> value_'[self]])
                                 /\ NIB2OFC' = Append(NIB2OFC, [value |-> value_'[self]])
                                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstallOFC, 
                                                 FirstInstallNIB, 
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
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 IRQueueRC, 
                                                 SwSuspensionStatusRC, 
                                                 SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 controllerStateOFC, 
                                                 IRStatusOFC, IRQueueOFC, 
                                                 SwSuspensionStatusOFC, 
                                                 SetScheduledIRsOFC, 
                                                 FlagOFCWorkerFailover, 
                                                 FlagOFCMonitorFailover, 
                                                 FlagOFCNIBEventHandlerFailover, 
                                                 OFCThreadID, OFC_READY, X2NIB, 
                                                 OFC2NIB, RC2NIB, 
                                                 FlagNIBFailover, 
                                                 FlagNIBRCEventhandlerFailover, 
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, nextTrans_, 
                                                 value_N, rowRemove_, 
                                                 IR2Remove_, send_NIB_back_, 
                                                 stepOfFailure_, IRIndex_, 
                                                 debug_, nextTrans, value, 
                                                 rowRemove_N, IR2Remove, 
                                                 send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug, NIBMsg_, isBootStrap_, 
                                                 toBeScheduledIRs, key, op1_, 
                                                 op2, transaction_, nextIR, 
                                                 stepOfFailure_c, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure, 
                                                 transaction_c, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBFailoverProc(self) == NIBFailoverResetStates(self)
                            \/ NIBFailoverReadOFC(self)
                            \/ NIBFailoverReadRC(self)
                            \/ ChangeNIBStatusToNormal(self)

NIBHandleRCTransactions(self) == /\ pc[self] = "NIBHandleRCTransactions"
                                 /\ pc' = [pc EXCEPT ![self] = "NIBDequeueRCTransaction"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstallOFC, 
                                                 FirstInstallNIB, 
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
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 IRQueueRC, 
                                                 SwSuspensionStatusRC, 
                                                 SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 controllerStateOFC, 
                                                 IRStatusOFC, IRQueueOFC, 
                                                 SwSuspensionStatusOFC, 
                                                 SetScheduledIRsOFC, 
                                                 FlagOFCWorkerFailover, 
                                                 FlagOFCMonitorFailover, 
                                                 FlagOFCNIBEventHandlerFailover, 
                                                 OFCThreadID, OFC_READY, 
                                                 NIB2OFC, NIB2RC, X2NIB, 
                                                 OFC2NIB, RC2NIB, 
                                                 FlagNIBFailover, 
                                                 FlagNIBRCEventhandlerFailover, 
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, value_, 
                                                 nextTrans_, value_N, 
                                                 rowRemove_, IR2Remove_, 
                                                 send_NIB_back_, 
                                                 stepOfFailure_, IRIndex_, 
                                                 debug_, nextTrans, value, 
                                                 rowRemove_N, IR2Remove, 
                                                 send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug, NIBMsg_, isBootStrap_, 
                                                 toBeScheduledIRs, key, op1_, 
                                                 op2, transaction_, nextIR, 
                                                 stepOfFailure_c, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure, 
                                                 transaction_c, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBDequeueRCTransaction(self) == /\ pc[self] = "NIBDequeueRCTransaction"
                                 /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = ""]
                                 /\ IF moduleIsUp(self)
                                       THEN /\ RC2NIB # <<>>
                                            /\ nextTrans_' = [nextTrans_ EXCEPT ![self] = Head(RC2NIB)]
                                            /\ RC2NIB' = Tail(RC2NIB)
                                            /\ pc' = [pc EXCEPT ![self] = "NIBProcessRCTransaction"]
                                            /\ UNCHANGED FlagNIBRCEventhandlerFailover
                                       ELSE /\ FlagNIBRCEventhandlerFailover' = TRUE
                                            /\ pc' = [pc EXCEPT ![self] = "NIBForRCReconciliation"]
                                            /\ UNCHANGED << RC2NIB, nextTrans_ >>
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstallOFC, 
                                                 FirstInstallNIB, 
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
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 IRQueueRC, 
                                                 SwSuspensionStatusRC, 
                                                 SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 controllerStateOFC, 
                                                 IRStatusOFC, IRQueueOFC, 
                                                 SwSuspensionStatusOFC, 
                                                 SetScheduledIRsOFC, 
                                                 FlagOFCWorkerFailover, 
                                                 FlagOFCMonitorFailover, 
                                                 FlagOFCNIBEventHandlerFailover, 
                                                 OFCThreadID, OFC_READY, 
                                                 NIB2OFC, NIB2RC, X2NIB, 
                                                 OFC2NIB, FlagNIBFailover, 
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, value_, 
                                                 value_N, rowRemove_, 
                                                 IR2Remove_, stepOfFailure_, 
                                                 IRIndex_, debug_, nextTrans, 
                                                 value, rowRemove_N, IR2Remove, 
                                                 send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug, NIBMsg_, isBootStrap_, 
                                                 toBeScheduledIRs, key, op1_, 
                                                 op2, transaction_, nextIR, 
                                                 stepOfFailure_c, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure, 
                                                 transaction_c, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBProcessRCTransaction(self) == /\ pc[self] = "NIBProcessRCTransaction"
                                 /\ IF moduleIsUp(self)
                                       THEN /\ IF (nextTrans_[self].name = "PrepareIR")
                                                  THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                                 "Failure of assertion at line 997, column 9 of macro called at line 1569, column 13.")
                                                       /\ Assert(Len(nextTrans_[self].ops[1].key) = 2, 
                                                                 "Failure of assertion at line 998, column 9 of macro called at line 1569, column 13.")
                                                       /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                       /\ Assert(nextTrans_[self].ops[2].table = NIBT_SET_SCHEDULED_IRS, 
                                                                 "Failure of assertion at line 1000, column 9 of macro called at line 1569, column 13.")
                                                       /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans_[self].ops[2].key] = nextTrans_[self].ops[2].value]
                                                       /\ UNCHANGED << FirstInstallNIB, 
                                                                       IRStatus, 
                                                                       IRQueueNIB, 
                                                                       value_N, 
                                                                       rowRemove_, 
                                                                       IR2Remove_, 
                                                                       send_NIB_back_, 
                                                                       IRIndex_ >>
                                                  ELSE /\ IF (nextTrans_[self].name = "ScheduleIR")
                                                             THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                            "Failure of assertion at line 1006, column 9 of macro called at line 1569, column 13.")
                                                                  /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans_[self].ops[1].value)
                                                                  /\ Assert(nextTrans_[self].ops[2].table = NIBT_CONTROLLER_STATE, 
                                                                            "Failure of assertion at line 1008, column 9 of macro called at line 1569, column 13.")
                                                                  /\ Assert(Len(nextTrans_[self].ops[2].key) = 2, 
                                                                            "Failure of assertion at line 1009, column 9 of macro called at line 1569, column 13.")
                                                                  /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans_[self].ops[2].key] = nextTrans_[self].ops[2].value]
                                                                  /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                                 IRQueueNIB |->IRQueueNIB',
                                                                                                                 SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                 SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                  /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2OFC"]
                                                                  /\ UNCHANGED << FirstInstallNIB, 
                                                                                  IRStatus, 
                                                                                  SetScheduledIRs, 
                                                                                  rowRemove_, 
                                                                                  IR2Remove_, 
                                                                                  IRIndex_ >>
                                                             ELSE /\ IF (nextTrans_[self].name = "RCScheduleIRInOneStep")
                                                                        THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                       "Failure of assertion at line 1015, column 9 of macro called at line 1569, column 13.")
                                                                             /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans_[self].ops[1].value)
                                                                             /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                                            IRQueueNIB |->IRQueueNIB',
                                                                                                                            SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                            SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                             /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2OFC"]
                                                                             /\ UNCHANGED << FirstInstallNIB, 
                                                                                             controllerStateNIB, 
                                                                                             IRStatus, 
                                                                                             SetScheduledIRs, 
                                                                                             rowRemove_, 
                                                                                             IR2Remove_, 
                                                                                             IRIndex_ >>
                                                                        ELSE /\ IF (nextTrans_[self].name = "SeqReadNIBStates")
                                                                                   THEN /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                                                       IRQueueNIB |->IRQueueNIB,
                                                                                                                                       SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                       SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                        /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                        /\ UNCHANGED << FirstInstallNIB, 
                                                                                                        controllerStateNIB, 
                                                                                                        IRStatus, 
                                                                                                        IRQueueNIB, 
                                                                                                        SetScheduledIRs, 
                                                                                                        rowRemove_, 
                                                                                                        IR2Remove_, 
                                                                                                        IRIndex_ >>
                                                                                   ELSE /\ IF (nextTrans_[self].name = "OFCOverrideIRStatus")
                                                                                              THEN /\ IRStatus' = nextTrans_[self].ops[1]
                                                                                                   /\ FirstInstallNIB' = nextTrans_[self].ops[2]
                                                                                                   /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatus',
                                                                                                                                                  IRQueueNIB |->IRQueueNIB,
                                                                                                                                                  SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                  SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                   /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                   /\ UNCHANGED << controllerStateNIB, 
                                                                                                                   IRQueueNIB, 
                                                                                                                   SetScheduledIRs, 
                                                                                                                   rowRemove_, 
                                                                                                                   IR2Remove_, 
                                                                                                                   IRIndex_ >>
                                                                                              ELSE /\ IF (nextTrans_[self].name = "OFCReadNIBStates")
                                                                                                         THEN /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                                                                             IRQueueNIB |->IRQueueNIB,
                                                                                                                                                             SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                             SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                              /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2OFC"]
                                                                                                              /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                              controllerStateNIB, 
                                                                                                                              IRStatus, 
                                                                                                                              IRQueueNIB, 
                                                                                                                              SetScheduledIRs, 
                                                                                                                              rowRemove_, 
                                                                                                                              IR2Remove_, 
                                                                                                                              IRIndex_ >>
                                                                                                         ELSE /\ IF (nextTrans_[self].name = "UpdateControllerState")
                                                                                                                    THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                                                                                                   "Failure of assertion at line 1049, column 17 of macro called at line 1569, column 13.")
                                                                                                                         /\ Assert(Len(nextTrans_[self].ops[1].key) = 2, 
                                                                                                                                   "Failure of assertion at line 1050, column 17 of macro called at line 1569, column 13.")
                                                                                                                         /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                         /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                         IRStatus, 
                                                                                                                                         IRQueueNIB, 
                                                                                                                                         SetScheduledIRs, 
                                                                                                                                         value_N, 
                                                                                                                                         rowRemove_, 
                                                                                                                                         IR2Remove_, 
                                                                                                                                         send_NIB_back_, 
                                                                                                                                         IRIndex_ >>
                                                                                                                    ELSE /\ IF (nextTrans_[self].name = "RemoveIR")
                                                                                                                               THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                              "Failure of assertion at line 1053, column 17 of macro called at line 1569, column 13.")
                                                                                                                                    /\ IR2Remove_' = [IR2Remove_ EXCEPT ![self] = nextTrans_[self].ops[1].key]
                                                                                                                                    /\ IF \E i \in DOMAIN IRQueueNIB: IRQueueNIB[i].IR = IR2Remove_'[self]
                                                                                                                                          THEN /\ rowRemove_' = [rowRemove_ EXCEPT ![self] = getFirstIndexWithNIB(IR2Remove_'[self], IRQueueNIB)]
                                                                                                                                               /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove_'[self])
                                                                                                                                          ELSE /\ TRUE
                                                                                                                                               /\ UNCHANGED << IRQueueNIB, 
                                                                                                                                                               rowRemove_ >>
                                                                                                                                    /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                    IRStatus, 
                                                                                                                                                    SetScheduledIRs, 
                                                                                                                                                    value_N, 
                                                                                                                                                    send_NIB_back_, 
                                                                                                                                                    IRIndex_ >>
                                                                                                                               ELSE /\ IF (nextTrans_[self].name = "OFCChangeIRStatus2Sent")
                                                                                                                                          THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                         "Failure of assertion at line 1061, column 17 of macro called at line 1569, column 13.")
                                                                                                                                               /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                         "Failure of assertion at line 1062, column 17 of macro called at line 1569, column 13.")
                                                                                                                                               /\ IRStatus' = [IRStatus EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                               /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatus',
                                                                                                                                                                                              IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                              SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                              SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                                                               /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                                                               /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                               IRQueueNIB, 
                                                                                                                                                               SetScheduledIRs, 
                                                                                                                                                               IRIndex_ >>
                                                                                                                                          ELSE /\ IF (nextTrans_[self].name = "ChangeSetScheduledIRs")
                                                                                                                                                     THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_SET_SCHEDULED_IRS, 
                                                                                                                                                                    "Failure of assertion at line 1067, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                          /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                                    "Failure of assertion at line 1068, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                          /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                                          /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                          IRStatus, 
                                                                                                                                                                          IRQueueNIB, 
                                                                                                                                                                          value_N, 
                                                                                                                                                                          send_NIB_back_, 
                                                                                                                                                                          IRIndex_ >>
                                                                                                                                                     ELSE /\ IF (nextTrans_[self].name = "UpdateIRTag")
                                                                                                                                                                THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                                                               "Failure of assertion at line 1071, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                                     /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                                               "Failure of assertion at line 1072, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                                     /\ Assert(Len(IRQueueNIB) > 0, 
                                                                                                                                                                               "Failure of assertion at line 1073, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                                     /\ IRIndex_' = [IRIndex_ EXCEPT ![self] = CHOOSE x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans_[self].ops[1].key]
                                                                                                                                                                     /\ Assert(IRIndex_'[self] # -1, 
                                                                                                                                                                               "Failure of assertion at line 1075, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                                     /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![IRIndex_'[self]].tag = nextTrans_[self].ops[1].value]
                                                                                                                                                                     /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                                     IRStatus, 
                                                                                                                                                                                     value_N, 
                                                                                                                                                                                     send_NIB_back_ >>
                                                                                                                                                                ELSE /\ IF (nextTrans_[self].name = "FirstInstallIR")
                                                                                                                                                                           THEN /\ Assert(Len(nextTrans_[self].ops) = 2, 
                                                                                                                                                                                          "Failure of assertion at line 1078, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                                                /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                                                          "Failure of assertion at line 1079, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                                                /\ IRStatus' = [IRStatus EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                                                                /\ Assert(nextTrans_[self].ops[2].table = NIBT_FIRST_INSTALL, 
                                                                                                                                                                                          "Failure of assertion at line 1081, column 17 of macro called at line 1569, column 13.")
                                                                                                                                                                                /\ FirstInstallNIB' = [FirstInstallNIB EXCEPT ![nextTrans_[self].ops[2].key] = nextTrans_[self].ops[2].value]
                                                                                                                                                                                /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatus',
                                                                                                                                                                                                                               IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                               SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                               SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                                                                                                /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                           ELSE /\ TRUE
                                                                                                                                                                                /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                                                IRStatus, 
                                                                                                                                                                                                value_N, 
                                                                                                                                                                                                send_NIB_back_ >>
                                                                                                                                                                     /\ UNCHANGED << IRQueueNIB, 
                                                                                                                                                                                     IRIndex_ >>
                                                                                                                                                          /\ UNCHANGED SetScheduledIRs
                                                                                                                                    /\ UNCHANGED << rowRemove_, 
                                                                                                                                                    IR2Remove_ >>
                                                                                                                         /\ UNCHANGED controllerStateNIB
                                            /\ debug_' = [debug_ EXCEPT ![self] = 0]
                                            /\ pc' = [pc EXCEPT ![self] = "NIBUpdateRCIfAny"]
                                            /\ UNCHANGED FlagNIBRCEventhandlerFailover
                                       ELSE /\ FlagNIBRCEventhandlerFailover' = TRUE
                                            /\ pc' = [pc EXCEPT ![self] = "NIBForRCReconciliation"]
                                            /\ UNCHANGED << FirstInstallNIB, 
                                                            controllerStateNIB, 
                                                            IRStatus, 
                                                            IRQueueNIB, 
                                                            SetScheduledIRs, 
                                                            value_N, 
                                                            rowRemove_, 
                                                            IR2Remove_, 
                                                            send_NIB_back_, 
                                                            IRIndex_, debug_ >>
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstallOFC, 
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
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 IRQueueRC, 
                                                 SwSuspensionStatusRC, 
                                                 SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 controllerStateOFC, 
                                                 IRStatusOFC, IRQueueOFC, 
                                                 SwSuspensionStatusOFC, 
                                                 SetScheduledIRsOFC, 
                                                 FlagOFCWorkerFailover, 
                                                 FlagOFCMonitorFailover, 
                                                 FlagOFCNIBEventHandlerFailover, 
                                                 OFCThreadID, OFC_READY, 
                                                 NIB2OFC, NIB2RC, X2NIB, 
                                                 OFC2NIB, RC2NIB, 
                                                 FlagNIBFailover, 
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, 
                                                 SwSuspensionStatus, X2NIB_len, 
                                                 NIBThreadID, RCThreadID, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, value_, 
                                                 nextTrans_, stepOfFailure_, 
                                                 nextTrans, value, rowRemove_N, 
                                                 IR2Remove, send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug, NIBMsg_, isBootStrap_, 
                                                 toBeScheduledIRs, key, op1_, 
                                                 op2, transaction_, nextIR, 
                                                 stepOfFailure_c, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure, 
                                                 transaction_c, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBUpdateRCIfAny(self) == /\ pc[self] = "NIBUpdateRCIfAny"
                          /\ IF moduleIsUp(self)
                                THEN /\ IF send_NIB_back_[self] = "NIB2RC"
                                           THEN /\ isRCUp(RCThreadID) \/ isRCFailed(RCThreadID)
                                                /\ NIB2RC' = Append(NIB2RC, [value |-> value_N[self]])
                                                /\ UNCHANGED NIB2OFC
                                           ELSE /\ IF send_NIB_back_[self] = "NIB2OFC"
                                                      THEN /\ isOFCUp(RCThreadID) \/ isOFCFailed(RCThreadID)
                                                           /\ NIB2OFC' = Append(NIB2OFC, [value |-> value_N[self]])
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED NIB2OFC
                                                /\ UNCHANGED NIB2RC
                                     /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = ""]
                                     /\ pc' = [pc EXCEPT ![self] = "NIBHandleRCTransactions"]
                                     /\ UNCHANGED FlagNIBRCEventhandlerFailover
                                ELSE /\ FlagNIBRCEventhandlerFailover' = TRUE
                                     /\ pc' = [pc EXCEPT ![self] = "NIBForRCReconciliation"]
                                     /\ UNCHANGED << NIB2OFC, NIB2RC, 
                                                     send_NIB_back_ >>
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstallOFC, FirstInstallNIB, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, NIBUpdateForRC, 
                                          controllerStateRC, IRStatusRC, 
                                          IRQueueRC, SwSuspensionStatusRC, 
                                          SetScheduledIRsRC, 
                                          FlagRCNIBEventHandlerFailover, 
                                          FlagRCSequencerFailover, RC_READY, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          controllerStateOFC, IRStatusOFC, 
                                          IRQueueOFC, SwSuspensionStatusOFC, 
                                          SetScheduledIRsOFC, 
                                          FlagOFCWorkerFailover, 
                                          FlagOFCMonitorFailover, 
                                          FlagOFCNIBEventHandlerFailover, 
                                          OFCThreadID, OFC_READY, X2NIB, 
                                          OFC2NIB, RC2NIB, FlagNIBFailover, 
                                          FlagNIBOFCEventhandlerFailover, 
                                          NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                          masterState, controllerStateNIB, 
                                          IRStatus, SwSuspensionStatus, 
                                          IRQueueNIB, SetScheduledIRs, 
                                          X2NIB_len, NIBThreadID, RCThreadID, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          value_, nextTrans_, value_N, 
                                          rowRemove_, IR2Remove_, 
                                          stepOfFailure_, IRIndex_, debug_, 
                                          nextTrans, value, rowRemove_N, 
                                          IR2Remove, send_NIB_back, 
                                          stepOfFailure_N, IRIndex, debug, 
                                          NIBMsg_, isBootStrap_, 
                                          toBeScheduledIRs, key, op1_, op2, 
                                          transaction_, nextIR, 
                                          stepOfFailure_c, transaction_O, 
                                          IRQueueTmp, NIBMsg_O, isBootStrap, 
                                          localIRSet, NIBIRSet, nextIRToSent, 
                                          rowIndex, rowRemove, stepOfFailure, 
                                          transaction_c, NIBMsg, op1, IRQueue, 
                                          op_ir_status_change_, removeIR, msg, 
                                          op_ir_status_change, 
                                          op_first_install, transaction >>

NIBForRCReconciliation(self) == /\ pc[self] = "NIBForRCReconciliation"
                                /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
                                   controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed
                                /\ pc' = [pc EXCEPT ![self] = "NIBHandleRCTransactions"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstallOFC, 
                                                FirstInstallNIB, 
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
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                IRQueueRC, 
                                                SwSuspensionStatusRC, 
                                                SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                controllerStateOFC, 
                                                IRStatusOFC, IRQueueOFC, 
                                                SwSuspensionStatusOFC, 
                                                SetScheduledIRsOFC, 
                                                FlagOFCWorkerFailover, 
                                                FlagOFCMonitorFailover, 
                                                FlagOFCNIBEventHandlerFailover, 
                                                OFCThreadID, OFC_READY, 
                                                NIB2OFC, NIB2RC, X2NIB, 
                                                OFC2NIB, RC2NIB, 
                                                FlagNIBFailover, 
                                                FlagNIBRCEventhandlerFailover, 
                                                FlagNIBOFCEventhandlerFailover, 
                                                NIB_READY_FOR_RC, 
                                                NIB_READY_FOR_OFC, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, X2NIB_len, 
                                                NIBThreadID, RCThreadID, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug, NIBMsg_, 
                                                isBootStrap_, toBeScheduledIRs, 
                                                key, op1_, op2, transaction_, 
                                                nextIR, stepOfFailure_c, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure, 
                                                transaction_c, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, msg, 
                                                op_ir_status_change, 
                                                op_first_install, transaction >>

NIBRCEventHandler(self) == NIBHandleRCTransactions(self)
                              \/ NIBDequeueRCTransaction(self)
                              \/ NIBProcessRCTransaction(self)
                              \/ NIBUpdateRCIfAny(self)
                              \/ NIBForRCReconciliation(self)

NIBHandleOFCTransactions(self) == /\ pc[self] = "NIBHandleOFCTransactions"
                                  /\ pc' = [pc EXCEPT ![self] = "NIBDequeueOFCTransaction"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstallOFC, 
                                                  FirstInstallNIB, 
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
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, IRQueueRC, 
                                                  SwSuspensionStatusRC, 
                                                  SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  controllerStateOFC, 
                                                  IRStatusOFC, IRQueueOFC, 
                                                  SwSuspensionStatusOFC, 
                                                  SetScheduledIRsOFC, 
                                                  FlagOFCWorkerFailover, 
                                                  FlagOFCMonitorFailover, 
                                                  FlagOFCNIBEventHandlerFailover, 
                                                  OFCThreadID, OFC_READY, 
                                                  NIB2OFC, NIB2RC, X2NIB, 
                                                  OFC2NIB, RC2NIB, 
                                                  FlagNIBFailover, 
                                                  FlagNIBRCEventhandlerFailover, 
                                                  FlagNIBOFCEventhandlerFailover, 
                                                  NIB_READY_FOR_RC, 
                                                  NIB_READY_FOR_OFC, 
                                                  masterState, 
                                                  controllerStateNIB, IRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, value_, 
                                                  nextTrans_, value_N, 
                                                  rowRemove_, IR2Remove_, 
                                                  send_NIB_back_, 
                                                  stepOfFailure_, IRIndex_, 
                                                  debug_, nextTrans, value, 
                                                  rowRemove_N, IR2Remove, 
                                                  send_NIB_back, 
                                                  stepOfFailure_N, IRIndex, 
                                                  debug, NIBMsg_, isBootStrap_, 
                                                  toBeScheduledIRs, key, op1_, 
                                                  op2, transaction_, nextIR, 
                                                  stepOfFailure_c, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure, 
                                                  transaction_c, NIBMsg, op1, 
                                                  IRQueue, 
                                                  op_ir_status_change_, 
                                                  removeIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

NIBDequeueOFCTransaction(self) == /\ pc[self] = "NIBDequeueOFCTransaction"
                                  /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = ""]
                                  /\ IF moduleIsUp(self)
                                        THEN /\ OFC2NIB # <<>>
                                             /\ nextTrans' = [nextTrans EXCEPT ![self] = Head(OFC2NIB)]
                                             /\ OFC2NIB' = Tail(OFC2NIB)
                                             /\ pc' = [pc EXCEPT ![self] = "NIBProcessTransaction"]
                                             /\ UNCHANGED FlagNIBOFCEventhandlerFailover
                                        ELSE /\ FlagNIBOFCEventhandlerFailover' = TRUE
                                             /\ pc' = [pc EXCEPT ![self] = "NIBForOFCReconciliation"]
                                             /\ UNCHANGED << OFC2NIB, 
                                                             nextTrans >>
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstallOFC, 
                                                  FirstInstallNIB, 
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
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, IRQueueRC, 
                                                  SwSuspensionStatusRC, 
                                                  SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  controllerStateOFC, 
                                                  IRStatusOFC, IRQueueOFC, 
                                                  SwSuspensionStatusOFC, 
                                                  SetScheduledIRsOFC, 
                                                  FlagOFCWorkerFailover, 
                                                  FlagOFCMonitorFailover, 
                                                  FlagOFCNIBEventHandlerFailover, 
                                                  OFCThreadID, OFC_READY, 
                                                  NIB2OFC, NIB2RC, X2NIB, 
                                                  RC2NIB, FlagNIBFailover, 
                                                  FlagNIBRCEventhandlerFailover, 
                                                  NIB_READY_FOR_RC, 
                                                  NIB_READY_FOR_OFC, 
                                                  masterState, 
                                                  controllerStateNIB, IRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, value_, 
                                                  nextTrans_, value_N, 
                                                  rowRemove_, IR2Remove_, 
                                                  send_NIB_back_, 
                                                  stepOfFailure_, IRIndex_, 
                                                  debug_, value, rowRemove_N, 
                                                  IR2Remove, stepOfFailure_N, 
                                                  IRIndex, debug, NIBMsg_, 
                                                  isBootStrap_, 
                                                  toBeScheduledIRs, key, op1_, 
                                                  op2, transaction_, nextIR, 
                                                  stepOfFailure_c, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure, 
                                                  transaction_c, NIBMsg, op1, 
                                                  IRQueue, 
                                                  op_ir_status_change_, 
                                                  removeIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

NIBProcessTransaction(self) == /\ pc[self] = "NIBProcessTransaction"
                               /\ IF moduleIsUp(self)
                                     THEN /\ IF (nextTrans[self].name = "PrepareIR")
                                                THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                               "Failure of assertion at line 997, column 9 of macro called at line 1621, column 13.")
                                                     /\ Assert(Len(nextTrans[self].ops[1].key) = 2, 
                                                               "Failure of assertion at line 998, column 9 of macro called at line 1621, column 13.")
                                                     /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                     /\ Assert(nextTrans[self].ops[2].table = NIBT_SET_SCHEDULED_IRS, 
                                                               "Failure of assertion at line 1000, column 9 of macro called at line 1621, column 13.")
                                                     /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans[self].ops[2].key] = nextTrans[self].ops[2].value]
                                                     /\ UNCHANGED << FirstInstallNIB, 
                                                                     IRStatus, 
                                                                     IRQueueNIB, 
                                                                     value, 
                                                                     rowRemove_N, 
                                                                     IR2Remove, 
                                                                     send_NIB_back, 
                                                                     IRIndex >>
                                                ELSE /\ IF (nextTrans[self].name = "ScheduleIR")
                                                           THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                          "Failure of assertion at line 1006, column 9 of macro called at line 1621, column 13.")
                                                                /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans[self].ops[1].value)
                                                                /\ Assert(nextTrans[self].ops[2].table = NIBT_CONTROLLER_STATE, 
                                                                          "Failure of assertion at line 1008, column 9 of macro called at line 1621, column 13.")
                                                                /\ Assert(Len(nextTrans[self].ops[2].key) = 2, 
                                                                          "Failure of assertion at line 1009, column 9 of macro called at line 1621, column 13.")
                                                                /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans[self].ops[2].key] = nextTrans[self].ops[2].value]
                                                                /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                           IRQueueNIB |->IRQueueNIB',
                                                                                                           SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                           SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2OFC"]
                                                                /\ UNCHANGED << FirstInstallNIB, 
                                                                                IRStatus, 
                                                                                SetScheduledIRs, 
                                                                                rowRemove_N, 
                                                                                IR2Remove, 
                                                                                IRIndex >>
                                                           ELSE /\ IF (nextTrans[self].name = "RCScheduleIRInOneStep")
                                                                      THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                     "Failure of assertion at line 1015, column 9 of macro called at line 1621, column 13.")
                                                                           /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans[self].ops[1].value)
                                                                           /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                                      IRQueueNIB |->IRQueueNIB',
                                                                                                                      SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                      SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                           /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2OFC"]
                                                                           /\ UNCHANGED << FirstInstallNIB, 
                                                                                           controllerStateNIB, 
                                                                                           IRStatus, 
                                                                                           SetScheduledIRs, 
                                                                                           rowRemove_N, 
                                                                                           IR2Remove, 
                                                                                           IRIndex >>
                                                                      ELSE /\ IF (nextTrans[self].name = "SeqReadNIBStates")
                                                                                 THEN /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                                                 IRQueueNIB |->IRQueueNIB,
                                                                                                                                 SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                 SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                      /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                      /\ UNCHANGED << FirstInstallNIB, 
                                                                                                      controllerStateNIB, 
                                                                                                      IRStatus, 
                                                                                                      IRQueueNIB, 
                                                                                                      SetScheduledIRs, 
                                                                                                      rowRemove_N, 
                                                                                                      IR2Remove, 
                                                                                                      IRIndex >>
                                                                                 ELSE /\ IF (nextTrans[self].name = "OFCOverrideIRStatus")
                                                                                            THEN /\ IRStatus' = nextTrans[self].ops[1]
                                                                                                 /\ FirstInstallNIB' = nextTrans[self].ops[2]
                                                                                                 /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatus',
                                                                                                                                            IRQueueNIB |->IRQueueNIB,
                                                                                                                                            SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                            SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                 /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                 /\ UNCHANGED << controllerStateNIB, 
                                                                                                                 IRQueueNIB, 
                                                                                                                 SetScheduledIRs, 
                                                                                                                 rowRemove_N, 
                                                                                                                 IR2Remove, 
                                                                                                                 IRIndex >>
                                                                                            ELSE /\ IF (nextTrans[self].name = "OFCReadNIBStates")
                                                                                                       THEN /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatus,
                                                                                                                                                       IRQueueNIB |->IRQueueNIB,
                                                                                                                                                       SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                       SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                            /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2OFC"]
                                                                                                            /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                            controllerStateNIB, 
                                                                                                                            IRStatus, 
                                                                                                                            IRQueueNIB, 
                                                                                                                            SetScheduledIRs, 
                                                                                                                            rowRemove_N, 
                                                                                                                            IR2Remove, 
                                                                                                                            IRIndex >>
                                                                                                       ELSE /\ IF (nextTrans[self].name = "UpdateControllerState")
                                                                                                                  THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                                                                                                 "Failure of assertion at line 1049, column 17 of macro called at line 1621, column 13.")
                                                                                                                       /\ Assert(Len(nextTrans[self].ops[1].key) = 2, 
                                                                                                                                 "Failure of assertion at line 1050, column 17 of macro called at line 1621, column 13.")
                                                                                                                       /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                       /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                       IRStatus, 
                                                                                                                                       IRQueueNIB, 
                                                                                                                                       SetScheduledIRs, 
                                                                                                                                       value, 
                                                                                                                                       rowRemove_N, 
                                                                                                                                       IR2Remove, 
                                                                                                                                       send_NIB_back, 
                                                                                                                                       IRIndex >>
                                                                                                                  ELSE /\ IF (nextTrans[self].name = "RemoveIR")
                                                                                                                             THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                            "Failure of assertion at line 1053, column 17 of macro called at line 1621, column 13.")
                                                                                                                                  /\ IR2Remove' = [IR2Remove EXCEPT ![self] = nextTrans[self].ops[1].key]
                                                                                                                                  /\ IF \E i \in DOMAIN IRQueueNIB: IRQueueNIB[i].IR = IR2Remove'[self]
                                                                                                                                        THEN /\ rowRemove_N' = [rowRemove_N EXCEPT ![self] = getFirstIndexWithNIB(IR2Remove'[self], IRQueueNIB)]
                                                                                                                                             /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove_N'[self])
                                                                                                                                        ELSE /\ TRUE
                                                                                                                                             /\ UNCHANGED << IRQueueNIB, 
                                                                                                                                                             rowRemove_N >>
                                                                                                                                  /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                  IRStatus, 
                                                                                                                                                  SetScheduledIRs, 
                                                                                                                                                  value, 
                                                                                                                                                  send_NIB_back, 
                                                                                                                                                  IRIndex >>
                                                                                                                             ELSE /\ IF (nextTrans[self].name = "OFCChangeIRStatus2Sent")
                                                                                                                                        THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                       "Failure of assertion at line 1061, column 17 of macro called at line 1621, column 13.")
                                                                                                                                             /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                       "Failure of assertion at line 1062, column 17 of macro called at line 1621, column 13.")
                                                                                                                                             /\ IRStatus' = [IRStatus EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                             /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatus',
                                                                                                                                                                                        IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                        SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                        SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                                                             /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                                                             /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                             IRQueueNIB, 
                                                                                                                                                             SetScheduledIRs, 
                                                                                                                                                             IRIndex >>
                                                                                                                                        ELSE /\ IF (nextTrans[self].name = "ChangeSetScheduledIRs")
                                                                                                                                                   THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_SET_SCHEDULED_IRS, 
                                                                                                                                                                  "Failure of assertion at line 1067, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                        /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                                  "Failure of assertion at line 1068, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                        /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                                        /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                        IRStatus, 
                                                                                                                                                                        IRQueueNIB, 
                                                                                                                                                                        value, 
                                                                                                                                                                        send_NIB_back, 
                                                                                                                                                                        IRIndex >>
                                                                                                                                                   ELSE /\ IF (nextTrans[self].name = "UpdateIRTag")
                                                                                                                                                              THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                                                             "Failure of assertion at line 1071, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                                   /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                                             "Failure of assertion at line 1072, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                                   /\ Assert(Len(IRQueueNIB) > 0, 
                                                                                                                                                                             "Failure of assertion at line 1073, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                                   /\ IRIndex' = [IRIndex EXCEPT ![self] = CHOOSE x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans[self].ops[1].key]
                                                                                                                                                                   /\ Assert(IRIndex'[self] # -1, 
                                                                                                                                                                             "Failure of assertion at line 1075, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                                   /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![IRIndex'[self]].tag = nextTrans[self].ops[1].value]
                                                                                                                                                                   /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                                   IRStatus, 
                                                                                                                                                                                   value, 
                                                                                                                                                                                   send_NIB_back >>
                                                                                                                                                              ELSE /\ IF (nextTrans[self].name = "FirstInstallIR")
                                                                                                                                                                         THEN /\ Assert(Len(nextTrans[self].ops) = 2, 
                                                                                                                                                                                        "Failure of assertion at line 1078, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                                              /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                                                        "Failure of assertion at line 1079, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                                              /\ IRStatus' = [IRStatus EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                                                              /\ Assert(nextTrans[self].ops[2].table = NIBT_FIRST_INSTALL, 
                                                                                                                                                                                        "Failure of assertion at line 1081, column 17 of macro called at line 1621, column 13.")
                                                                                                                                                                              /\ FirstInstallNIB' = [FirstInstallNIB EXCEPT ![nextTrans[self].ops[2].key] = nextTrans[self].ops[2].value]
                                                                                                                                                                              /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatus',
                                                                                                                                                                                                                         IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                         SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                         SwSuspensionStatusNIB |-> SwSuspensionStatus]]
                                                                                                                                                                              /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                         ELSE /\ TRUE
                                                                                                                                                                              /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                                              IRStatus, 
                                                                                                                                                                                              value, 
                                                                                                                                                                                              send_NIB_back >>
                                                                                                                                                                   /\ UNCHANGED << IRQueueNIB, 
                                                                                                                                                                                   IRIndex >>
                                                                                                                                                        /\ UNCHANGED SetScheduledIRs
                                                                                                                                  /\ UNCHANGED << rowRemove_N, 
                                                                                                                                                  IR2Remove >>
                                                                                                                       /\ UNCHANGED controllerStateNIB
                                          /\ debug' = [debug EXCEPT ![self] = 0]
                                          /\ pc' = [pc EXCEPT ![self] = "NIBSendBackIfAny"]
                                          /\ UNCHANGED FlagNIBOFCEventhandlerFailover
                                     ELSE /\ FlagNIBOFCEventhandlerFailover' = TRUE
                                          /\ pc' = [pc EXCEPT ![self] = "NIBForOFCReconciliation"]
                                          /\ UNCHANGED << FirstInstallNIB, 
                                                          controllerStateNIB, 
                                                          IRStatus, IRQueueNIB, 
                                                          SetScheduledIRs, 
                                                          value, rowRemove_N, 
                                                          IR2Remove, 
                                                          send_NIB_back, 
                                                          IRIndex, debug >>
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstallOFC, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, dependencyGraph, 
                                               IR2SW, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               IRQueueRC, SwSuspensionStatusRC, 
                                               SetScheduledIRsRC, 
                                               FlagRCNIBEventHandlerFailover, 
                                               FlagRCSequencerFailover, 
                                               RC_READY, idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               controllerStateOFC, IRStatusOFC, 
                                               IRQueueOFC, 
                                               SwSuspensionStatusOFC, 
                                               SetScheduledIRsOFC, 
                                               FlagOFCWorkerFailover, 
                                               FlagOFCMonitorFailover, 
                                               FlagOFCNIBEventHandlerFailover, 
                                               OFCThreadID, OFC_READY, NIB2OFC, 
                                               NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                               FlagNIBFailover, 
                                               FlagNIBRCEventhandlerFailover, 
                                               NIB_READY_FOR_RC, 
                                               NIB_READY_FOR_OFC, masterState, 
                                               SwSuspensionStatus, X2NIB_len, 
                                               NIBThreadID, RCThreadID, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, 
                                               stepOfFailure_N, NIBMsg_, 
                                               isBootStrap_, toBeScheduledIRs, 
                                               key, op1_, op2, transaction_, 
                                               nextIR, stepOfFailure_c, 
                                               transaction_O, IRQueueTmp, 
                                               NIBMsg_O, isBootStrap, 
                                               localIRSet, NIBIRSet, 
                                               nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure, 
                                               transaction_c, NIBMsg, op1, 
                                               IRQueue, op_ir_status_change_, 
                                               removeIR, msg, 
                                               op_ir_status_change, 
                                               op_first_install, transaction >>

NIBSendBackIfAny(self) == /\ pc[self] = "NIBSendBackIfAny"
                          /\ IF moduleIsUp(self)
                                THEN /\ IF send_NIB_back[self] = "NIB2RC"
                                           THEN /\ isRCUp(RCThreadID) \/ isRCFailed(RCThreadID)
                                                /\ NIB2RC' = Append(NIB2RC, [value |-> value[self]])
                                                /\ UNCHANGED NIB2OFC
                                           ELSE /\ IF send_NIB_back[self] = "NIB2OFC"
                                                      THEN /\ isOFCUp(RCThreadID) \/ isOFCFailed(RCThreadID)
                                                           /\ NIB2OFC' = Append(NIB2OFC, [value |-> value[self]])
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED NIB2OFC
                                                /\ UNCHANGED NIB2RC
                                     /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = ""]
                                     /\ pc' = [pc EXCEPT ![self] = "NIBHandleOFCTransactions"]
                                     /\ UNCHANGED FlagNIBOFCEventhandlerFailover
                                ELSE /\ FlagNIBOFCEventhandlerFailover' = TRUE
                                     /\ pc' = [pc EXCEPT ![self] = "NIBForOFCReconciliation"]
                                     /\ UNCHANGED << NIB2OFC, NIB2RC, 
                                                     send_NIB_back >>
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstallOFC, FirstInstallNIB, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, NIBUpdateForRC, 
                                          controllerStateRC, IRStatusRC, 
                                          IRQueueRC, SwSuspensionStatusRC, 
                                          SetScheduledIRsRC, 
                                          FlagRCNIBEventHandlerFailover, 
                                          FlagRCSequencerFailover, RC_READY, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          controllerStateOFC, IRStatusOFC, 
                                          IRQueueOFC, SwSuspensionStatusOFC, 
                                          SetScheduledIRsOFC, 
                                          FlagOFCWorkerFailover, 
                                          FlagOFCMonitorFailover, 
                                          FlagOFCNIBEventHandlerFailover, 
                                          OFCThreadID, OFC_READY, X2NIB, 
                                          OFC2NIB, RC2NIB, FlagNIBFailover, 
                                          FlagNIBRCEventhandlerFailover, 
                                          NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                          masterState, controllerStateNIB, 
                                          IRStatus, SwSuspensionStatus, 
                                          IRQueueNIB, SetScheduledIRs, 
                                          X2NIB_len, NIBThreadID, RCThreadID, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          value_, nextTrans_, value_N, 
                                          rowRemove_, IR2Remove_, 
                                          send_NIB_back_, stepOfFailure_, 
                                          IRIndex_, debug_, nextTrans, value, 
                                          rowRemove_N, IR2Remove, 
                                          stepOfFailure_N, IRIndex, debug, 
                                          NIBMsg_, isBootStrap_, 
                                          toBeScheduledIRs, key, op1_, op2, 
                                          transaction_, nextIR, 
                                          stepOfFailure_c, transaction_O, 
                                          IRQueueTmp, NIBMsg_O, isBootStrap, 
                                          localIRSet, NIBIRSet, nextIRToSent, 
                                          rowIndex, rowRemove, stepOfFailure, 
                                          transaction_c, NIBMsg, op1, IRQueue, 
                                          op_ir_status_change_, removeIR, msg, 
                                          op_ir_status_change, 
                                          op_first_install, transaction >>

NIBForOFCReconciliation(self) == /\ pc[self] = "NIBForOFCReconciliation"
                                 /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
                                    controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed
                                 /\ pc' = [pc EXCEPT ![self] = "NIBHandleOFCTransactions"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstallOFC, 
                                                 FirstInstallNIB, 
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
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 IRQueueRC, 
                                                 SwSuspensionStatusRC, 
                                                 SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 controllerStateOFC, 
                                                 IRStatusOFC, IRQueueOFC, 
                                                 SwSuspensionStatusOFC, 
                                                 SetScheduledIRsOFC, 
                                                 FlagOFCWorkerFailover, 
                                                 FlagOFCMonitorFailover, 
                                                 FlagOFCNIBEventHandlerFailover, 
                                                 OFCThreadID, OFC_READY, 
                                                 NIB2OFC, NIB2RC, X2NIB, 
                                                 OFC2NIB, RC2NIB, 
                                                 FlagNIBFailover, 
                                                 FlagNIBRCEventhandlerFailover, 
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, 
                                                 controllerStateNIB, IRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, value_, 
                                                 nextTrans_, value_N, 
                                                 rowRemove_, IR2Remove_, 
                                                 send_NIB_back_, 
                                                 stepOfFailure_, IRIndex_, 
                                                 debug_, nextTrans, value, 
                                                 rowRemove_N, IR2Remove, 
                                                 send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug, NIBMsg_, isBootStrap_, 
                                                 toBeScheduledIRs, key, op1_, 
                                                 op2, transaction_, nextIR, 
                                                 stepOfFailure_c, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure, 
                                                 transaction_c, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBOFCEventHandler(self) == NIBHandleOFCTransactions(self)
                               \/ NIBDequeueOFCTransaction(self)
                               \/ NIBProcessTransaction(self)
                               \/ NIBSendBackIfAny(self)
                               \/ NIBForOFCReconciliation(self)

RCFailoverResetStates(self) == /\ pc[self] = "RCFailoverResetStates"
                               /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = Failed /\
                                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed
                               /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<rc0,CONT_SEQ>>] = InReconciliation,
                                                                                                     ![<<rc0,CONT_RC_NIB_EVENT>>] = InReconciliation]
                               /\ FlagRCNIBEventHandlerFailover /\ FlagRCSequencerFailover
                               /\ NIB2RC' = <<>>
                               /\ SetScheduledIRsRC' = [y \in SW |-> {}]
                               /\ IRQueueRC' = <<>>
                               /\ RC_READY' = FALSE
                               /\ pc' = [pc EXCEPT ![self] = "RCReadNIB"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstallOFC, 
                                               FirstInstallNIB, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               controllerSubmoduleFailNum, 
                                               switchOrdering, dependencyGraph, 
                                               IR2SW, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               SwSuspensionStatusRC, 
                                               FlagRCNIBEventHandlerFailover, 
                                               FlagRCSequencerFailover, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               controllerStateOFC, IRStatusOFC, 
                                               IRQueueOFC, 
                                               SwSuspensionStatusOFC, 
                                               SetScheduledIRsOFC, 
                                               FlagOFCWorkerFailover, 
                                               FlagOFCMonitorFailover, 
                                               FlagOFCNIBEventHandlerFailover, 
                                               OFCThreadID, OFC_READY, NIB2OFC, 
                                               X2NIB, OFC2NIB, RC2NIB, 
                                               FlagNIBFailover, 
                                               FlagNIBRCEventhandlerFailover, 
                                               FlagNIBOFCEventhandlerFailover, 
                                               NIB_READY_FOR_RC, 
                                               NIB_READY_FOR_OFC, masterState, 
                                               controllerStateNIB, IRStatus, 
                                               SwSuspensionStatus, IRQueueNIB, 
                                               SetScheduledIRs, X2NIB_len, 
                                               NIBThreadID, RCThreadID, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, value, 
                                               rowRemove_N, IR2Remove, 
                                               send_NIB_back, stepOfFailure_N, 
                                               IRIndex, debug, NIBMsg_, 
                                               isBootStrap_, toBeScheduledIRs, 
                                               key, op1_, op2, transaction_, 
                                               nextIR, stepOfFailure_c, 
                                               transaction_O, IRQueueTmp, 
                                               NIBMsg_O, isBootStrap, 
                                               localIRSet, NIBIRSet, 
                                               nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure, 
                                               transaction_c, NIBMsg, op1, 
                                               IRQueue, op_ir_status_change_, 
                                               removeIR, msg, 
                                               op_ir_status_change, 
                                               op_first_install, transaction >>

RCReadNIB(self) == /\ pc[self] = "RCReadNIB"
                   /\ NIB_READY_FOR_RC \/ isNIBUp(NIBThreadID)
                   /\ IRStatusRC' = IRStatus
                   /\ SwSuspensionStatusRC' = SwSuspensionStatus
                   /\ RC_READY' = TRUE
                   /\ pc' = [pc EXCEPT ![self] = "RCBack2Normal"]
                   /\ UNCHANGED << switchLock, controllerLock, FirstInstallOFC, 
                                   FirstInstallNIB, sw_fail_ordering_var, 
                                   ContProcSet, SwProcSet, swSeqChangedStatus, 
                                   controller2Switch, switch2Controller, 
                                   switchStatus, installedIRs, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   dependencyGraph, IR2SW, NIBUpdateForRC, 
                                   controllerStateRC, IRQueueRC, 
                                   SetScheduledIRsRC, 
                                   FlagRCNIBEventHandlerFailover, 
                                   FlagRCSequencerFailover, 
                                   idThreadWorkingOnIR, workerThreadRanking, 
                                   controllerStateOFC, IRStatusOFC, IRQueueOFC, 
                                   SwSuspensionStatusOFC, SetScheduledIRsOFC, 
                                   FlagOFCWorkerFailover, 
                                   FlagOFCMonitorFailover, 
                                   FlagOFCNIBEventHandlerFailover, OFCThreadID, 
                                   OFC_READY, NIB2OFC, NIB2RC, X2NIB, OFC2NIB, 
                                   RC2NIB, FlagNIBFailover, 
                                   FlagNIBRCEventhandlerFailover, 
                                   FlagNIBOFCEventhandlerFailover, 
                                   NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                   masterState, controllerStateNIB, IRStatus, 
                                   SwSuspensionStatus, IRQueueNIB, 
                                   SetScheduledIRs, X2NIB_len, NIBThreadID, 
                                   RCThreadID, ingressPkt, ingressIR, 
                                   egressMsg, ofaInMsg, ofaOutConfirmation, 
                                   installerInIR, statusMsg, notFailedSet, 
                                   failedElem, failedSet, statusResolveMsg, 
                                   recoveredElem, value_, nextTrans_, value_N, 
                                   rowRemove_, IR2Remove_, send_NIB_back_, 
                                   stepOfFailure_, IRIndex_, debug_, nextTrans, 
                                   value, rowRemove_N, IR2Remove, 
                                   send_NIB_back, stepOfFailure_N, IRIndex, 
                                   debug, NIBMsg_, isBootStrap_, 
                                   toBeScheduledIRs, key, op1_, op2, 
                                   transaction_, nextIR, stepOfFailure_c, 
                                   transaction_O, IRQueueTmp, NIBMsg_O, 
                                   isBootStrap, localIRSet, NIBIRSet, 
                                   nextIRToSent, rowIndex, rowRemove, 
                                   stepOfFailure, transaction_c, NIBMsg, op1, 
                                   IRQueue, op_ir_status_change_, removeIR, 
                                   msg, op_ir_status_change, op_first_install, 
                                   transaction >>

RCBack2Normal(self) == /\ pc[self] = "RCBack2Normal"
                       /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<rc0,CONT_SEQ>>] = NotFailed,
                                                                                             ![<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed]
                       /\ NIBUpdateForRC' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstallOFC, FirstInstallNIB, 
                                       sw_fail_ordering_var, ContProcSet, 
                                       SwProcSet, swSeqChangedStatus, 
                                       controller2Switch, switch2Controller, 
                                       switchStatus, installedIRs, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Installer2OfaBuff, Ofa2InstallerBuff, 
                                       TCAM, controlMsgCounter, 
                                       controllerSubmoduleFailNum, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       controllerStateRC, IRStatusRC, 
                                       IRQueueRC, SwSuspensionStatusRC, 
                                       SetScheduledIRsRC, 
                                       FlagRCNIBEventHandlerFailover, 
                                       FlagRCSequencerFailover, RC_READY, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, controllerStateOFC, 
                                       IRStatusOFC, IRQueueOFC, 
                                       SwSuspensionStatusOFC, 
                                       SetScheduledIRsOFC, 
                                       FlagOFCWorkerFailover, 
                                       FlagOFCMonitorFailover, 
                                       FlagOFCNIBEventHandlerFailover, 
                                       OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, 
                                       X2NIB, OFC2NIB, RC2NIB, FlagNIBFailover, 
                                       FlagNIBRCEventhandlerFailover, 
                                       FlagNIBOFCEventhandlerFailover, 
                                       NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                       masterState, controllerStateNIB, 
                                       IRStatus, SwSuspensionStatus, 
                                       IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                       NIBThreadID, RCThreadID, ingressPkt, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       statusMsg, notFailedSet, failedElem, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, value_, nextTrans_, 
                                       value_N, rowRemove_, IR2Remove_, 
                                       send_NIB_back_, stepOfFailure_, 
                                       IRIndex_, debug_, nextTrans, value, 
                                       rowRemove_N, IR2Remove, send_NIB_back, 
                                       stepOfFailure_N, IRIndex, debug, 
                                       NIBMsg_, isBootStrap_, toBeScheduledIRs, 
                                       key, op1_, op2, transaction_, nextIR, 
                                       stepOfFailure_c, transaction_O, 
                                       IRQueueTmp, NIBMsg_O, isBootStrap, 
                                       localIRSet, NIBIRSet, nextIRToSent, 
                                       rowIndex, rowRemove, stepOfFailure, 
                                       transaction_c, NIBMsg, op1, IRQueue, 
                                       op_ir_status_change_, removeIR, msg, 
                                       op_ir_status_change, op_first_install, 
                                       transaction >>

RCFailoverProc(self) == RCFailoverResetStates(self) \/ RCReadNIB(self)
                           \/ RCBack2Normal(self)

RCNIBEventHanderProc(self) == /\ pc[self] = "RCNIBEventHanderProc"
                              /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                              /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF isRCFailed(self)
                                    THEN /\ FlagRCNIBEventHandlerFailover' = TRUE
                                         /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHandlerFailover"]
                                         /\ UNCHANGED << NIBUpdateForRC, 
                                                         IRStatusRC, IRQueueRC, 
                                                         SwSuspensionStatusRC, 
                                                         SetScheduledIRsRC, 
                                                         NIB2RC, NIBMsg_, 
                                                         isBootStrap_ >>
                                    ELSE /\ NIB2RC # <<>>
                                         /\ NIBMsg_' = [NIBMsg_ EXCEPT ![self] = Head(NIB2RC)]
                                         /\ NIB2RC' = Tail(NIB2RC)
                                         /\ IF isBootStrap_[self] = TRUE
                                               THEN /\ IRStatusRC' = [x \in 1..MaxNumIRs |-> IR_NONE]
                                                    /\ IRQueueRC' = <<>>
                                                    /\ SetScheduledIRsRC' = [y \in SW |-> {}]
                                                    /\ SwSuspensionStatusRC' = NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                    /\ NIBUpdateForRC' = TRUE
                                                    /\ isBootStrap_' = [isBootStrap_ EXCEPT ![self] = FALSE]
                                               ELSE /\ IF   IRStatusRC # NIBMsg_'[self].value.IRStatusNIB
                                                          \/ SwSuspensionStatusRC # NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                          THEN /\ IRStatusRC' = NIBMsg_'[self].value.IRStatusNIB
                                                               /\ SwSuspensionStatusRC' = NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                               /\ SetScheduledIRsRC' = [sw \in SW |-> IF SetScheduledIRsRC[sw] = {}
                                                                                          THEN SetScheduledIRsRC[sw]
                                                                                          ELSE {ir \in SetScheduledIRsRC[sw]:
                                                                                                  IRStatusRC'[ir] # IR_DONE}]
                                                               /\ IRQueueRC' = SelectSeq(IRQueueRC, LAMBDA i: IRStatusRC'[i.IR] # IR_DONE)
                                                               /\ NIBUpdateForRC' = TRUE
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED << NIBUpdateForRC, 
                                                                               IRStatusRC, 
                                                                               IRQueueRC, 
                                                                               SwSuspensionStatusRC, 
                                                                               SetScheduledIRsRC >>
                                                    /\ UNCHANGED isBootStrap_
                                         /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHanderProc"]
                                         /\ UNCHANGED FlagRCNIBEventHandlerFailover
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstallOFC, FirstInstallNIB, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, dependencyGraph, 
                                              IR2SW, controllerStateRC, 
                                              FlagRCSequencerFailover, 
                                              RC_READY, idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              controllerStateOFC, IRStatusOFC, 
                                              IRQueueOFC, 
                                              SwSuspensionStatusOFC, 
                                              SetScheduledIRsOFC, 
                                              FlagOFCWorkerFailover, 
                                              FlagOFCMonitorFailover, 
                                              FlagOFCNIBEventHandlerFailover, 
                                              OFCThreadID, OFC_READY, NIB2OFC, 
                                              X2NIB, OFC2NIB, RC2NIB, 
                                              FlagNIBFailover, 
                                              FlagNIBRCEventhandlerFailover, 
                                              FlagNIBOFCEventhandlerFailover, 
                                              NIB_READY_FOR_RC, 
                                              NIB_READY_FOR_OFC, masterState, 
                                              controllerStateNIB, IRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, X2NIB_len, 
                                              NIBThreadID, RCThreadID, 
                                              ingressPkt, ingressIR, egressMsg, 
                                              ofaInMsg, ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, value_, 
                                              nextTrans_, value_N, rowRemove_, 
                                              IR2Remove_, send_NIB_back_, 
                                              stepOfFailure_, IRIndex_, debug_, 
                                              nextTrans, value, rowRemove_N, 
                                              IR2Remove, send_NIB_back, 
                                              stepOfFailure_N, IRIndex, debug, 
                                              toBeScheduledIRs, key, op1_, op2, 
                                              transaction_, nextIR, 
                                              stepOfFailure_c, transaction_O, 
                                              IRQueueTmp, NIBMsg_O, 
                                              isBootStrap, localIRSet, 
                                              NIBIRSet, nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure, 
                                              transaction_c, NIBMsg, op1, 
                                              IRQueue, op_ir_status_change_, 
                                              removeIR, msg, 
                                              op_ir_status_change, 
                                              op_first_install, transaction >>

RCNIBEventHandlerFailover(self) == /\ pc[self] = "RCNIBEventHandlerFailover"
                                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = NotFailed /\
                                            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
                                   /\ isBootStrap_' = [isBootStrap_ EXCEPT ![self] = FALSE]
                                   /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHanderProc"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstallOFC, 
                                                   FirstInstallNIB, 
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
                                                   NIBUpdateForRC, 
                                                   controllerStateRC, 
                                                   IRStatusRC, IRQueueRC, 
                                                   SwSuspensionStatusRC, 
                                                   SetScheduledIRsRC, 
                                                   FlagRCNIBEventHandlerFailover, 
                                                   FlagRCSequencerFailover, 
                                                   RC_READY, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   controllerStateOFC, 
                                                   IRStatusOFC, IRQueueOFC, 
                                                   SwSuspensionStatusOFC, 
                                                   SetScheduledIRsOFC, 
                                                   FlagOFCWorkerFailover, 
                                                   FlagOFCMonitorFailover, 
                                                   FlagOFCNIBEventHandlerFailover, 
                                                   OFCThreadID, OFC_READY, 
                                                   NIB2OFC, NIB2RC, X2NIB, 
                                                   OFC2NIB, RC2NIB, 
                                                   FlagNIBFailover, 
                                                   FlagNIBRCEventhandlerFailover, 
                                                   FlagNIBOFCEventhandlerFailover, 
                                                   NIB_READY_FOR_RC, 
                                                   NIB_READY_FOR_OFC, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   IRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   X2NIB_len, NIBThreadID, 
                                                   RCThreadID, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   failedSet, statusResolveMsg, 
                                                   recoveredElem, value_, 
                                                   nextTrans_, value_N, 
                                                   rowRemove_, IR2Remove_, 
                                                   send_NIB_back_, 
                                                   stepOfFailure_, IRIndex_, 
                                                   debug_, nextTrans, value, 
                                                   rowRemove_N, IR2Remove, 
                                                   send_NIB_back, 
                                                   stepOfFailure_N, IRIndex, 
                                                   debug, NIBMsg_, 
                                                   toBeScheduledIRs, key, op1_, 
                                                   op2, transaction_, nextIR, 
                                                   stepOfFailure_c, 
                                                   transaction_O, IRQueueTmp, 
                                                   NIBMsg_O, isBootStrap, 
                                                   localIRSet, NIBIRSet, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure, 
                                                   transaction_c, NIBMsg, op1, 
                                                   IRQueue, 
                                                   op_ir_status_change_, 
                                                   removeIR, msg, 
                                                   op_ir_status_change, 
                                                   op_first_install, 
                                                   transaction >>

RCNIBEventHandler(self) == RCNIBEventHanderProc(self)
                              \/ RCNIBEventHandlerFailover(self)

RCSendReadTransaction(self) == /\ pc[self] = "RCSendReadTransaction"
                               /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ IF isRCFailed(self)
                                     THEN /\ FlagRCSequencerFailover' = TRUE
                                          /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                                          /\ UNCHANGED << RC2NIB, transaction_ >>
                                     ELSE /\ isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID)
                                          /\ transaction_' = [transaction_ EXCEPT ![self] = [name |-> "SeqReadNIBStates"]]
                                          /\ RC2NIB' = RC2NIB \o <<transaction_'[self]>>
                                          /\ pc' = [pc EXCEPT ![self] = "SequencerProc"]
                                          /\ UNCHANGED FlagRCSequencerFailover
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstallOFC, 
                                               FirstInstallNIB, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, dependencyGraph, 
                                               IR2SW, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               IRQueueRC, SwSuspensionStatusRC, 
                                               SetScheduledIRsRC, 
                                               FlagRCNIBEventHandlerFailover, 
                                               RC_READY, idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               controllerStateOFC, IRStatusOFC, 
                                               IRQueueOFC, 
                                               SwSuspensionStatusOFC, 
                                               SetScheduledIRsOFC, 
                                               FlagOFCWorkerFailover, 
                                               FlagOFCMonitorFailover, 
                                               FlagOFCNIBEventHandlerFailover, 
                                               OFCThreadID, OFC_READY, NIB2OFC, 
                                               NIB2RC, X2NIB, OFC2NIB, 
                                               FlagNIBFailover, 
                                               FlagNIBRCEventhandlerFailover, 
                                               FlagNIBOFCEventhandlerFailover, 
                                               NIB_READY_FOR_RC, 
                                               NIB_READY_FOR_OFC, masterState, 
                                               controllerStateNIB, IRStatus, 
                                               SwSuspensionStatus, IRQueueNIB, 
                                               SetScheduledIRs, X2NIB_len, 
                                               NIBThreadID, RCThreadID, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, value, 
                                               rowRemove_N, IR2Remove, 
                                               send_NIB_back, stepOfFailure_N, 
                                               IRIndex, debug, NIBMsg_, 
                                               isBootStrap_, toBeScheduledIRs, 
                                               key, op1_, op2, nextIR, 
                                               stepOfFailure_c, transaction_O, 
                                               IRQueueTmp, NIBMsg_O, 
                                               isBootStrap, localIRSet, 
                                               NIBIRSet, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure, transaction_c, 
                                               NIBMsg, op1, IRQueue, 
                                               op_ir_status_change_, removeIR, 
                                               msg, op_ir_status_change, 
                                               op_first_install, transaction >>

SequencerProc(self) == /\ pc[self] = "SequencerProc"
                       /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ controllerIsMaster(self[1])
                       /\ IF isRCFailed(self)
                             THEN /\ FlagRCSequencerFailover' = TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "RCComputeNextIR2Schedule"]
                                  /\ UNCHANGED FlagRCSequencerFailover
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstallOFC, FirstInstallNIB, 
                                       sw_fail_ordering_var, ContProcSet, 
                                       SwProcSet, swSeqChangedStatus, 
                                       controller2Switch, switch2Controller, 
                                       switchStatus, installedIRs, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Installer2OfaBuff, Ofa2InstallerBuff, 
                                       TCAM, controlMsgCounter, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, IR2SW, 
                                       NIBUpdateForRC, controllerStateRC, 
                                       IRStatusRC, IRQueueRC, 
                                       SwSuspensionStatusRC, SetScheduledIRsRC, 
                                       FlagRCNIBEventHandlerFailover, RC_READY, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, controllerStateOFC, 
                                       IRStatusOFC, IRQueueOFC, 
                                       SwSuspensionStatusOFC, 
                                       SetScheduledIRsOFC, 
                                       FlagOFCWorkerFailover, 
                                       FlagOFCMonitorFailover, 
                                       FlagOFCNIBEventHandlerFailover, 
                                       OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, 
                                       X2NIB, OFC2NIB, RC2NIB, FlagNIBFailover, 
                                       FlagNIBRCEventhandlerFailover, 
                                       FlagNIBOFCEventhandlerFailover, 
                                       NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                       masterState, controllerStateNIB, 
                                       IRStatus, SwSuspensionStatus, 
                                       IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                       NIBThreadID, RCThreadID, ingressPkt, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       statusMsg, notFailedSet, failedElem, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, value_, nextTrans_, 
                                       value_N, rowRemove_, IR2Remove_, 
                                       send_NIB_back_, stepOfFailure_, 
                                       IRIndex_, debug_, nextTrans, value, 
                                       rowRemove_N, IR2Remove, send_NIB_back, 
                                       stepOfFailure_N, IRIndex, debug, 
                                       NIBMsg_, isBootStrap_, toBeScheduledIRs, 
                                       key, op1_, op2, transaction_, nextIR, 
                                       stepOfFailure_c, transaction_O, 
                                       IRQueueTmp, NIBMsg_O, isBootStrap, 
                                       localIRSet, NIBIRSet, nextIRToSent, 
                                       rowIndex, rowRemove, stepOfFailure, 
                                       transaction_c, NIBMsg, op1, IRQueue, 
                                       op_ir_status_change_, removeIR, msg, 
                                       op_ir_status_change, op_first_install, 
                                       transaction >>

RCComputeNextIR2Schedule(self) == /\ pc[self] = "RCComputeNextIR2Schedule"
                                  /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF isRCFailed(self)
                                        THEN /\ FlagRCSequencerFailover' = TRUE
                                             /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                                             /\ UNCHANGED << NIBUpdateForRC, 
                                                             toBeScheduledIRs >>
                                        ELSE /\ NIBUpdateForRC
                                             /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNextRC(self[1])]
                                             /\ NIBUpdateForRC' = FALSE
                                             /\ IF toBeScheduledIRs'[self] = {}
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "RCComputeNextIR2Schedule"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                             /\ UNCHANGED FlagRCSequencerFailover
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstallOFC, 
                                                  FirstInstallNIB, 
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
                                                  controllerStateRC, 
                                                  IRStatusRC, IRQueueRC, 
                                                  SwSuspensionStatusRC, 
                                                  SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  RC_READY, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  controllerStateOFC, 
                                                  IRStatusOFC, IRQueueOFC, 
                                                  SwSuspensionStatusOFC, 
                                                  SetScheduledIRsOFC, 
                                                  FlagOFCWorkerFailover, 
                                                  FlagOFCMonitorFailover, 
                                                  FlagOFCNIBEventHandlerFailover, 
                                                  OFCThreadID, OFC_READY, 
                                                  NIB2OFC, NIB2RC, X2NIB, 
                                                  OFC2NIB, RC2NIB, 
                                                  FlagNIBFailover, 
                                                  FlagNIBRCEventhandlerFailover, 
                                                  FlagNIBOFCEventhandlerFailover, 
                                                  NIB_READY_FOR_RC, 
                                                  NIB_READY_FOR_OFC, 
                                                  masterState, 
                                                  controllerStateNIB, IRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, value_, 
                                                  nextTrans_, value_N, 
                                                  rowRemove_, IR2Remove_, 
                                                  send_NIB_back_, 
                                                  stepOfFailure_, IRIndex_, 
                                                  debug_, nextTrans, value, 
                                                  rowRemove_N, IR2Remove, 
                                                  send_NIB_back, 
                                                  stepOfFailure_N, IRIndex, 
                                                  debug, NIBMsg_, isBootStrap_, 
                                                  key, op1_, op2, transaction_, 
                                                  nextIR, stepOfFailure_c, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure, 
                                                  transaction_c, NIBMsg, op1, 
                                                  IRQueue, 
                                                  op_ir_status_change_, 
                                                  removeIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF isRCFailed(self)
                                  THEN /\ FlagRCSequencerFailover' = TRUE
                                       /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                                       /\ UNCHANGED << IRQueueRC, 
                                                       SetScheduledIRsRC, 
                                                       toBeScheduledIRs, 
                                                       nextIR >>
                                  ELSE /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                                       /\ SetScheduledIRsRC' = [SetScheduledIRsRC EXCEPT ![IR2SW[nextIR'[self]]] = SetScheduledIRsRC[IR2SW[nextIR'[self]]] \cup {nextIR'[self]}]
                                       /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR'[self]}]
                                       /\ IRQueueRC' = Append(IRQueueRC, [IR |-> nextIR'[self], tag |-> NO_TAG])
                                       /\ pc' = [pc EXCEPT ![self] = "RCSendPrepareIR2NIB"]
                                       /\ UNCHANGED FlagRCSequencerFailover
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            RC_READY, idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            controllerStateOFC, IRStatusOFC, 
                                            IRQueueOFC, SwSuspensionStatusOFC, 
                                            SetScheduledIRsOFC, 
                                            FlagOFCWorkerFailover, 
                                            FlagOFCMonitorFailover, 
                                            FlagOFCNIBEventHandlerFailover, 
                                            OFCThreadID, OFC_READY, NIB2OFC, 
                                            NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                            FlagNIBFailover, 
                                            FlagNIBRCEventhandlerFailover, 
                                            FlagNIBOFCEventhandlerFailover, 
                                            NIB_READY_FOR_RC, 
                                            NIB_READY_FOR_OFC, masterState, 
                                            controllerStateNIB, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug, NIBMsg_, 
                                            isBootStrap_, key, op1_, op2, 
                                            transaction_, stepOfFailure_c, 
                                            transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, nextIRToSent, rowIndex, 
                                            rowRemove, stepOfFailure, 
                                            transaction_c, NIBMsg, op1, 
                                            IRQueue, op_ir_status_change_, 
                                            removeIR, msg, op_ir_status_change, 
                                            op_first_install, transaction >>

RCSendPrepareIR2NIB(self) == /\ pc[self] = "RCSendPrepareIR2NIB"
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ IF isRCFailed(self)
                                   THEN /\ FlagRCSequencerFailover' = TRUE
                                        /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                                        /\ UNCHANGED << RC2NIB, op1_, 
                                                        transaction_ >>
                                   ELSE /\ isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID)
                                        /\ op1_' = [op1_ EXCEPT ![self] = [table |-> NIBT_IR_QUEUE, key |-> NULL, value |-> [IR |-> nextIR[self], tag |-> NO_TAG]]]
                                        /\ transaction_' = [transaction_ EXCEPT ![self] = [name |-> "RCScheduleIRInOneStep", ops |-> <<op1_'[self]>>]]
                                        /\ RC2NIB' = RC2NIB \o <<transaction_'[self]>>
                                        /\ IF toBeScheduledIRs[self] = {}
                                              THEN /\ pc' = [pc EXCEPT ![self] = "SequencerProc"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                        /\ UNCHANGED FlagRCSequencerFailover
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstallOFC, FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             IRQueueRC, SwSuspensionStatusRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             RC_READY, idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             controllerStateOFC, IRStatusOFC, 
                                             IRQueueOFC, SwSuspensionStatusOFC, 
                                             SetScheduledIRsOFC, 
                                             FlagOFCWorkerFailover, 
                                             FlagOFCMonitorFailover, 
                                             FlagOFCNIBEventHandlerFailover, 
                                             OFCThreadID, OFC_READY, NIB2OFC, 
                                             NIB2RC, X2NIB, OFC2NIB, 
                                             FlagNIBFailover, 
                                             FlagNIBRCEventhandlerFailover, 
                                             FlagNIBOFCEventhandlerFailover, 
                                             NIB_READY_FOR_RC, 
                                             NIB_READY_FOR_OFC, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, value_, nextTrans_, 
                                             value_N, rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug, NIBMsg_, 
                                             isBootStrap_, toBeScheduledIRs, 
                                             key, op2, nextIR, stepOfFailure_c, 
                                             transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure, 
                                             transaction_c, NIBMsg, op1, 
                                             IRQueue, op_ir_status_change_, 
                                             removeIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

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
                                          /\ pc' = [pc EXCEPT ![self] = "SequencerProc"]
                                          /\ UNCHANGED << switchLock, 
                                                          FirstInstallOFC, 
                                                          FirstInstallNIB, 
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
                                                          NIBUpdateForRC, 
                                                          controllerStateRC, 
                                                          IRStatusRC, 
                                                          IRQueueRC, 
                                                          SwSuspensionStatusRC, 
                                                          SetScheduledIRsRC, 
                                                          FlagRCNIBEventHandlerFailover, 
                                                          FlagRCSequencerFailover, 
                                                          RC_READY, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          controllerStateOFC, 
                                                          IRStatusOFC, 
                                                          IRQueueOFC, 
                                                          SwSuspensionStatusOFC, 
                                                          SetScheduledIRsOFC, 
                                                          FlagOFCWorkerFailover, 
                                                          FlagOFCMonitorFailover, 
                                                          FlagOFCNIBEventHandlerFailover, 
                                                          OFCThreadID, 
                                                          OFC_READY, NIB2OFC, 
                                                          NIB2RC, X2NIB, 
                                                          OFC2NIB, RC2NIB, 
                                                          FlagNIBFailover, 
                                                          FlagNIBRCEventhandlerFailover, 
                                                          FlagNIBOFCEventhandlerFailover, 
                                                          NIB_READY_FOR_RC, 
                                                          NIB_READY_FOR_OFC, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          IRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          X2NIB_len, 
                                                          NIBThreadID, 
                                                          RCThreadID, 
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
                                                          value_, nextTrans_, 
                                                          value_N, rowRemove_, 
                                                          IR2Remove_, 
                                                          send_NIB_back_, 
                                                          stepOfFailure_, 
                                                          IRIndex_, debug_, 
                                                          nextTrans, value, 
                                                          rowRemove_N, 
                                                          IR2Remove, 
                                                          send_NIB_back, 
                                                          stepOfFailure_N, 
                                                          IRIndex, debug, 
                                                          NIBMsg_, 
                                                          isBootStrap_, 
                                                          toBeScheduledIRs, 
                                                          key, op1_, op2, 
                                                          transaction_, nextIR, 
                                                          stepOfFailure_c, 
                                                          transaction_O, 
                                                          IRQueueTmp, NIBMsg_O, 
                                                          isBootStrap, 
                                                          localIRSet, NIBIRSet, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure, 
                                                          transaction_c, 
                                                          NIBMsg, op1, IRQueue, 
                                                          op_ir_status_change_, 
                                                          removeIR, msg, 
                                                          op_ir_status_change, 
                                                          op_first_install, 
                                                          transaction >>

RCSequencerFailover(self) == /\ pc[self] = "RCSequencerFailover"
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = {}]
                             /\ controllerSubmoduleFailStat[<<rc0,CONT_SEQ>>] = NotFailed /\
                                      controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
                             /\ pc' = [pc EXCEPT ![self] = "SequencerProc"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstallOFC, FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             IR2SW, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             IRQueueRC, SwSuspensionStatusRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             controllerStateOFC, IRStatusOFC, 
                                             IRQueueOFC, SwSuspensionStatusOFC, 
                                             SetScheduledIRsOFC, 
                                             FlagOFCWorkerFailover, 
                                             FlagOFCMonitorFailover, 
                                             FlagOFCNIBEventHandlerFailover, 
                                             OFCThreadID, OFC_READY, NIB2OFC, 
                                             NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                             FlagNIBFailover, 
                                             FlagNIBRCEventhandlerFailover, 
                                             FlagNIBOFCEventhandlerFailover, 
                                             NIB_READY_FOR_RC, 
                                             NIB_READY_FOR_OFC, masterState, 
                                             controllerStateNIB, IRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, value_, nextTrans_, 
                                             value_N, rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug, NIBMsg_, 
                                             isBootStrap_, key, op1_, op2, 
                                             transaction_, nextIR, 
                                             stepOfFailure_c, transaction_O, 
                                             IRQueueTmp, NIBMsg_O, isBootStrap, 
                                             localIRSet, NIBIRSet, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure, transaction_c, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             msg, op_ir_status_change, 
                                             op_first_install, transaction >>

controllerSequencer(self) == RCSendReadTransaction(self)
                                \/ SequencerProc(self)
                                \/ RCComputeNextIR2Schedule(self)
                                \/ SchedulerMechanism(self)
                                \/ RCSendPrepareIR2NIB(self)
                                \/ ControllerSeqStateReconciliation(self)
                                \/ RCSequencerFailover(self)

OFCFailure(self) == /\ pc[self] = "OFCFailure"
                    /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                    /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![OFCThreadID] = Failed,
                                                                                          ![<<ofc0,CONT_MONITOR>>] = Failed,
                                                                                          ![<<ofc0,CONT_OFC_NIB_EVENT>>] = Failed]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << switchLock, controllerLock, 
                                    FirstInstallOFC, FirstInstallNIB, 
                                    sw_fail_ordering_var, ContProcSet, 
                                    SwProcSet, swSeqChangedStatus, 
                                    controller2Switch, switch2Controller, 
                                    switchStatus, installedIRs, 
                                    NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                    Installer2OfaBuff, Ofa2InstallerBuff, TCAM, 
                                    controlMsgCounter, 
                                    controllerSubmoduleFailNum, switchOrdering, 
                                    dependencyGraph, IR2SW, NIBUpdateForRC, 
                                    controllerStateRC, IRStatusRC, IRQueueRC, 
                                    SwSuspensionStatusRC, SetScheduledIRsRC, 
                                    FlagRCNIBEventHandlerFailover, 
                                    FlagRCSequencerFailover, RC_READY, 
                                    idThreadWorkingOnIR, workerThreadRanking, 
                                    controllerStateOFC, IRStatusOFC, 
                                    IRQueueOFC, SwSuspensionStatusOFC, 
                                    SetScheduledIRsOFC, FlagOFCWorkerFailover, 
                                    FlagOFCMonitorFailover, 
                                    FlagOFCNIBEventHandlerFailover, 
                                    OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, 
                                    X2NIB, OFC2NIB, RC2NIB, FlagNIBFailover, 
                                    FlagNIBRCEventhandlerFailover, 
                                    FlagNIBOFCEventhandlerFailover, 
                                    NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                    masterState, controllerStateNIB, IRStatus, 
                                    SwSuspensionStatus, IRQueueNIB, 
                                    SetScheduledIRs, X2NIB_len, NIBThreadID, 
                                    RCThreadID, ingressPkt, ingressIR, 
                                    egressMsg, ofaInMsg, ofaOutConfirmation, 
                                    installerInIR, statusMsg, notFailedSet, 
                                    failedElem, failedSet, statusResolveMsg, 
                                    recoveredElem, value_, nextTrans_, value_N, 
                                    rowRemove_, IR2Remove_, send_NIB_back_, 
                                    stepOfFailure_, IRIndex_, debug_, 
                                    nextTrans, value, rowRemove_N, IR2Remove, 
                                    send_NIB_back, stepOfFailure_N, IRIndex, 
                                    debug, NIBMsg_, isBootStrap_, 
                                    toBeScheduledIRs, key, op1_, op2, 
                                    transaction_, nextIR, stepOfFailure_c, 
                                    transaction_O, IRQueueTmp, NIBMsg_O, 
                                    isBootStrap, localIRSet, NIBIRSet, 
                                    nextIRToSent, rowIndex, rowRemove, 
                                    stepOfFailure, transaction_c, NIBMsg, op1, 
                                    IRQueue, op_ir_status_change_, removeIR, 
                                    msg, op_ir_status_change, op_first_install, 
                                    transaction >>

OFCFailureProc(self) == OFCFailure(self)

OFCFailoverResetStates(self) == /\ pc[self] = "OFCFailoverResetStates"
                                /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerSubmoduleFailStat[OFCThreadID] = Failed
                                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] = Failed
                                     /\ controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] = Failed
                                /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![OFCThreadID] = InReconciliation,
                                                                                                      ![<<ofc0,CONT_MONITOR>>] = InReconciliation,
                                                                                                      ![<<ofc0,CONT_OFC_NIB_EVENT>>] = InReconciliation]
                                /\ FlagOFCNIBEventHandlerFailover /\ FlagOFCMonitorFailover /\ FlagOFCWorkerFailover
                                /\ NIB2OFC' = <<>>
                                /\ OFC2NIB' = <<>>
                                /\ IRQueueOFC' = <<>>
                                /\ IRStatusOFC' = [x \in 1..MaxNumIRs |-> IR_NONE]
                                /\ switch2Controller' = <<>>
                                /\ controller2Switch' = [x\in SW |-> <<>>]
                                /\ OFC_READY' = FALSE
                                /\ pc' = [pc EXCEPT ![self] = "OFCReadSwitches"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstallOFC, 
                                                FirstInstallNIB, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                swSeqChangedStatus, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                controllerSubmoduleFailNum, 
                                                switchOrdering, 
                                                dependencyGraph, IR2SW, 
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                IRQueueRC, 
                                                SwSuspensionStatusRC, 
                                                SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                controllerStateOFC, 
                                                SwSuspensionStatusOFC, 
                                                SetScheduledIRsOFC, 
                                                FlagOFCWorkerFailover, 
                                                FlagOFCMonitorFailover, 
                                                FlagOFCNIBEventHandlerFailover, 
                                                OFCThreadID, NIB2RC, X2NIB, 
                                                RC2NIB, FlagNIBFailover, 
                                                FlagNIBRCEventhandlerFailover, 
                                                FlagNIBOFCEventhandlerFailover, 
                                                NIB_READY_FOR_RC, 
                                                NIB_READY_FOR_OFC, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, X2NIB_len, 
                                                NIBThreadID, RCThreadID, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug, NIBMsg_, 
                                                isBootStrap_, toBeScheduledIRs, 
                                                key, op1_, op2, transaction_, 
                                                nextIR, stepOfFailure_c, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure, 
                                                transaction_c, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, msg, 
                                                op_ir_status_change, 
                                                op_first_install, transaction >>

OFCReadSwitches(self) == /\ pc[self] = "OFCReadSwitches"
                         /\ IRStatusOFC' = [x \in 1..MaxNumIRs |-> IF x \in rangeSeq(installedIRs)
                                                                   THEN IR_DONE
                                                                   ELSE IRStatusOFC[x]]
                         /\ FirstInstallOFC' = [x \in 1..MaxNumIRs |-> IF IRStatusOFC'[x] = IR_DONE
                                                                       THEN FirstInstallOFC[x] + 1
                                                                       ELSE FirstInstallOFC[x]]
                         /\ OFC_READY' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "OFCReadNIB"]
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         IRQueueRC, SwSuspensionStatusRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         controllerStateOFC, IRQueueOFC, 
                                         SwSuspensionStatusOFC, 
                                         SetScheduledIRsOFC, 
                                         FlagOFCWorkerFailover, 
                                         FlagOFCMonitorFailover, 
                                         FlagOFCNIBEventHandlerFailover, 
                                         OFCThreadID, NIB2OFC, NIB2RC, X2NIB, 
                                         OFC2NIB, RC2NIB, FlagNIBFailover, 
                                         FlagNIBRCEventhandlerFailover, 
                                         FlagNIBOFCEventhandlerFailover, 
                                         NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         value_, nextTrans_, value_N, 
                                         rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug, 
                                         NIBMsg_, isBootStrap_, 
                                         toBeScheduledIRs, key, op1_, op2, 
                                         transaction_, nextIR, stepOfFailure_c, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure, transaction_c, NIBMsg, 
                                         op1, IRQueue, op_ir_status_change_, 
                                         removeIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

OFCReadNIB(self) == /\ pc[self] = "OFCReadNIB"
                    /\ NIB_READY_FOR_OFC \/ isNIBUp(NIBThreadID)
                    /\ IRQueueOFC' = SelectSeq(IRQueueRC, LAMBDA i: IRStatusOFC[i.IR] # IR_DONE)
                    /\ pc' = [pc EXCEPT ![self] = "OFCBack2Normal"]
                    /\ UNCHANGED << switchLock, controllerLock, 
                                    FirstInstallOFC, FirstInstallNIB, 
                                    sw_fail_ordering_var, ContProcSet, 
                                    SwProcSet, swSeqChangedStatus, 
                                    controller2Switch, switch2Controller, 
                                    switchStatus, installedIRs, 
                                    NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                    Installer2OfaBuff, Ofa2InstallerBuff, TCAM, 
                                    controlMsgCounter, 
                                    controllerSubmoduleFailNum, 
                                    controllerSubmoduleFailStat, 
                                    switchOrdering, dependencyGraph, IR2SW, 
                                    NIBUpdateForRC, controllerStateRC, 
                                    IRStatusRC, IRQueueRC, 
                                    SwSuspensionStatusRC, SetScheduledIRsRC, 
                                    FlagRCNIBEventHandlerFailover, 
                                    FlagRCSequencerFailover, RC_READY, 
                                    idThreadWorkingOnIR, workerThreadRanking, 
                                    controllerStateOFC, IRStatusOFC, 
                                    SwSuspensionStatusOFC, SetScheduledIRsOFC, 
                                    FlagOFCWorkerFailover, 
                                    FlagOFCMonitorFailover, 
                                    FlagOFCNIBEventHandlerFailover, 
                                    OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, 
                                    X2NIB, OFC2NIB, RC2NIB, FlagNIBFailover, 
                                    FlagNIBRCEventhandlerFailover, 
                                    FlagNIBOFCEventhandlerFailover, 
                                    NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                    masterState, controllerStateNIB, IRStatus, 
                                    SwSuspensionStatus, IRQueueNIB, 
                                    SetScheduledIRs, X2NIB_len, NIBThreadID, 
                                    RCThreadID, ingressPkt, ingressIR, 
                                    egressMsg, ofaInMsg, ofaOutConfirmation, 
                                    installerInIR, statusMsg, notFailedSet, 
                                    failedElem, failedSet, statusResolveMsg, 
                                    recoveredElem, value_, nextTrans_, value_N, 
                                    rowRemove_, IR2Remove_, send_NIB_back_, 
                                    stepOfFailure_, IRIndex_, debug_, 
                                    nextTrans, value, rowRemove_N, IR2Remove, 
                                    send_NIB_back, stepOfFailure_N, IRIndex, 
                                    debug, NIBMsg_, isBootStrap_, 
                                    toBeScheduledIRs, key, op1_, op2, 
                                    transaction_, nextIR, stepOfFailure_c, 
                                    transaction_O, IRQueueTmp, NIBMsg_O, 
                                    isBootStrap, localIRSet, NIBIRSet, 
                                    nextIRToSent, rowIndex, rowRemove, 
                                    stepOfFailure, transaction_c, NIBMsg, op1, 
                                    IRQueue, op_ir_status_change_, removeIR, 
                                    msg, op_ir_status_change, op_first_install, 
                                    transaction >>

OFCBack2Normal(self) == /\ pc[self] = "OFCBack2Normal"
                        /\ isNIBUp(NIBThreadID) \/ isNIBReconciliation(NIBThreadID)
                        /\ transaction_O' = [transaction_O EXCEPT ![self] = [name |-> "OFCOverrideIRStatus",
                                                                                     ops |-> <<IRStatusOFC, FirstInstallOFC>>]]
                        /\ OFC2NIB' = OFC2NIB \o <<transaction_O'[self]>>
                        /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![OFCThreadID] = NotFailed,
                                                                                              ![<<ofc0,CONT_MONITOR>>] = NotFailed,
                                                                                              ![<<ofc0,CONT_OFC_NIB_EVENT>>] = NotFailed]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << switchLock, controllerLock, 
                                        FirstInstallOFC, FirstInstallNIB, 
                                        sw_fail_ordering_var, ContProcSet, 
                                        SwProcSet, swSeqChangedStatus, 
                                        controller2Switch, switch2Controller, 
                                        switchStatus, installedIRs, 
                                        NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                        Installer2OfaBuff, Ofa2InstallerBuff, 
                                        TCAM, controlMsgCounter, 
                                        controllerSubmoduleFailNum, 
                                        switchOrdering, dependencyGraph, IR2SW, 
                                        NIBUpdateForRC, controllerStateRC, 
                                        IRStatusRC, IRQueueRC, 
                                        SwSuspensionStatusRC, 
                                        SetScheduledIRsRC, 
                                        FlagRCNIBEventHandlerFailover, 
                                        FlagRCSequencerFailover, RC_READY, 
                                        idThreadWorkingOnIR, 
                                        workerThreadRanking, 
                                        controllerStateOFC, IRStatusOFC, 
                                        IRQueueOFC, SwSuspensionStatusOFC, 
                                        SetScheduledIRsOFC, 
                                        FlagOFCWorkerFailover, 
                                        FlagOFCMonitorFailover, 
                                        FlagOFCNIBEventHandlerFailover, 
                                        OFCThreadID, OFC_READY, NIB2OFC, 
                                        NIB2RC, X2NIB, RC2NIB, FlagNIBFailover, 
                                        FlagNIBRCEventhandlerFailover, 
                                        FlagNIBOFCEventhandlerFailover, 
                                        NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                        masterState, controllerStateNIB, 
                                        IRStatus, SwSuspensionStatus, 
                                        IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                        NIBThreadID, RCThreadID, ingressPkt, 
                                        ingressIR, egressMsg, ofaInMsg, 
                                        ofaOutConfirmation, installerInIR, 
                                        statusMsg, notFailedSet, failedElem, 
                                        failedSet, statusResolveMsg, 
                                        recoveredElem, value_, nextTrans_, 
                                        value_N, rowRemove_, IR2Remove_, 
                                        send_NIB_back_, stepOfFailure_, 
                                        IRIndex_, debug_, nextTrans, value, 
                                        rowRemove_N, IR2Remove, send_NIB_back, 
                                        stepOfFailure_N, IRIndex, debug, 
                                        NIBMsg_, isBootStrap_, 
                                        toBeScheduledIRs, key, op1_, op2, 
                                        transaction_, nextIR, stepOfFailure_c, 
                                        IRQueueTmp, NIBMsg_O, isBootStrap, 
                                        localIRSet, NIBIRSet, nextIRToSent, 
                                        rowIndex, rowRemove, stepOfFailure, 
                                        transaction_c, NIBMsg, op1, IRQueue, 
                                        op_ir_status_change_, removeIR, msg, 
                                        op_ir_status_change, op_first_install, 
                                        transaction >>

OFCFailoverProc(self) == OFCFailoverResetStates(self)
                            \/ OFCReadSwitches(self) \/ OFCReadNIB(self)
                            \/ OFCBack2Normal(self)

OFCNIBEventHanderProc(self) == /\ pc[self] = "OFCNIBEventHanderProc"
                               /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ IF isOFCFailed(self)
                                     THEN /\ FlagOFCNIBEventHandlerFailover' = TRUE
                                          /\ pc' = [pc EXCEPT ![self] = "OFCNIBEventHandlerFailover"]
                                          /\ UNCHANGED << IRQueueOFC, NIB2OFC, 
                                                          NIBMsg_O, localIRSet, 
                                                          NIBIRSet >>
                                     ELSE /\ NIB2OFC # <<>>
                                          /\ NIBMsg_O' = [NIBMsg_O EXCEPT ![self] = Head(NIB2OFC)]
                                          /\ NIB2OFC' = Tail(NIB2OFC)
                                          /\ localIRSet' = [localIRSet EXCEPT ![self] = {IRQueueOFC[i].IR: i \in DOMAIN IRQueueOFC}]
                                          /\ NIBIRSet' = [NIBIRSet EXCEPT ![self] = {NIBMsg_O'[self].value.IRQueueNIB[i].IR: i \in DOMAIN NIBMsg_O'[self].value.IRQueueNIB}]
                                          /\ IF localIRSet'[self] # NIBIRSet'[self]
                                                THEN /\ IRQueueOFC' = SelectSeq(NIBMsg_O'[self].value.IRQueueNIB, LAMBDA i: IRStatusOFC[i.IR] = IR_NONE)
                                                     /\ Assert(Len(IRQueueOFC') <= MaxNumIRs, 
                                                               "Failure of assertion at line 2018, column 21.")
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED IRQueueOFC
                                          /\ pc' = [pc EXCEPT ![self] = "OFCNIBEventHanderProc"]
                                          /\ UNCHANGED FlagOFCNIBEventHandlerFailover
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstallOFC, 
                                               FirstInstallNIB, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, dependencyGraph, 
                                               IR2SW, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               IRQueueRC, SwSuspensionStatusRC, 
                                               SetScheduledIRsRC, 
                                               FlagRCNIBEventHandlerFailover, 
                                               FlagRCSequencerFailover, 
                                               RC_READY, idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               controllerStateOFC, IRStatusOFC, 
                                               SwSuspensionStatusOFC, 
                                               SetScheduledIRsOFC, 
                                               FlagOFCWorkerFailover, 
                                               FlagOFCMonitorFailover, 
                                               OFCThreadID, OFC_READY, NIB2RC, 
                                               X2NIB, OFC2NIB, RC2NIB, 
                                               FlagNIBFailover, 
                                               FlagNIBRCEventhandlerFailover, 
                                               FlagNIBOFCEventhandlerFailover, 
                                               NIB_READY_FOR_RC, 
                                               NIB_READY_FOR_OFC, masterState, 
                                               controllerStateNIB, IRStatus, 
                                               SwSuspensionStatus, IRQueueNIB, 
                                               SetScheduledIRs, X2NIB_len, 
                                               NIBThreadID, RCThreadID, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, value, 
                                               rowRemove_N, IR2Remove, 
                                               send_NIB_back, stepOfFailure_N, 
                                               IRIndex, debug, NIBMsg_, 
                                               isBootStrap_, toBeScheduledIRs, 
                                               key, op1_, op2, transaction_, 
                                               nextIR, stepOfFailure_c, 
                                               transaction_O, IRQueueTmp, 
                                               isBootStrap, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure, transaction_c, 
                                               NIBMsg, op1, IRQueue, 
                                               op_ir_status_change_, removeIR, 
                                               msg, op_ir_status_change, 
                                               op_first_install, transaction >>

OFCNIBEventHandlerFailover(self) == /\ pc[self] = "OFCNIBEventHandlerFailover"
                                    /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ isOFCUp(OFCThreadID)
                                    /\ pc' = [pc EXCEPT ![self] = "OFCNIBEventHanderProc"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstallOFC, 
                                                    FirstInstallNIB, 
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
                                                    NIBUpdateForRC, 
                                                    controllerStateRC, 
                                                    IRStatusRC, IRQueueRC, 
                                                    SwSuspensionStatusRC, 
                                                    SetScheduledIRsRC, 
                                                    FlagRCNIBEventHandlerFailover, 
                                                    FlagRCSequencerFailover, 
                                                    RC_READY, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    controllerStateOFC, 
                                                    IRStatusOFC, IRQueueOFC, 
                                                    SwSuspensionStatusOFC, 
                                                    SetScheduledIRsOFC, 
                                                    FlagOFCWorkerFailover, 
                                                    FlagOFCMonitorFailover, 
                                                    FlagOFCNIBEventHandlerFailover, 
                                                    OFCThreadID, OFC_READY, 
                                                    NIB2OFC, NIB2RC, X2NIB, 
                                                    OFC2NIB, RC2NIB, 
                                                    FlagNIBFailover, 
                                                    FlagNIBRCEventhandlerFailover, 
                                                    FlagNIBOFCEventhandlerFailover, 
                                                    NIB_READY_FOR_RC, 
                                                    NIB_READY_FOR_OFC, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    IRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, X2NIB_len, 
                                                    NIBThreadID, RCThreadID, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, value_, 
                                                    nextTrans_, value_N, 
                                                    rowRemove_, IR2Remove_, 
                                                    send_NIB_back_, 
                                                    stepOfFailure_, IRIndex_, 
                                                    debug_, nextTrans, value, 
                                                    rowRemove_N, IR2Remove, 
                                                    send_NIB_back, 
                                                    stepOfFailure_N, IRIndex, 
                                                    debug, NIBMsg_, 
                                                    isBootStrap_, 
                                                    toBeScheduledIRs, key, 
                                                    op1_, op2, transaction_, 
                                                    nextIR, stepOfFailure_c, 
                                                    transaction_O, IRQueueTmp, 
                                                    NIBMsg_O, isBootStrap, 
                                                    localIRSet, NIBIRSet, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure, 
                                                    transaction_c, NIBMsg, op1, 
                                                    IRQueue, 
                                                    op_ir_status_change_, 
                                                    removeIR, msg, 
                                                    op_ir_status_change, 
                                                    op_first_install, 
                                                    transaction >>

OFCNIBEventHandler(self) == OFCNIBEventHanderProc(self)
                               \/ OFCNIBEventHandlerFailover(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerIsMaster(self[1])
                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ pc' = [pc EXCEPT ![self] = "OFCThreadGetNextIR"]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstallOFC, FirstInstallNIB, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          IR2SW, NIBUpdateForRC, 
                                          controllerStateRC, IRStatusRC, 
                                          IRQueueRC, SwSuspensionStatusRC, 
                                          SetScheduledIRsRC, 
                                          FlagRCNIBEventHandlerFailover, 
                                          FlagRCSequencerFailover, RC_READY, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          controllerStateOFC, IRStatusOFC, 
                                          IRQueueOFC, SwSuspensionStatusOFC, 
                                          SetScheduledIRsOFC, 
                                          FlagOFCWorkerFailover, 
                                          FlagOFCMonitorFailover, 
                                          FlagOFCNIBEventHandlerFailover, 
                                          OFCThreadID, OFC_READY, NIB2OFC, 
                                          NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                          FlagNIBFailover, 
                                          FlagNIBRCEventhandlerFailover, 
                                          FlagNIBOFCEventhandlerFailover, 
                                          NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                          masterState, controllerStateNIB, 
                                          IRStatus, SwSuspensionStatus, 
                                          IRQueueNIB, SetScheduledIRs, 
                                          X2NIB_len, NIBThreadID, RCThreadID, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, failedSet, 
                                          statusResolveMsg, recoveredElem, 
                                          value_, nextTrans_, value_N, 
                                          rowRemove_, IR2Remove_, 
                                          send_NIB_back_, stepOfFailure_, 
                                          IRIndex_, debug_, nextTrans, value, 
                                          rowRemove_N, IR2Remove, 
                                          send_NIB_back, stepOfFailure_N, 
                                          IRIndex, debug, NIBMsg_, 
                                          isBootStrap_, toBeScheduledIRs, key, 
                                          op1_, op2, transaction_, nextIR, 
                                          stepOfFailure_c, transaction_O, 
                                          IRQueueTmp, NIBMsg_O, isBootStrap, 
                                          localIRSet, NIBIRSet, nextIRToSent, 
                                          rowIndex, rowRemove, stepOfFailure, 
                                          transaction_c, NIBMsg, op1, IRQueue, 
                                          op_ir_status_change_, removeIR, msg, 
                                          op_ir_status_change, 
                                          op_first_install, transaction >>

OFCThreadGetNextIR(self) == /\ pc[self] = "OFCThreadGetNextIR"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF isOFCFailed(self)
                                  THEN /\ FlagOFCWorkerFailover' = TRUE
                                       /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                       /\ UNCHANGED << IRQueueOFC, 
                                                       nextIRToSent, rowIndex >>
                                  ELSE /\ Len(IRQueueOFC) > 0
                                       /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead(self, IRQueueOFC)]
                                       /\ nextIRToSent' = [nextIRToSent EXCEPT ![self] = IRQueueOFC[rowIndex'[self]].IR]
                                       /\ IRQueueOFC' = [IRQueueOFC EXCEPT ![rowIndex'[self]].tag = self]
                                       /\ IF IRStatusOFC[nextIRToSent'[self]] = IR_DONE
                                             THEN /\ pc' = [pc EXCEPT ![self] = "OFCRemoveIRFromIRQueueOFCLocal"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "OFCThreadSendIR"]
                                       /\ UNCHANGED FlagOFCWorkerFailover
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            IRQueueRC, SwSuspensionStatusRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            controllerStateOFC, IRStatusOFC, 
                                            SwSuspensionStatusOFC, 
                                            SetScheduledIRsOFC, 
                                            FlagOFCMonitorFailover, 
                                            FlagOFCNIBEventHandlerFailover, 
                                            OFCThreadID, OFC_READY, NIB2OFC, 
                                            NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                            FlagNIBFailover, 
                                            FlagNIBRCEventhandlerFailover, 
                                            FlagNIBOFCEventhandlerFailover, 
                                            NIB_READY_FOR_RC, 
                                            NIB_READY_FOR_OFC, masterState, 
                                            controllerStateNIB, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug, NIBMsg_, 
                                            isBootStrap_, toBeScheduledIRs, 
                                            key, op1_, op2, transaction_, 
                                            nextIR, stepOfFailure_c, 
                                            transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, rowRemove, stepOfFailure, 
                                            transaction_c, NIBMsg, op1, 
                                            IRQueue, op_ir_status_change_, 
                                            removeIR, msg, op_ir_status_change, 
                                            op_first_install, transaction >>

OFCThreadSendIR(self) == /\ pc[self] = "OFCThreadSendIR"
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                         /\ IF isOFCFailed(self)
                               THEN /\ FlagOFCWorkerFailover' = TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                    /\ UNCHANGED IRStatusOFC
                               ELSE /\ IF IRStatusOFC[nextIRToSent[self]] = IR_DONE
                                          THEN /\ pc' = [pc EXCEPT ![self] = "OFCRemoveIRFromIRQueueOFCLocal"]
                                               /\ UNCHANGED IRStatusOFC
                                          ELSE /\ IRStatusOFC' = [IRStatusOFC EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                               /\ pc' = [pc EXCEPT ![self] = "OFCThreadNotifyNIBIRSent"]
                                    /\ UNCHANGED FlagOFCWorkerFailover
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstallOFC, FirstInstallNIB, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         IRQueueRC, SwSuspensionStatusRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         controllerStateOFC, IRQueueOFC, 
                                         SwSuspensionStatusOFC, 
                                         SetScheduledIRsOFC, 
                                         FlagOFCMonitorFailover, 
                                         FlagOFCNIBEventHandlerFailover, 
                                         OFCThreadID, OFC_READY, NIB2OFC, 
                                         NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                         FlagNIBFailover, 
                                         FlagNIBRCEventhandlerFailover, 
                                         FlagNIBOFCEventhandlerFailover, 
                                         NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         value_, nextTrans_, value_N, 
                                         rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug, 
                                         NIBMsg_, isBootStrap_, 
                                         toBeScheduledIRs, key, op1_, op2, 
                                         transaction_, nextIR, stepOfFailure_c, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure, transaction_c, NIBMsg, 
                                         op1, IRQueue, op_ir_status_change_, 
                                         removeIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

OFCThreadNotifyNIBIRSent(self) == /\ pc[self] = "OFCThreadNotifyNIBIRSent"
                                  /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF isOFCFailed(self)
                                        THEN /\ FlagOFCWorkerFailover' = TRUE
                                             /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                             /\ UNCHANGED << OFC2NIB, 
                                                             transaction_c, 
                                                             op_ir_status_change_ >>
                                        ELSE /\ isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID)
                                             /\ op_ir_status_change_' = [op_ir_status_change_ EXCEPT ![self] = [table |-> NIBT_IR_STATUS, key |-> nextIRToSent[self], value |-> IR_SENT]]
                                             /\ transaction_c' = [transaction_c EXCEPT ![self] = [name |-> "OFCChangeIRStatus2Sent", ops |-> <<op_ir_status_change_'[self]>>]]
                                             /\ OFC2NIB' = OFC2NIB \o <<transaction_c'[self]>>
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIRInner"]
                                             /\ UNCHANGED FlagOFCWorkerFailover
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstallOFC, 
                                                  FirstInstallNIB, 
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
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, IRQueueRC, 
                                                  SwSuspensionStatusRC, 
                                                  SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  controllerStateOFC, 
                                                  IRStatusOFC, IRQueueOFC, 
                                                  SwSuspensionStatusOFC, 
                                                  SetScheduledIRsOFC, 
                                                  FlagOFCMonitorFailover, 
                                                  FlagOFCNIBEventHandlerFailover, 
                                                  OFCThreadID, OFC_READY, 
                                                  NIB2OFC, NIB2RC, X2NIB, 
                                                  RC2NIB, FlagNIBFailover, 
                                                  FlagNIBRCEventhandlerFailover, 
                                                  FlagNIBOFCEventhandlerFailover, 
                                                  NIB_READY_FOR_RC, 
                                                  NIB_READY_FOR_OFC, 
                                                  masterState, 
                                                  controllerStateNIB, IRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  failedSet, statusResolveMsg, 
                                                  recoveredElem, value_, 
                                                  nextTrans_, value_N, 
                                                  rowRemove_, IR2Remove_, 
                                                  send_NIB_back_, 
                                                  stepOfFailure_, IRIndex_, 
                                                  debug_, nextTrans, value, 
                                                  rowRemove_N, IR2Remove, 
                                                  send_NIB_back, 
                                                  stepOfFailure_N, IRIndex, 
                                                  debug, NIBMsg_, isBootStrap_, 
                                                  toBeScheduledIRs, key, op1_, 
                                                  op2, transaction_, nextIR, 
                                                  stepOfFailure_c, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure, 
                                                  NIBMsg, op1, IRQueue, 
                                                  removeIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

ControllerThreadForwardIRInner(self) == /\ pc[self] = "ControllerThreadForwardIRInner"
                                        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ IF isOFCFailed(self)
                                              THEN /\ FlagOFCWorkerFailover' = TRUE
                                                   /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   controller2Switch >>
                                              ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![IR2SW[nextIRToSent[self]]] = Append(controller2Switch[IR2SW[nextIRToSent[self]]], [type |-> INSTALL_FLOW,
                                                                                                                                                                                          to |-> IR2SW[nextIRToSent[self]],
                                                                                                                                                                                          IR |-> nextIRToSent[self]])]
                                                   /\ IF whichSwitchModel(IR2SW[nextIRToSent[self]]) = SW_COMPLEX_MODEL
                                                         THEN /\ switchLock' = <<NIC_ASIC_IN, IR2SW[nextIRToSent[self]]>>
                                                         ELSE /\ switchLock' = <<SW_SIMPLE_ID, IR2SW[nextIRToSent[self]]>>
                                                   /\ pc' = [pc EXCEPT ![self] = "OFCRemoveIRFromIRQueueOFCLocal"]
                                                   /\ UNCHANGED FlagOFCWorkerFailover
                                        /\ UNCHANGED << controllerLock, 
                                                        FirstInstallOFC, 
                                                        FirstInstallNIB, 
                                                        sw_fail_ordering_var, 
                                                        ContProcSet, SwProcSet, 
                                                        swSeqChangedStatus, 
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
                                                        dependencyGraph, IR2SW, 
                                                        NIBUpdateForRC, 
                                                        controllerStateRC, 
                                                        IRStatusRC, IRQueueRC, 
                                                        SwSuspensionStatusRC, 
                                                        SetScheduledIRsRC, 
                                                        FlagRCNIBEventHandlerFailover, 
                                                        FlagRCSequencerFailover, 
                                                        RC_READY, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        controllerStateOFC, 
                                                        IRStatusOFC, 
                                                        IRQueueOFC, 
                                                        SwSuspensionStatusOFC, 
                                                        SetScheduledIRsOFC, 
                                                        FlagOFCMonitorFailover, 
                                                        FlagOFCNIBEventHandlerFailover, 
                                                        OFCThreadID, OFC_READY, 
                                                        NIB2OFC, NIB2RC, X2NIB, 
                                                        OFC2NIB, RC2NIB, 
                                                        FlagNIBFailover, 
                                                        FlagNIBRCEventhandlerFailover, 
                                                        FlagNIBOFCEventhandlerFailover, 
                                                        NIB_READY_FOR_RC, 
                                                        NIB_READY_FOR_OFC, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        IRStatus, 
                                                        SwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        SetScheduledIRs, 
                                                        X2NIB_len, NIBThreadID, 
                                                        RCThreadID, ingressPkt, 
                                                        ingressIR, egressMsg, 
                                                        ofaInMsg, 
                                                        ofaOutConfirmation, 
                                                        installerInIR, 
                                                        statusMsg, 
                                                        notFailedSet, 
                                                        failedElem, failedSet, 
                                                        statusResolveMsg, 
                                                        recoveredElem, value_, 
                                                        nextTrans_, value_N, 
                                                        rowRemove_, IR2Remove_, 
                                                        send_NIB_back_, 
                                                        stepOfFailure_, 
                                                        IRIndex_, debug_, 
                                                        nextTrans, value, 
                                                        rowRemove_N, IR2Remove, 
                                                        send_NIB_back, 
                                                        stepOfFailure_N, 
                                                        IRIndex, debug, 
                                                        NIBMsg_, isBootStrap_, 
                                                        toBeScheduledIRs, key, 
                                                        op1_, op2, 
                                                        transaction_, nextIR, 
                                                        stepOfFailure_c, 
                                                        transaction_O, 
                                                        IRQueueTmp, NIBMsg_O, 
                                                        isBootStrap, 
                                                        localIRSet, NIBIRSet, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure, 
                                                        transaction_c, NIBMsg, 
                                                        op1, IRQueue, 
                                                        op_ir_status_change_, 
                                                        removeIR, msg, 
                                                        op_ir_status_change, 
                                                        op_first_install, 
                                                        transaction >>

OFCRemoveIRFromIRQueueOFCLocal(self) == /\ pc[self] = "OFCRemoveIRFromIRQueueOFCLocal"
                                        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ IF isOFCFailed(self)
                                              THEN /\ FlagOFCWorkerFailover' = TRUE
                                                   /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                                   /\ UNCHANGED << IRQueueOFC, 
                                                                   rowRemove, 
                                                                   removeIR >>
                                              ELSE /\ IF \E i \in DOMAIN IRQueueOFC: IRQueueOFC[i].IR = nextIRToSent[self]
                                                         THEN /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self, IRQueueOFC)]
                                                              /\ IRQueueOFC' = removeFromSeq(IRQueueOFC, rowRemove'[self])
                                                              /\ removeIR' = [removeIR EXCEPT ![self] = TRUE]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << IRQueueOFC, 
                                                                              rowRemove, 
                                                                              removeIR >>
                                                   /\ pc' = [pc EXCEPT ![self] = "OFCRemoveIRFromIRQueueRemote"]
                                                   /\ UNCHANGED FlagOFCWorkerFailover
                                        /\ UNCHANGED << switchLock, 
                                                        controllerLock, 
                                                        FirstInstallOFC, 
                                                        FirstInstallNIB, 
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
                                                        Ofa2InstallerBuff, 
                                                        TCAM, 
                                                        controlMsgCounter, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        dependencyGraph, IR2SW, 
                                                        NIBUpdateForRC, 
                                                        controllerStateRC, 
                                                        IRStatusRC, IRQueueRC, 
                                                        SwSuspensionStatusRC, 
                                                        SetScheduledIRsRC, 
                                                        FlagRCNIBEventHandlerFailover, 
                                                        FlagRCSequencerFailover, 
                                                        RC_READY, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        controllerStateOFC, 
                                                        IRStatusOFC, 
                                                        SwSuspensionStatusOFC, 
                                                        SetScheduledIRsOFC, 
                                                        FlagOFCMonitorFailover, 
                                                        FlagOFCNIBEventHandlerFailover, 
                                                        OFCThreadID, OFC_READY, 
                                                        NIB2OFC, NIB2RC, X2NIB, 
                                                        OFC2NIB, RC2NIB, 
                                                        FlagNIBFailover, 
                                                        FlagNIBRCEventhandlerFailover, 
                                                        FlagNIBOFCEventhandlerFailover, 
                                                        NIB_READY_FOR_RC, 
                                                        NIB_READY_FOR_OFC, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        IRStatus, 
                                                        SwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        SetScheduledIRs, 
                                                        X2NIB_len, NIBThreadID, 
                                                        RCThreadID, ingressPkt, 
                                                        ingressIR, egressMsg, 
                                                        ofaInMsg, 
                                                        ofaOutConfirmation, 
                                                        installerInIR, 
                                                        statusMsg, 
                                                        notFailedSet, 
                                                        failedElem, failedSet, 
                                                        statusResolveMsg, 
                                                        recoveredElem, value_, 
                                                        nextTrans_, value_N, 
                                                        rowRemove_, IR2Remove_, 
                                                        send_NIB_back_, 
                                                        stepOfFailure_, 
                                                        IRIndex_, debug_, 
                                                        nextTrans, value, 
                                                        rowRemove_N, IR2Remove, 
                                                        send_NIB_back, 
                                                        stepOfFailure_N, 
                                                        IRIndex, debug, 
                                                        NIBMsg_, isBootStrap_, 
                                                        toBeScheduledIRs, key, 
                                                        op1_, op2, 
                                                        transaction_, nextIR, 
                                                        stepOfFailure_c, 
                                                        transaction_O, 
                                                        IRQueueTmp, NIBMsg_O, 
                                                        isBootStrap, 
                                                        localIRSet, NIBIRSet, 
                                                        nextIRToSent, rowIndex, 
                                                        stepOfFailure, 
                                                        transaction_c, NIBMsg, 
                                                        op1, IRQueue, 
                                                        op_ir_status_change_, 
                                                        msg, 
                                                        op_ir_status_change, 
                                                        op_first_install, 
                                                        transaction >>

OFCRemoveIRFromIRQueueRemote(self) == /\ pc[self] = "OFCRemoveIRFromIRQueueRemote"
                                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ IF isOFCFailed(self)
                                            THEN /\ FlagOFCWorkerFailover' = TRUE
                                                 /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                                 /\ UNCHANGED << OFC2NIB, 
                                                                 transaction_c, 
                                                                 op1, removeIR >>
                                            ELSE /\ IF removeIR[self] = TRUE
                                                       THEN /\ isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID)
                                                            /\ op1' = [op1 EXCEPT ![self] = [table |-> NIBT_IR_QUEUE, key |-> nextIRToSent[self]]]
                                                            /\ transaction_c' = [transaction_c EXCEPT ![self] = [name |-> "RemoveIR", ops |-> <<op1'[self]>>]]
                                                            /\ OFC2NIB' = OFC2NIB \o <<transaction_c'[self]>>
                                                            /\ removeIR' = [removeIR EXCEPT ![self] = FALSE]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED << OFC2NIB, 
                                                                            transaction_c, 
                                                                            op1, 
                                                                            removeIR >>
                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                                 /\ UNCHANGED FlagOFCWorkerFailover
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      FirstInstallOFC, 
                                                      FirstInstallNIB, 
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
                                                      NIBUpdateForRC, 
                                                      controllerStateRC, 
                                                      IRStatusRC, IRQueueRC, 
                                                      SwSuspensionStatusRC, 
                                                      SetScheduledIRsRC, 
                                                      FlagRCNIBEventHandlerFailover, 
                                                      FlagRCSequencerFailover, 
                                                      RC_READY, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      controllerStateOFC, 
                                                      IRStatusOFC, IRQueueOFC, 
                                                      SwSuspensionStatusOFC, 
                                                      SetScheduledIRsOFC, 
                                                      FlagOFCMonitorFailover, 
                                                      FlagOFCNIBEventHandlerFailover, 
                                                      OFCThreadID, OFC_READY, 
                                                      NIB2OFC, NIB2RC, X2NIB, 
                                                      RC2NIB, FlagNIBFailover, 
                                                      FlagNIBRCEventhandlerFailover, 
                                                      FlagNIBOFCEventhandlerFailover, 
                                                      NIB_READY_FOR_RC, 
                                                      NIB_READY_FOR_OFC, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      IRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      X2NIB_len, NIBThreadID, 
                                                      RCThreadID, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, value_, 
                                                      nextTrans_, value_N, 
                                                      rowRemove_, IR2Remove_, 
                                                      send_NIB_back_, 
                                                      stepOfFailure_, IRIndex_, 
                                                      debug_, nextTrans, value, 
                                                      rowRemove_N, IR2Remove, 
                                                      send_NIB_back, 
                                                      stepOfFailure_N, IRIndex, 
                                                      debug, NIBMsg_, 
                                                      isBootStrap_, 
                                                      toBeScheduledIRs, key, 
                                                      op1_, op2, transaction_, 
                                                      nextIR, stepOfFailure_c, 
                                                      transaction_O, 
                                                      IRQueueTmp, NIBMsg_O, 
                                                      isBootStrap, localIRSet, 
                                                      NIBIRSet, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure, NIBMsg, 
                                                      IRQueue, 
                                                      op_ir_status_change_, 
                                                      msg, op_ir_status_change, 
                                                      op_first_install, 
                                                      transaction >>

OFCWorkerFailover(self) == /\ pc[self] = "OFCWorkerFailover"
                           /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ isOFCUp(OFCThreadID)
                           /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstallOFC, FirstInstallNIB, 
                                           sw_fail_ordering_var, ContProcSet, 
                                           SwProcSet, swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           IR2SW, NIBUpdateForRC, 
                                           controllerStateRC, IRStatusRC, 
                                           IRQueueRC, SwSuspensionStatusRC, 
                                           SetScheduledIRsRC, 
                                           FlagRCNIBEventHandlerFailover, 
                                           FlagRCSequencerFailover, RC_READY, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, 
                                           controllerStateOFC, IRStatusOFC, 
                                           IRQueueOFC, SwSuspensionStatusOFC, 
                                           SetScheduledIRsOFC, 
                                           FlagOFCWorkerFailover, 
                                           FlagOFCMonitorFailover, 
                                           FlagOFCNIBEventHandlerFailover, 
                                           OFCThreadID, OFC_READY, NIB2OFC, 
                                           NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                           FlagNIBFailover, 
                                           FlagNIBRCEventhandlerFailover, 
                                           FlagNIBOFCEventhandlerFailover, 
                                           NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                           masterState, controllerStateNIB, 
                                           IRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, SetScheduledIRs, 
                                           X2NIB_len, NIBThreadID, RCThreadID, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, failedSet, 
                                           statusResolveMsg, recoveredElem, 
                                           value_, nextTrans_, value_N, 
                                           rowRemove_, IR2Remove_, 
                                           send_NIB_back_, stepOfFailure_, 
                                           IRIndex_, debug_, nextTrans, value, 
                                           rowRemove_N, IR2Remove, 
                                           send_NIB_back, stepOfFailure_N, 
                                           IRIndex, debug, NIBMsg_, 
                                           isBootStrap_, toBeScheduledIRs, key, 
                                           op1_, op2, transaction_, nextIR, 
                                           stepOfFailure_c, transaction_O, 
                                           IRQueueTmp, NIBMsg_O, isBootStrap, 
                                           localIRSet, NIBIRSet, nextIRToSent, 
                                           rowIndex, rowRemove, stepOfFailure, 
                                           transaction_c, NIBMsg, op1, IRQueue, 
                                           op_ir_status_change_, removeIR, msg, 
                                           op_ir_status_change, 
                                           op_first_install, transaction >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ OFCThreadGetNextIR(self)
                                    \/ OFCThreadSendIR(self)
                                    \/ OFCThreadNotifyNIBIRSent(self)
                                    \/ ControllerThreadForwardIRInner(self)
                                    \/ OFCRemoveIRFromIRQueueOFCLocal(self)
                                    \/ OFCRemoveIRFromIRQueueRemote(self)
                                    \/ OFCWorkerFailover(self)

OFCMonitorCheckIfMastr(self) == /\ pc[self] = "OFCMonitorCheckIfMastr"
                                /\ controllerIsMaster(self[1])
                                /\ IF isOFCFailed(self)
                                      THEN /\ FlagOFCMonitorFailover' = TRUE
                                           /\ pc' = [pc EXCEPT ![self] = "OFCMonitorFailover"]
                                           /\ UNCHANGED << controllerLock, msg >>
                                      ELSE /\ switch2Controller # <<>>
                                           /\ \/ controllerLock = self
                                              \/ controllerLock = <<NO_LOCK, NO_LOCK>>
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                           /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                           /\ Assert(msg'[self].from = IR2SW[msg'[self].IR], 
                                                     "Failure of assertion at line 2327, column 13.")
                                           /\ Assert(msg'[self].type \in {RECONCILIATION_RESPONSE, RECEIVED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                     "Failure of assertion at line 2328, column 13.")
                                           /\ pc' = [pc EXCEPT ![self] = "OFCMonitorUpdateIRDone"]
                                           /\ UNCHANGED FlagOFCMonitorFailover
                                /\ UNCHANGED << switchLock, FirstInstallOFC, 
                                                FirstInstallNIB, 
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
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                IRQueueRC, 
                                                SwSuspensionStatusRC, 
                                                SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                controllerStateOFC, 
                                                IRStatusOFC, IRQueueOFC, 
                                                SwSuspensionStatusOFC, 
                                                SetScheduledIRsOFC, 
                                                FlagOFCWorkerFailover, 
                                                FlagOFCNIBEventHandlerFailover, 
                                                OFCThreadID, OFC_READY, 
                                                NIB2OFC, NIB2RC, X2NIB, 
                                                OFC2NIB, RC2NIB, 
                                                FlagNIBFailover, 
                                                FlagNIBRCEventhandlerFailover, 
                                                FlagNIBOFCEventhandlerFailover, 
                                                NIB_READY_FOR_RC, 
                                                NIB_READY_FOR_OFC, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, X2NIB_len, 
                                                NIBThreadID, RCThreadID, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug, NIBMsg_, 
                                                isBootStrap_, toBeScheduledIRs, 
                                                key, op1_, op2, transaction_, 
                                                nextIR, stepOfFailure_c, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure, 
                                                transaction_c, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, op_ir_status_change, 
                                                op_first_install, transaction >>

OFCMonitorUpdateIRDone(self) == /\ pc[self] = "OFCMonitorUpdateIRDone"
                                /\ IF msg[self].type = INSTALLED_SUCCESSFULLY
                                      THEN /\ pc' = [pc EXCEPT ![self] = "OFCUpdateIRDone"]
                                      ELSE /\ Assert(FALSE, 
                                                     "Failure of assertion at line 2359, column 13.")
                                           /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstallOFC, 
                                                FirstInstallNIB, 
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
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                IRQueueRC, 
                                                SwSuspensionStatusRC, 
                                                SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                controllerStateOFC, 
                                                IRStatusOFC, IRQueueOFC, 
                                                SwSuspensionStatusOFC, 
                                                SetScheduledIRsOFC, 
                                                FlagOFCWorkerFailover, 
                                                FlagOFCMonitorFailover, 
                                                FlagOFCNIBEventHandlerFailover, 
                                                OFCThreadID, OFC_READY, 
                                                NIB2OFC, NIB2RC, X2NIB, 
                                                OFC2NIB, RC2NIB, 
                                                FlagNIBFailover, 
                                                FlagNIBRCEventhandlerFailover, 
                                                FlagNIBOFCEventhandlerFailover, 
                                                NIB_READY_FOR_RC, 
                                                NIB_READY_FOR_OFC, masterState, 
                                                controllerStateNIB, IRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, X2NIB_len, 
                                                NIBThreadID, RCThreadID, 
                                                ingressPkt, ingressIR, 
                                                egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug, NIBMsg_, 
                                                isBootStrap_, toBeScheduledIRs, 
                                                key, op1_, op2, transaction_, 
                                                nextIR, stepOfFailure_c, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure, 
                                                transaction_c, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, msg, 
                                                op_ir_status_change, 
                                                op_first_install, transaction >>

OFCUpdateIRDone(self) == /\ pc[self] = "OFCUpdateIRDone"
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                         /\ IF isOFCFailed(self)
                               THEN /\ FlagOFCMonitorFailover' = TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "OFCMonitorFailover"]
                                    /\ UNCHANGED << FirstInstallOFC, 
                                                    IRStatusOFC >>
                               ELSE /\ IRStatusOFC' = [IRStatusOFC EXCEPT ![msg[self].IR] = IR_DONE]
                                    /\ FirstInstallOFC' = [FirstInstallOFC EXCEPT ![msg[self].IR] = 1]
                                    /\ pc' = [pc EXCEPT ![self] = "OFCUpdateNIBIRDONE"]
                                    /\ UNCHANGED FlagOFCMonitorFailover
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         IR2SW, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         IRQueueRC, SwSuspensionStatusRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         controllerStateOFC, IRQueueOFC, 
                                         SwSuspensionStatusOFC, 
                                         SetScheduledIRsOFC, 
                                         FlagOFCWorkerFailover, 
                                         FlagOFCNIBEventHandlerFailover, 
                                         OFCThreadID, OFC_READY, NIB2OFC, 
                                         NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                         FlagNIBFailover, 
                                         FlagNIBRCEventhandlerFailover, 
                                         FlagNIBOFCEventhandlerFailover, 
                                         NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                         masterState, controllerStateNIB, 
                                         IRStatus, SwSuspensionStatus, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, failedSet, 
                                         statusResolveMsg, recoveredElem, 
                                         value_, nextTrans_, value_N, 
                                         rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug, 
                                         NIBMsg_, isBootStrap_, 
                                         toBeScheduledIRs, key, op1_, op2, 
                                         transaction_, nextIR, stepOfFailure_c, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure, transaction_c, NIBMsg, 
                                         op1, IRQueue, op_ir_status_change_, 
                                         removeIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

OFCUpdateNIBIRDONE(self) == /\ pc[self] = "OFCUpdateNIBIRDONE"
                            /\ IF isOFCFailed(self)
                                  THEN /\ FlagOFCMonitorFailover' = TRUE
                                       /\ pc' = [pc EXCEPT ![self] = "OFCMonitorFailover"]
                                       /\ UNCHANGED << OFC2NIB, 
                                                       op_ir_status_change, 
                                                       op_first_install, 
                                                       transaction >>
                                  ELSE /\ isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID)
                                       /\ op_ir_status_change' = [op_ir_status_change EXCEPT ![self] = [table |-> NIBT_IR_STATUS, key |-> msg[self].IR, value |-> IR_DONE]]
                                       /\ op_first_install' = [op_first_install EXCEPT ![self] = [table |-> NIBT_FIRST_INSTALL, key |-> msg[self].IR, value |-> 1]]
                                       /\ transaction' = [transaction EXCEPT ![self] = [name |-> "FirstInstallIR",
                                                                                        ops |-> <<op_ir_status_change'[self], op_first_install'[self]>>]]
                                       /\ OFC2NIB' = OFC2NIB \o <<transaction'[self]>>
                                       /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                       /\ UNCHANGED FlagOFCMonitorFailover
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            IRQueueRC, SwSuspensionStatusRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            controllerStateOFC, IRStatusOFC, 
                                            IRQueueOFC, SwSuspensionStatusOFC, 
                                            SetScheduledIRsOFC, 
                                            FlagOFCWorkerFailover, 
                                            FlagOFCNIBEventHandlerFailover, 
                                            OFCThreadID, OFC_READY, NIB2OFC, 
                                            NIB2RC, X2NIB, RC2NIB, 
                                            FlagNIBFailover, 
                                            FlagNIBRCEventhandlerFailover, 
                                            FlagNIBOFCEventhandlerFailover, 
                                            NIB_READY_FOR_RC, 
                                            NIB_READY_FOR_OFC, masterState, 
                                            controllerStateNIB, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug, NIBMsg_, 
                                            isBootStrap_, toBeScheduledIRs, 
                                            key, op1_, op2, transaction_, 
                                            nextIR, stepOfFailure_c, 
                                            transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, nextIRToSent, rowIndex, 
                                            rowRemove, stepOfFailure, 
                                            transaction_c, NIBMsg, op1, 
                                            IRQueue, op_ir_status_change_, 
                                            removeIR, msg >>

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
                                                    /\ pc' = [pc EXCEPT ![self] = "OFCMonitorCheckIfMastr"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "OFCMonitorCheckIfMastr"]
                                                    /\ UNCHANGED switch2Controller
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         FirstInstallOFC, 
                                                         FirstInstallNIB, 
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
                                                         IR2SW, NIBUpdateForRC, 
                                                         controllerStateRC, 
                                                         IRStatusRC, IRQueueRC, 
                                                         SwSuspensionStatusRC, 
                                                         SetScheduledIRsRC, 
                                                         FlagRCNIBEventHandlerFailover, 
                                                         FlagRCSequencerFailover, 
                                                         RC_READY, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         controllerStateOFC, 
                                                         IRStatusOFC, 
                                                         IRQueueOFC, 
                                                         SwSuspensionStatusOFC, 
                                                         SetScheduledIRsOFC, 
                                                         FlagOFCWorkerFailover, 
                                                         FlagOFCMonitorFailover, 
                                                         FlagOFCNIBEventHandlerFailover, 
                                                         OFCThreadID, 
                                                         OFC_READY, NIB2OFC, 
                                                         NIB2RC, X2NIB, 
                                                         OFC2NIB, RC2NIB, 
                                                         FlagNIBFailover, 
                                                         FlagNIBRCEventhandlerFailover, 
                                                         FlagNIBOFCEventhandlerFailover, 
                                                         NIB_READY_FOR_RC, 
                                                         NIB_READY_FOR_OFC, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         IRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         X2NIB_len, 
                                                         NIBThreadID, 
                                                         RCThreadID, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, value_, 
                                                         nextTrans_, value_N, 
                                                         rowRemove_, 
                                                         IR2Remove_, 
                                                         send_NIB_back_, 
                                                         stepOfFailure_, 
                                                         IRIndex_, debug_, 
                                                         nextTrans, value, 
                                                         rowRemove_N, 
                                                         IR2Remove, 
                                                         send_NIB_back, 
                                                         stepOfFailure_N, 
                                                         IRIndex, debug, 
                                                         NIBMsg_, isBootStrap_, 
                                                         toBeScheduledIRs, key, 
                                                         op1_, op2, 
                                                         transaction_, nextIR, 
                                                         stepOfFailure_c, 
                                                         transaction_O, 
                                                         IRQueueTmp, NIBMsg_O, 
                                                         isBootStrap, 
                                                         localIRSet, NIBIRSet, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure, 
                                                         transaction_c, NIBMsg, 
                                                         op1, IRQueue, 
                                                         op_ir_status_change_, 
                                                         removeIR, msg, 
                                                         op_ir_status_change, 
                                                         op_first_install, 
                                                         transaction >>

OFCMonitorFailover(self) == /\ pc[self] = "OFCMonitorFailover"
                            /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ isOFCUp(OFCThreadID)
                            /\ pc' = [pc EXCEPT ![self] = "OFCMonitorCheckIfMastr"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            IR2SW, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            IRQueueRC, SwSuspensionStatusRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            controllerStateOFC, IRStatusOFC, 
                                            IRQueueOFC, SwSuspensionStatusOFC, 
                                            SetScheduledIRsOFC, 
                                            FlagOFCWorkerFailover, 
                                            FlagOFCMonitorFailover, 
                                            FlagOFCNIBEventHandlerFailover, 
                                            OFCThreadID, OFC_READY, NIB2OFC, 
                                            NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                            FlagNIBFailover, 
                                            FlagNIBRCEventhandlerFailover, 
                                            FlagNIBOFCEventhandlerFailover, 
                                            NIB_READY_FOR_RC, 
                                            NIB_READY_FOR_OFC, masterState, 
                                            controllerStateNIB, IRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug, NIBMsg_, 
                                            isBootStrap_, toBeScheduledIRs, 
                                            key, op1_, op2, transaction_, 
                                            nextIR, stepOfFailure_c, 
                                            transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, nextIRToSent, rowIndex, 
                                            rowRemove, stepOfFailure, 
                                            transaction_c, NIBMsg, op1, 
                                            IRQueue, op_ir_status_change_, 
                                            removeIR, msg, op_ir_status_change, 
                                            op_first_install, transaction >>

controllerMonitoringServer(self) == OFCMonitorCheckIfMastr(self)
                                       \/ OFCMonitorUpdateIRDone(self)
                                       \/ OFCUpdateIRDone(self)
                                       \/ OFCUpdateNIBIRDONE(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ OFCMonitorFailover(self)

Next == (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
           \/ (\E self \in ({NIC_ASIC_IN} \X SW): swNicAsicProcPacketIn(self))
           \/ (\E self \in ({NIC_ASIC_OUT} \X SW): swNicAsicProcPacketOut(self))
           \/ (\E self \in ({OFA_IN} \X SW): ofaModuleProcPacketIn(self))
           \/ (\E self \in ({OFA_OUT} \X SW): ofaModuleProcPacketOut(self))
           \/ (\E self \in ({INSTALLER} \X SW): installerModuleProc(self))
           \/ (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
           \/ (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
           \/ (\E self \in ({GHOST_UNLOCK_PROC} \X SW): ghostUnlockProcess(self))
           \/ (\E self \in ({"proc"} \X {CONT_NIB_FAILOVER}): NIBFailoverProc(self))
           \/ (\E self \in ({nib0} \X {CONT_NIB_RC_EVENT}): NIBRCEventHandler(self))
           \/ (\E self \in ({nib0} \X {CONT_NIB_OFC_EVENT}): NIBOFCEventHandler(self))
           \/ (\E self \in ({"proc"} \X {RC_FAILOVER}): RCFailoverProc(self))
           \/ (\E self \in ({rc0} \X {CONT_RC_NIB_EVENT}): RCNIBEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_SEQ}): controllerSequencer(self))
           \/ (\E self \in ( {"proc"} \X {OFC_FAILURE}): OFCFailureProc(self))
           \/ (\E self \in ({"proc"} \X {OFC_FAILOVER}): OFCFailoverProc(self))
           \/ (\E self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}): OFCNIBEventHandler(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))

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
        /\ \A self \in ({"proc"} \X {CONT_NIB_FAILOVER}) : WF_vars(NIBFailoverProc(self))
        /\ \A self \in ({nib0} \X {CONT_NIB_RC_EVENT}) : WF_vars(NIBRCEventHandler(self))
        /\ \A self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) : WF_vars(NIBOFCEventHandler(self))
        /\ \A self \in ({"proc"} \X {RC_FAILOVER}) : WF_vars(RCFailoverProc(self))
        /\ \A self \in ({rc0} \X {CONT_RC_NIB_EVENT}) : WF_vars(RCNIBEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ( {"proc"} \X {OFC_FAILURE}) : WF_vars(OFCFailureProc(self))
        /\ \A self \in ({"proc"} \X {OFC_FAILOVER}) : WF_vars(OFCFailoverProc(self))
        /\ \A self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) : WF_vars(OFCNIBEventHandler(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-16b93345e15cd6acc93cabc865786300
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

\*RedundantInstallation == \A x \in 1..MaxNumIRs: \/ IRStatusOFC[x] = IR_DONE
\*                                                \/ FirstInstallOFC[x] = 0
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)
                                                         /\ <<y, x>> \notin dependencyGraph
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<x, y>> \notin dependencyGraph
Debug == (Len(X2NIB) < 20)

=============================================================================
\* Modification History
\* Last modified Sun May 02 15:54:59 PDT 2021 by zmy
\* Last modified Sun Feb 14 21:50:09 PST 2021 by root
\* Created Thu Nov 19 19:02:15 PST 2020 by root

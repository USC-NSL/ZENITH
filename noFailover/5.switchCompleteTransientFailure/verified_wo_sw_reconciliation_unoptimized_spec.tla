------------------- MODULE SwitchCompleteTransientFailure -------------------
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
          CONT_WORKER_SEQ, CONT_BOSS_SEQ, 
          \* id for sequencer (type: model value)
          CONT_MONITOR,
          \* id for monitoring server (type: model value) 
          CONT_EVENT,
          \* id for event handler (type: model value)
          WATCH_DOG,
          \* id for watch dog (type: model value)
          NIB_EVENT_HANDLER,
          CONT_TE
          
(***************************************************************************)
(*********************** SW/IR/DAG state identifiers ***********************)
(***************************************************************************)
CONSTANTS IR_NONE,
          IR_SENT,
          IR_RECONCILE,
          IR_DONE,
          SW_RUN,
          SW_SUSPEND,
          IR_UNLOCK,
          DAG_UNLOCK,
          DAG_STALE,
          DAG_NEW,
          DAG_SUBMIT,
          DAG_NONE,
          SEQ_WORKER_RUN,
          SEQ_WORKER_STALE_SIGNAL,
          SEQ_WORKER_STALE_REMOVED
          
(***************************************************************************)
(*************************** Failure Status ********************************)
(***************************************************************************)
CONSTANTS NotFailed, 
          Failed           

(***************************************************************************)
(*********************** NIB notification semantics ************************)
(***************************************************************************)
CONSTANTS TOPO_MOD,
          IR_MOD
                    
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
          DELETE_FLOW,
          INSTALLED_SUCCESSFULLY,
          DELETED_SUCCESSFULLY, 
          KEEP_ALIVE,
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
          SW_FAIL_ORDERING,
          TOPO_DAG_MAPPING,
          SW_MODULE_CAN_FAIL_OR_NOT,
          FINAL_DAG,
          IR2SW,
          IR2FLOW,
          MaxNumFlows
          
                    
(* Assumption1: at most one instruction is associated with one switch *)
ASSUME MaxNumIRs >= Cardinality({TOPO_DAG_MAPPING[i]: i \in DOMAIN TOPO_DAG_MAPPING})
(* Assumption2: MAX_NUM_CONTROLLER_SUB_FAILURE is a function from control plane *)
(* modules (e.g. OFC, RC) to maximum number of submodule failure each can face *)
ASSUME {"ofc0", "rc0"} \subseteq DOMAIN MAX_NUM_CONTROLLER_SUB_FAILURE
(* WHICH_SWITCH_MODEL should be a valid function with domain SW *)
ASSUME WHICH_SWITCH_MODEL \in [SW -> {SW_SIMPLE_MODEL, SW_COMPLEX_MODEL}]
(* SW_FAIL_ORDERING should have correct form *)
ASSUME \A x \in {SW_FAIL_ORDERING[z]: z \in DOMAIN SW_FAIL_ORDERING}: \/ x = {}
                                                                      \/ \A y \in x: /\ "transient" \in DOMAIN y
                                                                                     /\ "sw" \in DOMAIN y
                                                                                     /\ "partial" \in DOMAIN y
                                                                                     /\ y.transient \in {0, 1}
                                                                                     /\ y.sw \in SW          
                                                                                     /\ y.partial \in {0, 1}
(* SW_MODULE_CAN_FAIL_OR_NOT should cover all the switch elements *)
ASSUME /\ "cpu" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "nicAsic" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "ofa" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT
       /\ "installer" \in DOMAIN SW_MODULE_CAN_FAIL_OR_NOT

ASSUME \A x \in DOMAIN TOPO_DAG_MAPPING: /\ "v" \in DOMAIN TOPO_DAG_MAPPING[x]
                                         /\ "e" \in DOMAIN TOPO_DAG_MAPPING[x]        

ASSUME \A x \in 1..MaxNumIRs: x \in DOMAIN IR2SW
ASSUME \A x \in 1..MaxNumIRs: /\ x \in DOMAIN IR2FLOW
                              /\ IR2FLOW[x] \in 1..MaxNumFlows
       
(*--fair algorithm stateConsistency
(************************* variables ***************************************)
    variables (*************** Some Auxiliary Vars ***********************)
              switchLock = <<NO_LOCK, NO_LOCK>>,
              controllerLock = <<NO_LOCK, NO_LOCK>>, 
              FirstInstall = [x \in 1..MaxNumIRs |-> 0],
              sw_fail_ordering_var = SW_FAIL_ORDERING,
              ContProcSet = ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR,
                                          NIB_EVENT_HANDLER, CONT_TE}) \cup 
                                ({ofc0} \X {CONT_EVENT, CONT_MONITOR}) \cup
                                ({ofc0} \X CONTROLLER_THREAD_POOL),
              SwProcSet = (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) 
                            \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) 
                            \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) 
                            \cup (({SW_RESOLVE_PROC} \X SW)),
              \* irTypeMapping is a mapping from irIR to {INSTALL_FLOW, DELETE_FLOW}
              \* it should be encoded into the IR msg from RC to NIB to OFC. However, to 
              \* simplify the abstraction, we keep it in this static mapping.
              irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]],
              ir2sw = IR2SW,
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
              switchStatus = [x \in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed, 
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
              \* auxiliary variable to determine the recovery state of switch
              RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]],
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
              \* dependencyGraph \in generateConnectedDAG(1..MaxNumIRs),
              \*IR2SW = CHOOSE x \in [1..MaxNumIRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z 
              \*                                                                  /\ switchOrdering[x[y]] =< switchOrdering[x[z]],
              TEEventQueue = [x \in {rc0} |-> <<>>],
              DAGEventQueue = [x \in {rc0} |-> <<>>],
              DAGQueue = [x \in {rc0} |-> <<>>],
              DAGID = 0,
              MaxDAGID = 15,
              DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
              RCNIBEventQueue = [x \in {rc0} |-> <<>>],
              RCIRStatus = [x \in {rc0} |-> [y \in 1..MaxNumIRs |-> IR_NONE]],
              RCSwSuspensionStatus = [x \in {rc0} |-> [y \in SW |-> SW_RUN]],
              nxtRCIRID = MaxNumIRs + 10,
              idWorkerWorkingOnDAG = [x \in 1..MaxDAGID |-> DAG_UNLOCK],
              RCSeqWorkerStatus = (CONT_WORKER_SEQ :> SEQ_WORKER_RUN),
              IRDoneSet = [x \in {rc0} |-> {}],
              (********************** OFC Vars ****************************)
              \************** Workers ********************
              \* idThreadWorkingOnIR is a logical semaphore used for 
              \* synchronization between IRs
              idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK] @@ [x \in (MaxNumIRs + 10)..(MaxNumIRs + 20) |-> IR_UNLOCK],
              \* WorkerThreadRanking is an auxiliary variable used for 
              \* reducing the number of possible behaviours by applying
              \* the following rule; if two workers try to get the lock 
              \* for an IR, the one with lower ranking always gets it. 
              workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
              
              (********************* NIB Vars *****************************)
              masterState = [ofc0 |-> "primary", rc0 |-> "primary"],
              controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]],
              NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE], 
              SwSuspensionStatus = [x \in SW |-> SW_RUN],
              IRQueueNIB = <<>>,
              \* notificationNIB = [y \in {c0, c1} |-> [RCS |-> [IRQueueNIB |-> <<>>]]], 
              SetScheduledIRs = [y \in SW |-> {}] 
              
    define
        (********************* Auxiliary functions **********************)
        max(set) == CHOOSE x \in set: \A y \in set: x \geq y
        min(set) == CHOOSE x \in set: \A y \in set: x \leq y 
        rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
        indexInSeq(seq, val) == CHOOSE i \in DOMAIN seq: seq[i] = val
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
        \* for final check
        listDownSwitches(swList) == {sw \in swList: \/ switchStatus[sw].cpu = Failed
                                        \/ switchStatus[sw].ofa = Failed
                                        \/ switchStatus[sw].installer = Failed
                                        \/ switchStatus[sw].nicAsic = Failed}
        
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
        returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                                                             /\ \/ /\ WHICH_SWITCH_MODEL[x] = SW_COMPLEX_MODEL
                                                                                   /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1
                                                                                \/ /\ WHICH_SWITCH_MODEL[x] = SW_SIMPLE_MODEL
                                                                                   /\ x = "nicAsic"}
        \* getSetIRsForSwitch is for verification optimization reasons
        getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}
        
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
        existIRIndexToRead(threadID) == \E x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                                    \/ /\ NoEntryTaggedWith(threadID)
                                                                       /\ FirstUntaggedEntry(threadID, x)
                                                                       /\ IRQueueNIB[x].tag = NO_TAG
        getFirstIndexWith(RID, threadID) == CHOOSE x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = threadID
                                                                            /\ IRQueueNIB[x].IR = RID
                                                                   
        (****************** RC (routing controller) **************************)
        \****************************** TE ***********************************
        getSetRemovableIRs(CID, swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ RCIRStatus[CID][x] # IR_NONE
                                                                           \/ x \in SetScheduledIRs[ir2sw[x]]
                                                                        /\ x \notin nxtDAGV
                                                                        /\ ir2sw[x] \in swSet}
        getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: ir2sw[x] = swID}
        
        \*************************** Sequencer *******************************
        isDependencySatisfied(CID, DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                                /\ RCIRStatus[CID][y] # IR_DONE
        getSetIRsCanBeScheduledNext(CID, DAG)  == {x \in DAG.v: /\ RCIRStatus[CID][x] = IR_NONE
                                                                /\ isDependencySatisfied(CID, DAG, x)
                                                                /\ RCSwSuspensionStatus[CID][ir2sw[x]] = SW_RUN
                                                                /\ x \notin SetScheduledIRs[ir2sw[x]]}
        allIRsInDAGInstalled(CID, DAG) == ~\E y \in DAG.v: RCIRStatus[CID][y] # IR_DONE
        isDAGStale(id) == DAGState[id] # DAG_SUBMIT
        
        \*************************** Monitor *********************************
        existIRInSetScheduledIRs(CID, swID, type, flowID) == \E x \in SetScheduledIRs[swID]: /\ irTypeMapping[x].type = type
                                                                                             /\ ir2sw[x] = swID
                                                                                             /\ irTypeMapping[x].flow = flowID
        existIRDeletionInIRSent(CID, swID, flowID) == \E x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = DELETE_FLOW
                                                                                     /\ ir2sw[x] = swID
                                                                                     /\ irTypeMapping[x].flow = flowID
                                                                                     /\ RCIRStatus[CID][x] = IR_SENT
        irMonitorShouldScheduleIR(CID, irID) == \/ /\ irID \in IRDoneSet[CID]
                                                   /\ RCIRStatus[CID][irID] = IR_NONE
                                                   /\ RCSwSuspensionStatus[CID][IR2SW[irID]] = SW_RUN
                                                   /\ ~existIRInSetScheduledIRs(CID, ir2sw[irID], INSTALL_FLOW, irTypeMapping[irID].flow)
                                                \/ /\ irID \in (1..MaxNumIRs) \ IRDoneSet[CID]
                                                   /\ RCIRStatus[CID][irID] = IR_DONE
                                                   /\ RCSwSuspensionStatus[CID][IR2SW[irID]] = SW_RUN
                                                   /\ ~ existIRInSetScheduledIRs(CID, ir2sw[irID], DELETE_FLOW, irTypeMapping[irID].flow)
                                                   /\ ~ existIRDeletionInIRSent(CID, ir2sw[irID], irTypeMapping[irID].flow)
        setIRMonitorShouldSchedule(CID) == {x \in 1..MaxNumIRs: irMonitorShouldScheduleIR(CID, x)}                                         
                                                    
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
                                                                                         /\ pc[<<CID, x>>] = "ControllerThread3"}
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
        
                                                               
        \* getIRSetToReconcile(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
        \*                                                 /\ NIBIRStatus[x] \notin {IR_DONE, IR_NONE, IR_SUSPEND}}
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                                     /\ NIBIRStatus[x] \notin {IR_NONE}}
        \* getIRSetToSuspend(CID, SID) == {x \in SetScheduledIRs[SID]: NIBIRStatus[x] = IR_NONE}           
                                                                             
        \*************************** Monitoring Server **********************
        getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                                \/ /\ irType = DELETED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = DELETE_FLOW
                                                                             /\ irTypeMapping[x].flow = flowID
        getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID
        \*************************** Watchdog *******************************
        returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                                   /\ controllerSubmoduleFailStat[x] = Failed}
                                                                                                                                                                          
        (***************** SystemWide Check **********************************)        
        isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE
                                                                                                                
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
    
    \* ======= Complete Failure ========
    macro completeFailure()
    begin
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusMsg := [type |-> NIC_ASIC_DOWN, 
                            swID |-> self[2],
                            num |-> controlMsgCounter[self[2]]];
            swSeqChangedStatus := Append(swSeqChangedStatus, statusMsg);
        end if;
        
        switchStatus[self[2]] := [cpu |-> Failed, nicAsic |-> Failed, 
                                    ofa |-> Failed, installer |-> Failed];
        NicAsic2OfaBuff[self[2]] := <<>>; 
        Ofa2NicAsicBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        TCAM[self[2]] := <<>>;
        controller2Switch[self[2]] := <<>>;    
    end macro;
    \* =================================
    
    \* == Resolving Complete Failure ===
    macro resolveCompleteFailure()
    begin
        assert switchStatus[self[2]].cpu = Failed;
        assert switchStatus[self[2]].nicAsic = Failed;
        assert switchStatus[self[2]].ofa = Failed;
        assert switchStatus[self[2]].installer = Failed;
        
        await nicAsicStartingMode(self[2]);
        await ofaStartingMode(self[2]);
        await installerInStartingMode(self[2]);
        
        switchStatus[self[2]] := [cpu |-> NotFailed, nicAsic |-> NotFailed, 
                                    ofa |-> NotFailed, installer |-> NotFailed];
        NicAsic2OfaBuff[self[2]] := <<>>; 
        Ofa2NicAsicBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        TCAM[self[2]] := <<>>;
        controller2Switch[self[2]] := <<>>;
        
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
        statusResolveMsg := [type |-> KEEP_ALIVE, 
                             swID |-> self[2],
                             num |-> controlMsgCounter[self[2]],
                             status |-> [installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)]];  
        swSeqChangedStatus := Append(swSeqChangedStatus, statusResolveMsg);  
    end macro;
    \* =================================
    
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
\*        await controllerLock = <<NO_LOCK, NO_LOCK>>; 
\*        await switchLock \in {<<NO_LOCK, NO_LOCK>>, self};
        skip;
    end macro;
    \* =================================
    
    \* ===========Acquire Lock==========
    macro acquireLock()
    begin
        \* switch acquires the lock if switchWaitForLock conditions are 
        \* satisfied
\*        switchWaitForLock();
\*        switchLock := self;

        skip;
    end macro;
    \* =================================
    
    
    \* ====== Acquire & Change Lock =====
    macro acquireAndChangeLock(nextLockHolder)
    begin
        \* Using this macro, processes can pass lock to another process        
\*        switchWaitForLock();
\*        switchLock := nextLockHolder;

        skip;
    end macro;
    \* =================================
    
    \* ========= Release Lock ==========
    macro releaseLock(prevLockHolder)
    begin
\*        assert \/ switchLock[2] = prevLockHolder[2]
\*               \/ switchLock[2] = NO_LOCK;
\*        switchLock := <<NO_LOCK, NO_LOCK>>;

        skip;
    end macro;
    \* =================================
    
    \* ========= Is Lock free ==========
    macro controllerWaitForLockFree()
    begin
        \* controller only proceeds when the following two conditions 
        \* are satified;
\*        await controllerLock \in {self, <<NO_LOCK, NO_LOCK>>};
\*        await switchLock = <<NO_LOCK, NO_LOCK>>;
        skip;
    end macro
    \* =================================
    
    \* ========= controller acquire Lock ==========
    macro controllerAcquireLock()
    begin
\*        controllerWaitForLockFree();
\*        controllerLock := self;
        skip;
    end macro    
    \* ============================================
    
    \* ========= controller release Lock ==========
    macro controllerReleaseLock()
    begin
        \* only the controller process itself can release the controller lock. 
\*        controllerWaitForLockFree();
\*        controllerLock := <<NO_LOCK, NO_LOCK>>;
        skip;
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
        assert irTypeMapping[s].type \in {INSTALL_FLOW, DELETE_FLOW};
        assert irTypeMapping[s].flow \in 1..MaxNumFlows;
        controller2Switch[ir2sw[s]] := Append(controller2Switch[ir2sw[s]], [type |-> irTypeMapping[s].type,
                                                                            to |-> ir2sw[s],
                                                                            flow |-> irTypeMapping[s].flow]);
        
        if whichSwitchModel(ir2sw[s]) = SW_COMPLEX_MODEL then 
            switchLock := <<NIC_ASIC_IN, ir2sw[s]>>;
        else
            switchLock := <<SW_SIMPLE_ID, ir2sw[s]>>;
        end if;
    end macro;
    \* =================================
    
    
                  
    (*******************************************************************)
    (*                     NIB   (Macros)                              *)
    (*******************************************************************)
    \* ========= Tagged Buffer ==========
    macro modifiedEnqueue(nextIR)
    begin
        IRQueueNIB := Append(IRQueueNIB, [IR |-> nextIR, tag |-> NO_TAG]);
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
               \*   /\ SwSuspensionStatus[ir2sw[nextIR]] = SW_RUN;
        AddToScheduleIRSet: 
            assert nextIR \notin SetScheduledIRs[self[1]][ir2sw[nextIR]];
            SetScheduledIRs[self[1]][ir2sw[nextIR]] := SetScheduledIRs[self[1]][ir2sw[nextIR]] \cup {nextIR};
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
        await swCanReceivePackets(self[2]);         
        await Len(controller2Switch[self[2]]) > 0;
        switchWaitForLock();
        ingressPkt := Head(controller2Switch[self[2]]);
        assert ingressPkt.type \in {INSTALL_FLOW, DELETE_FLOW};
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        if ingressPkt.type = INSTALL_FLOW then
            installedIRs := Append(installedIRs, ingressPkt.flow);
            TCAM[self[2]] := Append(TCAM[self[2]], ingressPkt.flow);
            switch2Controller := Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                            from |-> self[2],
                                                            flow |-> ingressPkt.flow]);
        else
            if \E i \in DOMAIN TCAM[self[2]]: TCAM[self[2]][i] = ingressPkt.flow then
                TCAM[self[2]] := removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], ingressPkt.flow));
            end if;
            switch2Controller := Append(switch2Controller, [type |-> DELETED_SUCCESSFULLY,
                                                            from |-> self[2],
                                                            flow |-> ingressPkt.flow]); 
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
        SwitchRcvPacket1:
            if swCanReceivePackets(self[2]) then
                ingressIR := Head(controller2Switch[self[2]]);
                assert ingressIR.type \in {INSTALL_FLOW, DELETE_FLOW};
                acquireLock();
                controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
            else
               ingressIR := [type |-> 0];
               goto SwitchRcvPacket;
            end if;
        
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
        SwitchFromOFAPacket1:
            if swCanReceivePackets(self[2]) then
                egressMsg := Head(Ofa2NicAsicBuff[self[2]]);
                acquireLock();
                assert \/ egressMsg.type = INSTALLED_SUCCESSFULLY
                       \/ egressMsg.type = DELETED_SUCCESSFULLY;
                Ofa2NicAsicBuff[self[2]] := Tail(Ofa2NicAsicBuff[self[2]]);
            else
                egressMsg := [type |-> 0];
                goto SwitchFromOFAPacket;
            end if;
        
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
        SwitchOfaProcIn1:
           if swOFACanProcessIRs(self[2]) then
               ofaInMsg := Head(NicAsic2OfaBuff[self[2]]);           
               assert ofaInMsg.to = self[2];
               assert ofaInMsg.flow  \in 1..MaxNumFlows;
               NicAsic2OfaBuff[self[2]] := Tail(NicAsic2OfaBuff[self[2]]);
           else
                ofaInMsg := [type |-> 0];
                goto SwitchOfaProcIn;
           end if;
        
        \* Step 2: append the IR to the installer buffer
        SwitchOfaProcessPacket:
           if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<INSTALLER, self[2]>>);
                if ofaInMsg.type \in {INSTALL_FLOW, DELETE_FLOW} then
                    SwitchOfaProcessPacket1:   
                        if swOFACanProcessIRs(self[2]) then
                            Ofa2InstallerBuff[self[2]] := Append(Ofa2InstallerBuff[self[2]], [type |-> ofaInMsg.type, 
                                                                                      flow |-> ofaInMsg.flow]);
                        else
                             ofaInMsg := [type |-> 0];
                             goto SwitchOfaProcIn;
                        end if;                                                              
                end if;
           else
                ofaInMsg := [type |-> 0];
                goto SwitchOfaProcIn;
           end if;
    end while    
    end process
    
    fair process ofaModuleProcPacketOut \in ({OFA_OUT} \X SW)
    variables ofaOutConfirmation = [type |-> 0, flow |-> 0]
    begin
    SwitchOfaProcOut:
    while TRUE do
    
        \* Step 1: pick the first confirmation from installer
        await swOFACanProcessIRs(self[2]);
        await Installer2OfaBuff[self[2]] # <<>>;
        acquireLock();
        SwitchOfaProcOut1:
            if swOFACanProcessIRs(self[2]) then
                ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
                Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
                assert ofaOutConfirmation.flow \in 1..MaxNumFlows;
                assert ofaOutConfirmation.type \in {INSTALL_FLOW, DELETE_FLOW};
            else
                ofaOutConfirmation := [type |-> 0, flow |-> 0];
                goto SwitchOfaProcOut;
            end if;
        \* Step 2: prepare an installation confirmation message and send it to the controller
        \* through the NIC/ASIC
        SendInstallationConfirmation:
            if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                if ofaOutConfirmation.type = INSTALL_FLOW then
                    SendInstallationConfirmation1:        
                        if swOFACanProcessIRs(self[2]) then
                            Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                                  from |-> self[2],
                                                                                  flow |-> ofaOutConfirmation.flow]);
                        else
                            ofaOutConfirmation := [type |-> 0, flow |-> 0];
                            goto SwitchOfaProcOut;
                        end if;
                else
                    SendInstallationConfirmation2:    
                        if swOFACanProcessIRs(self[2]) then
                            Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], [type |-> DELETED_SUCCESSFULLY,
                                                                                  from |-> self[2],
                                                                                  flow |-> ofaOutConfirmation.flow]);
                        else
                            ofaOutConfirmation := [type |-> 0, flow |-> 0];
                            goto SwitchOfaProcOut;
                        end if;
                end if;
                \* OfaCacheInstalled[self[2]] := OfaCacheInstalled[self[2]] \cup {ofaOutConfirmation};                
            else 
                ofaOutConfirmation := [type |-> 0, flow |-> 0];
                goto SwitchOfaProcOut;
            end if;                                                              
    end while;                                                                      
    end process
    \* =================================
    
    \* ======= Installer Module ========
    \* installer only has one process that installs the IR and sends back the feedback to the OFC
    fair process installerModuleProc \in ({INSTALLER} \X SW)
    variables installerInIR = [type |-> 0, flow |-> 0]
    begin
    SwitchInstallerProc: 
    while TRUE do
       
       \* Step 1: pick the first instruction from the input buffer      
       await swCanInstallIRs(self[2]);
       await Len(Ofa2InstallerBuff[self[2]]) > 0;
       acquireLock();
       SwitchInstallerProc1:
            if swCanInstallIRs(self[2]) then
                installerInIR := Head(Ofa2InstallerBuff[self[2]]);
                assert installerInIR.flow \in 1..MaxNumFlows;
                assert installerInIR.type \in {INSTALL_FLOW, DELETE_FLOW};
                Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);
            else
                installerInIR := [type |-> 0, flow |-> 0];
                goto SwitchInstallerProc;
            end if;
               
       \* Step 2: install the IR to the TCAM
       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then
                acquireLock();
                if installerInIR.type = INSTALL_FLOW then    
                    SwitchInstallerInsert2TCAM1:
                        if swCanInstallIRs(self[2]) then
                            installedIRs := Append(installedIRs, installerInIR.flow);
                            TCAM[self[2]] := Append(TCAM[self[2]], installerInIR.flow);
                        else
                            installerInIR := [type |-> 0, flow |-> 0];
                            goto SwitchInstallerProc;                        
                        end if;
                else
                    SwitchInstallerInsert2TCAM2:
                        if swCanInstallIRs(self[2]) then    
                            if \E i \in DOMAIN TCAM[self[2]]: TCAM[self[2]][i] = installerInIR.flow then
                                SwitchInstallerInsert2TCAM3:                        
                                    if swCanInstallIRs(self[2]) then
                                        TCAM[self[2]] := removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], installerInIR.flow));
                                    else
                                        installerInIR := [type |-> 0, flow |-> 0];
                                        goto SwitchInstallerProc;
                                    end if;
                            end if;
                        else
                            installerInIR := [type |-> 0, flow |-> 0];
                            goto SwitchInstallerProc;                        
                        end if;
                        
                end if; 
            else
                installerInIR := [type |-> 0, flow |-> 0];
                goto SwitchInstallerProc;
            end if;
            
       \* Step 3: send the confirmation to the OFA
       SwitchInstallerSendConfirmation:
            if swCanInstallIRs(self[2]) then
                acquireAndChangeLock(<<OFA_OUT, self[2]>>);
                Installer2OfaBuff[self[2]] := Append(Installer2OfaBuff[self[2]], installerInIR);
            else
                installerInIR := [type |-> 0, flow |-> 0];
                goto SwitchInstallerProc;
            end if;
    end while;
    end process
    \* =================================
    
    \* ======= Failure Proccess=========
    fair process swFailureProc \in ({SW_FAILURE_PROC} \X SW)
    variable statusMsg = <<>>, notFailedSet = {}, failedElem = "", obj = [type |-> 0];
    begin
    SwitchFailure:
    while TRUE do
        
        \* proceed only if 
        \* I. there is an element to fail
        \* II. the system has not finished installing all the IRs
        \* III. either lock is for its switch or no one has the lock
        \* IV. there is no difference if switch fails after the corresponding IR is in IR_DONE mode
        \* V. switches fail according to the order of sw_fail_ordering_var (input), so
        \*    this switch should be at the head of failure ordering sequence.  
        \*await ~isFinished;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                 \/ switchLock[2] = self[2];
        \*await \E x \in getSetIRsForSwitch(self[2]): NIBIRStatus[x] # IR_DONE;
        await sw_fail_ordering_var # <<>>;
        await \E x \in Head(sw_fail_ordering_var): x.sw = self[2];
        obj := CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2];
        RecoveryStatus[self[2]].transient := obj.transient || RecoveryStatus[self[2]].partial := obj.partial;
        removeFromSeqSet(sw_fail_ordering_var, obj);
        
        
        await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
        
        if obj.partial = 0 then \* Complete Failure
            completeFailure();
            
        else \* Partial Failure
            \* retrieves all the possible elements to fail and creates a branch in each of which
            \* one the modules fail 
            notFailedSet := returnSwitchElementsNotFailed(self[2]);
            await notFailedSet # {};
         
            \* for each element a branch is created in each of which one of them fails.
            with elem \in notFailedSet do
                failedElem := elem;
            end with;
        
            if failedElem = "cpu" then
                cpuFailure();
            elsif failedElem = "ofa" then
                ofaFailure();
            elsif failedElem = "installer" then
                installerFailure();
            elsif failedElem = "nicAsic" then 
                nicAsicFailure();
            else assert FALSE;
            end if;
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
        await RecoveryStatus[self[2]].transient = 1;
        \*await ~isFinished;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ switchLock = <<NO_LOCK, NO_LOCK>>;
              
        if RecoveryStatus[self[2]].partial = 0 then
            resolveCompleteFailure();
        else
            failedSet := returnSwitchFailedElements(self[2]);
            await Cardinality(failedSet) > 0;
            with elem \in failedSet do
                recoveredElem := elem;
            end with;
        
            if recoveredElem = "cpu" then resolveCpuFailure();
            elsif recoveredElem = "nicAsic" then resolveNicAsicFailure();
            elsif recoveredElem = "ofa" then resolveOfaFailure();
            elsif recoveredElem = "installer" then resolveInstallerFailure();
            else assert FALSE;
            end if;
        
        end if;
        
        RecoveryStatus[self[2]] := [transient |-> 0, partial |-> 0];
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
    \* ===== RC NIB event handler =====
    fair process rcNibEventHandler \in ({rc0} \X {NIB_EVENT_HANDLER})
    variables event = [type |-> 0];
    begin
    RCSNIBEventHndlerProc:
    while TRUE do
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await RCNIBEventQueue[self[1]] # <<>>;
        controllerWaitForLockFree();
        rcReadEvent: event := Head(RCNIBEventQueue[self[1]]);
        assert event.type \in {TOPO_MOD, IR_MOD};
        rcCheckType: if (event.type = TOPO_MOD) then
            rcTopoModEvent: if RCSwSuspensionStatus[self[1]][event.sw] # event.state then    
                rcSwSuspend: RCSwSuspensionStatus[self[1]][event.sw] := event.state;
                rcTEEventQue: TEEventQueue[self[1]] := Append(TEEventQueue[self[1]], event);
            end if;
        elsif (event.type = IR_MOD) then
            rcIRModEvent: if RCIRStatus[self[1]][event.IR] # event.state then
                rcIRStatus: RCIRStatus[self[1]][event.IR] := event.state;
                rcCheckIRStatus: if event.state \in {IR_SENT, IR_NONE, IR_DONE} then
                    \* remove the IR from setscheduledIRs
                    rcChangeIRStatus: SetScheduledIRs[ir2sw[event.IR]] := SetScheduledIRs[ir2sw[event.IR]]\{event.IR};    
                end if;
            end if;
        end if;
        rcRemoveEvent: RCNIBEventQueue[self[1]] := Tail(RCNIBEventQueue[self[1]]);
    end while;
    end process
    \* =================================
    
    \* ============ TE =================
    fair process controllerTrafficEngineering \in ({rc0} \X {CONT_TE})
    variables topoChangeEvent = [type |-> 0], currSetDownSw = {}, prev_dag_id = 0, init = 1,
        nxtDAG = [type |-> 0], setRemovableIRs = {}, currIR = 0, currIRInDAG = 0,
        nxtDAGVertices = {}, setIRsInDAG = {}, prev_dag = [e |-> {}, v |-> {}];
    begin
    ControllerTEProc:
    while TRUE do
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await init = 1 \/ TEEventQueue[self[1]] # <<>>;
        controllerAcquireLock();
        
        ControllerTEEventProcessing:
            while TEEventQueue[self[1]] # <<>> do 
                controllerWaitForLockFree();
                ReadHeadTEEvent: topoChangeEvent := Head(TEEventQueue[self[1]]);
                assert topoChangeEvent.type \in {TOPO_MOD};
                ComputeTopoUpdates:
                if topoChangeEvent.state = SW_SUSPEND then
                    currSetDownSw := currSetDownSw \cup {topoChangeEvent.sw};
                else
                    currSetDownSw := currSetDownSw \ {topoChangeEvent.sw};
                end if; 
                RemoveFromTEEventQueue: TEEventQueue[self[1]] := Tail(TEEventQueue[self[1]]);
            end while;
            controllerReleaseLock();
        
        ControllerTEComputeDagBasedOnTopo:
            controllerWaitForLockFree();
            DAGID := (DAGID % MaxDAGID) + 1;
            nxtDAG := [id |-> DAGID, dag |-> TOPO_DAG_MAPPING[currSetDownSw]];
            if prev_dag = nxtDAG.dag then
                goto ControllerTEProc;
            else
                nxtDAGVertices := nxtDAG.dag.v;
                if init = 0 then
                    ControllerUpdateDAGState:
                        DAGState[prev_dag_id] := DAG_STALE;
                
                    ControllerTESendDagStaleNotif:
                        controllerWaitForLockFree();
                        DAGEventQueue[self[1]] := Append(DAGEventQueue[self[1]], [type |-> DAG_STALE, id |-> prev_dag_id]);
                
                    ControllerTEWaitForStaleDAGToBeRemoved:
                        controllerWaitForLockFree();
                        await DAGState[prev_dag_id] = DAG_NONE;
                        prev_dag_id := DAGID;
                        prev_dag := nxtDAG.dag;
                        setRemovableIRs := getSetRemovableIRs(self[1], SW \ currSetDownSw, nxtDAGVertices);
                else
                    init := 0;
                    prev_dag_id := DAGID;
                end if;
            end if;
            
        ControllerTERemoveUnnecessaryIRs:
            while setRemovableIRs # {} do
                controllerAcquireLock();
                ControllerTEChooseOneIR:
                    currIR := CHOOSE x \in setRemovableIRs: TRUE;
                    setRemovableIRs := setRemovableIRs \ {currIR};
                
                \* adjust data structures
                ControllerTEAdjustRCState:
                    RCIRStatus[self[1]] := RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE);
                ControllerTEAdjustNIBIRStatusState:
                    NIBIRStatus := NIBIRStatus @@ (nxtRCIRID :> IR_NONE);
                    FirstInstall := FirstInstall @@ (nxtRCIRID :> 0);
                ControllerTEIRMapping:
                    irTypeMapping := irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIR]]);
                    ir2sw := ir2sw @@ (nxtRCIRID :> ir2sw[currIR]);
                ControllerTEIRAddNodesDAG:
                    nxtDAG.dag.v := nxtDAG.dag.v \cup {nxtRCIRID};
                ControllerTEGetIrsInDAG:
                    setIRsInDAG := getSetIRsForSwitchInDAG(ir2sw[currIR], nxtDAGVertices); 
                        
                ControllerTEAddEdge:
                    while setIRsInDAG # {} do
                        controllerAcquireLock();
                        currIRInDAG := CHOOSE x \in setIRsInDAG: TRUE;
                        setIRsInDAG := setIRsInDAG \ {currIRInDAG};
                        nxtDAG.dag.e := nxtDAG.dag.e \cup {<<nxtRCIRID, currIRInDAG>>};
                    end while;
                    nxtRCIRID := nxtRCIRID + 1;                
                    controllerAcquireLock();
            end while;
            controllerReleaseLock();
            ControllerTEUpdateSetScheduledIR:
                SetScheduledIRs := [x \in SW |-> (SetScheduledIRs[x] \ nxtDAG.dag.v)];
            
        ControllerTESubmitNewDAG:
            controllerWaitForLockFree();
            DAGState[nxtDAG.id] := DAG_SUBMIT;
        ControllerTEAddToDAGQueue:
            DAGEventQueue[self[1]] := Append(DAGEventQueue[self[1]], [type |-> DAG_NEW, dag_obj |-> nxtDAG]);      
    
    end while;
    end process
    \* =================================
    
    \* ========= Boss Sequencer ========
    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
    variables seqEvent = [type |-> 0], worker = 0;
    begin
    ControllerBossSeqProc:
    while TRUE do
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await DAGEventQueue[self[1]] # <<>>;
    
        controllerWaitForLockFree();
        ControllerBossDAGHead:
            seqEvent := Head(DAGEventQueue[self[1]]);
            DAGEventQueue[self[1]] := Tail(DAGEventQueue[self[1]]);
        assert seqEvent.type \in {DAG_NEW, DAG_STALE};
        ControllerBossCheckEventType:
            if seqEvent.type = DAG_NEW then
                ControllerBossDAGSend: DAGQueue[self[1]] := Append(DAGQueue[self[1]], seqEvent.dag_obj);
            else
                ControllerBossDAGTerminate:
                    worker := idWorkerWorkingOnDAG[seqEvent.id];
                    ControllerBossIfDAGUnlock:
                        if worker # DAG_UNLOCK then
                            ControllerBossSendSignal:
                                RCSeqWorkerStatus[CONT_WORKER_SEQ] := SEQ_WORKER_STALE_SIGNAL;
                            WaitForRCSeqWorkerTerminate:
                                controllerWaitForLockFree();
                                await idWorkerWorkingOnDAG[seqEvent.id] = DAG_UNLOCK;
                            ControllerBossChangeDAGState:
                                DAGState[seqEvent.id] := DAG_NONE;
                        else
                            ControllerBossChangeDAGStateToNone:
                                DAGState[seqEvent.id] := DAG_NONE;
                        end if;
            end if;
    end while;
    end process
    \* =================================
    
    \* ======== Worker Sequencers =======
    \* Sequencer periodically gets all the valid IRs (those with satisfied
    \* dependencies), run its scheduling mechanism to decide the order of
    \* scheduling and then, schedule the IR
    fair process controllerSequencer \in ({rc0} \X {CONT_WORKER_SEQ})
    variables toBeScheduledIRs = {}, nextIR = 0, stepOfFailure = 0, currDAG = [dag |-> 0], IRSet = {};
    begin
    ControllerWorkerSeqProc:
    while TRUE do
        \* ControlSeqProc consists of one operation;
        \* 1) Retrieving the set of valid IRs
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await DAGQueue[self[1]] # <<>>;
        controllerWaitForLockFree();
        ControllerWorkerSeq1: currDAG := Head(DAGQueue[self[1]]);
        ControllerWorkerSeq2: idWorkerWorkingOnDAG[currDAG.id] := self[2];
        
        ControllerWorkerSeqScheduleDAG:
            while ~allIRsInDAGInstalled(self[1], currDAG.dag) /\ ~isDAGStale(currDAG.id) do
                controllerWaitForLockFree();
                ControllerWorkerSeq3:
                    toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1], currDAG.dag);
                    await isDAGStale(currDAG.id) \/ toBeScheduledIRs # {};
                    if isDAGStale(currDAG.id) then
                        goto ControllerWorkerSeqScheduleDAG;
                    end if;
                    
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
                                SetScheduledIRs[ir2sw[nextIR]] := SetScheduledIRs[ir2sw[nextIR]] \cup {nextIR};                    
                            end if;
                        end if;
                    end if;
            
                    if (stepOfFailure # 0) then    
                        controllerModuleFails();
                        goto ControllerSeqStateReconciliation; 
                    end if;  
                    
                    AddDeleteIRIRDoneSet:      
                        controllerWaitForLockFree();
                        if irTypeMapping[nextIR].type = INSTALL_FLOW then
                            IRDoneSet[self[1]] := IRDoneSet[self[1]] \cup {nextIR};
                        else
                            IRDoneSet[self[1]] := IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
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
                            modifiedEnqueue(nextIR);
                            toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                            if (stepOfFailure # 2) then
                                \* step 2: clear the state on NIB  
                                controllerStateNIB[self] := [type |-> NO_STATUS];    
                            end if;
                        end if;
                
                        if (stepOfFailure # 0) then    
                            controllerModuleFails();
                            goto ControllerSeqStateReconciliation;
                        elsif toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then \* where while ends *\
                            goto ControllerWorkerSeqScheduleDAG;
                        end if;
                        
                end while;                                                
            end while;
            \* Remove DAG from the DAG Queue
            controllerAcquireLock();
            idWorkerWorkingOnDAG[currDAG.id] := DAG_UNLOCK;
            RCSeqWorkerStatus[self[2]] := SEQ_WORKER_RUN;
            IRSet := currDAG.dag.v;
            
            AddDeleteDAGIRDoneSet:
                while IRSet # {} /\ allIRsInDAGInstalled(self[1], currDAG.dag) do
                    controllerWaitForLockFree();
                    nextIR := CHOOSE x \in IRSet: TRUE;
                    if irTypeMapping[nextIR].type = INSTALL_FLOW then
                        IRDoneSet[self[1]] := IRDoneSet[self[1]] \cup {nextIR};
                    else
                        IRDoneSet[self[1]] := IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
                    end if;
                    IRSet := IRSet \ {nextIR};
                end while; 
                controllerReleaseLock();
                DAGQueue[self[1]] := Tail(DAGQueue[self[1]]);
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
        controllerReleaseLock();
        if(controllerStateNIB[self].type = STATUS_START_SCHEDULING) then
            SetScheduledIRs[ir2sw[controllerStateNIB[self].next]] := 
                        SetScheduledIRs[ir2sw[controllerStateNIB[self].next]]\{controllerStateNIB[self].next};
        end if;
        goto ControllerWorkerSeqProc;
    end process
    \* ==========================
    
    \* ====== IR Monitor =======
    fair process rcIRMonitor \in ({rc0} \X {CONT_MONITOR})
    variable currIRMon = 0;
    begin
    controllerIRMonitor:
    while TRUE do
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        controllerWaitForLockFree();
        rcIRMonitor1:
           await setIRMonitorShouldSchedule(self[1]) # {};
           currIRMon := CHOOSE x \in setIRMonitorShouldSchedule(self[1]): TRUE;
        rcIRMonitor2:
            if currIRMon \in IRDoneSet[self[1]] then 
                rcIRMonitor3: SetScheduledIRs[ir2sw[currIRMon]] := SetScheduledIRs[ir2sw[currIRMon]] \cup {currIRMon};
                rcIRMonitor4: modifiedEnqueue(currIRMon);
            else
            
                \* adjust data structures
                rcIRMonitor5: RCIRStatus[self[1]] := RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE);
                rcIRMonitor6:
                    NIBIRStatus := NIBIRStatus @@ (nxtRCIRID :> IR_NONE);
                    FirstInstall := FirstInstall @@ (nxtRCIRID :> 0);
                rcIRMonitor7:
                    irTypeMapping := irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIRMon]]);
                    ir2sw := ir2sw @@ (nxtRCIRID :> ir2sw[currIRMon]);
                rcIRMonitor8:
                    SetScheduledIRs[ir2sw[nxtRCIRID]] := SetScheduledIRs[ir2sw[nxtRCIRID]] \cup {nxtRCIRID};
                rcIRMonitor9:
                    modifiedEnqueue(nxtRCIRID);
                    nxtRCIRID := nxtRCIRID + 1;   
            end if;
    end while
    end process
    \* ========================== 
    
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
        ControllerThread1:        
            await existIRIndexToRead(self);
            await IRQueueNIB # <<>>;
            modifiedRead();
 
        whichStepToFail(2);
        if (stepOfFailure = 1) then
            \* Failed before Step 1
            controllerModuleFails();
            goto ControllerThreadStateReconciliation;
        else 
            \* Step 2: Worker Thread save state to NIB
            ControllerThread2: controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent];
            if (stepOfFailure = 2) then
                \* Failed before Step 2
                controllerModuleFails();
                goto ControllerThreadStateReconciliation;
            else    
                \* Step 3: try to lock the IR and if it's already lock do ControllerThreadWaitForIRUnlock Operation.
                \***** Step 3.1: lock the semaphore using CAS operation 
                ControllerThread3:
                    if idThreadWorkingOnIR[nextIRToSent] = IR_UNLOCK then
\*                        await threadWithLowerIDGetsTheLock(self[1], self, nextIRToSent, IRQueueNIB); \* For Reducing Space
                        idThreadWorkingOnIR[nextIRToSent] := self[2]
                    else
                        ControllerThreadWaitForIRUnlock: 
                            controllerWaitForLockFree();
                            await idThreadWorkingOnIR[nextIRToSent] = IR_UNLOCK;
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
                if ~isSwitchSuspended(ir2sw[nextIRToSent]) /\ NIBIRStatus[nextIRToSent] = IR_NONE then
                    \**** Step 1.1: change the status of the switch to IR_SENT before actually sending
                    \**** the IR (Update-before-Action) 
                    ControllerThreadSendIR1:
                        NIBIRStatus[nextIRToSent] := IR_SENT;
                        RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> nextIRToSent, state |-> IR_SENT]); 
                    \* ControllerThreadForwardIR consists of 2 operations;
                    \* 1. Forwarding the IR to the switch
                    \* 2. Updating the state on db to SENT_DONE
                    \* Worker may fail between these operations
                    ControllerThreadForwardIR:
                        controllerWaitForLockFree();
\*                        whichStepToFail(2);
\*                        if (stepOfFailure # 1) then
                            \* Step 1: forward the IR
                            controllerSendIR(nextIRToSent);
\*                            if (stepOfFailure # 2) then
                               \* Step 2: save the state on NIB
                               ControllerThreadForwardIR1: controllerStateNIB[self] := [type |-> STATUS_SENT_DONE, next |-> nextIRToSent];
\*                            end if;
\*                        end if;                          
\*                        if (stepOfFailure # 0) then
\*                            controllerModuleFails();
\*                            goto ControllerThreadStateReconciliation;
\*                        end if;
                end if;
            else
                \* Failed even before begining of this operation
                goto ControllerThreadStateReconciliation;
            end if;
            
        \* Operations in the next two labels are for performance reasons
        \* since we have already dedicated this worker to a IR, if the switch
        \* is in suspended mode, worker waits for it to be recovered and then, 
        \* does the fast recovery by immediately starting to send the IR
        \*WaitForIRToHaveCorrectStatus:  
        \*    controllerWaitForLockFree();
        \*    controllerModuleFailOrNot();
        \*    if (controllerSubmoduleFailStat[self] = NotFailed) then 
        \*        await ~isSwitchSuspended(ir2sw[nextIRToSent]);
        \*    else
        \*        goto ControllerThreadStateReconciliation;
        \*    end if;
            
        \*ReScheduleifIRNone:
        \*    controllerWaitForLockFree();
        \*    controllerModuleFailOrNot();
        \*    if (controllerSubmoduleFailStat[self] = NotFailed) then
        \*        if IRStatus[nextIRToSent] = IR_NONE then
        \*            controllerStateNIB[self] := [type |-> STATUS_LOCKING, next |-> nextIRToSent]; 
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
                if idThreadWorkingOnIR[nextIRToSent] = self[2] then
                    ControllerThreadUnlockSemaphore1: idThreadWorkingOnIR[nextIRToSent] := IR_UNLOCK;
                end if;
            else
                goto ControllerThreadStateReconciliation;
            end if;
            
        \* RemoveFromScheduledIRSet consists of three operations;
        \* 1. Clear the state on db
        \* 2. Remove the IR from the tagged buffer in NIB (Lazy removel strategy) 
        \* Worker may fail between any of these Ops
        RemoveFromScheduledIRSet:
            controllerWaitForLockFree();
\*            whichStepToFail(2);
\*            if (stepOfFailure # 1) then 
                \* Step 1: clear the state on NIB
                controllerStateNIB[self] := [type |-> NO_STATUS];
\*                if (stepOfFailure # 2) then
                    \* Step 3: remove from IRQueue
                    RemoveFromScheduledIRSet1: modifiedRemove();
\*                end if;
\*            end if;
            
\*            if (stepOfFailure # 0) then
\*                controllerModuleFails();
\*                goto ControllerThreadStateReconciliation;
\*            end if;
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
        controllerReleaseLock();
        if (controllerStateNIB[self].type = STATUS_LOCKING) then
            if (NIBIRStatus[controllerStateNIB[self].next] = IR_SENT) then
                    NIBIRStatus[controllerStateNIB[self].next] := IR_NONE;
            end if;                 
            if (idThreadWorkingOnIR[controllerStateNIB[self].next] = self[2]) then
                idThreadWorkingOnIR[controllerStateNIB[self].next] := IR_UNLOCK;
            end if;        
        elsif (controllerStateNIB[self].type = STATUS_SENT_DONE) then
            \*SetScheduledIRs[ir2sw[controllerStateNIB[self].next]] := 
            \*        SetScheduledIRs[ir2sw[controllerStateNIB[self].next]] \cup {controllerStateNIB[self].next};          
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
         controllerAcquireLock();
         
         \* Controller event handler process consists of two operations;
         \* 1. Picking the first event from the event queue
         \* 2. Check whether the event is a switch failure or a switch recovery
         ControllerEventHandlerProc1: monitoringEvent := Head(swSeqChangedStatus);
         ControllerEventHandlerProc2:
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
                    ControllerSuspendSW1: RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
                                                                            sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]);        
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
                
         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            \*call suspendInSchedulingIRs(monitoringEvent.swID);
            
            \* ControllerCheckIfThisIsLastEvent consists of 3 operations;
            \* 1. Check if this is the last event for the corresponding sw (if it is not, then, maybe the switch
            \*      has failed again and resetting the IRs is not necessary). Note that we have to process the 
            \*      event and change the status of SW anyway. Otherwise, it may result in discarding the subsequent
            \*      events (one of the failures!!!!)   
            \* 2. GetIRsToBeChecked 
            \* 3. ResetAllIRs
            ControllerCheckIfThisIsLastEvent:
                controllerReleaseLock();
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
                                    \*goto ControllerEvenHanlderRemoveEventFromQueue;
                                    goto ControllerFreeSuspendedSW;
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
                                    ResetAllIRs1: setIRsToReset := setIRsToReset \ {resetIR};
                                    
                                    \* the following operation (if -- end if;) should be done atomically
                                    \* using CAS operation
                                    \*if NIBIRStatus[resetIR] # IR_DONE then
                                        ResetAllIRs2:
                                            NIBIRStatus[resetIR] := IR_NONE;
                                            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], 
                                                                        [type |-> IR_MOD, IR |-> resetIR, state |-> IR_NONE]);
                                    \*end if;
                                    
                                    if setIRsToReset = {} then \* End of while *\
                                        \*goto ControllerEvenHanlderRemoveEventFromQueue;
                                        goto ControllerFreeSuspendedSW;
                                    end if;
                                else
                                    goto ControllerEventHandlerStateReconciliation;
                                end if;
                            end while;
                    end if;
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
            \* ControllerFreeSuspendedSW consists of three operations; 
            \* 1. Save on db that it is going to reset the IRs
            \* 2. Change the SW status to SW_RUN (so all the corresponding IRs going to be scheduled immediately)
            \* (event handler may fail between any of these Ops.)
            ControllerFreeSuspendedSW: 
                controllerAcquireLock();
\*                whichStepToFail(2);
\*                if (stepOfFailure # 1) then 
                    \* Step 1: save state on NIB
                    controllerStateNIB[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
\*                    if (stepOfFailure # 2) then
                        \* Step 2: change switch status to SW_RUN
                        ControllerFreeSuspendedSW1:
                            SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
                                                                                sw |-> monitoringEvent.swID, state |-> SW_RUN]);  
\*                    end if;
\*                end if;
                
\*                if (stepOfFailure # 0) then
\*                    controllerModuleFails();
\*                    goto ControllerEventHandlerStateReconciliation;
\*                end if;
         end if;
         
         \* ControllerEventHandlerRemoveEventFromQueue consists of 2 operations;
         \* 1. Clear the state on db
         \* 2. Remove the event from queue (Lazy removal procedure)
         \* event handler may fail between these Ops. 
         ControllerEvenHanlderRemoveEventFromQueue:
            controllerReleaseLock();
\*            whichStepToFail(2);
\*            if (stepOfFailure # 1) then 
                \* Step 1: clear state on NIB
                controllerStateNIB[self] := [type |-> NO_STATUS]; 
\*                if (stepOfFailure # 2) then
                    \* Step 2: remove from event queue
                    ControllerEvenHanlderRemoveEventFromQueue1: swSeqChangedStatus := Tail(swSeqChangedStatus);
\*                end if;
\*            end if;
            
\*            if (stepOfFailure # 0) then
\*                controllerModuleFails();
\*                goto ControllerEventHandlerStateReconciliation;
\*            end if;
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
         controllerReleaseLock();
         if (controllerStateNIB[self].type = START_RESET_IR) then
            SwSuspensionStatus[controllerStateNIB[self].sw] := SW_SUSPEND;
            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
                                                                    sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]);
         end if;
        goto ControllerEventHandlerProc;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    \* monitroing server does not need a reconciliation phase. 
    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable msg = [type |-> 0], irID = 0, removedIR = 0;
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
        \* controllerReleaseLock(); \* commented for optimization
        controllerAcquireLock();
        ControllerMonitorCheckIfMastr1: msg := Head(switch2Controller);
        assert msg.flow \in 1..MaxNumFlows;
        assert msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY};
        ControllerMonitorCheckIfMastr2: irID := getIRIDForFlow(msg.flow, msg.type);
        assert msg.from = ir2sw[irID];
        
        ControllerMonitorCheckIfMastr3: if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            \* If msg type is INSTALLED_SUCCESSFULLY, we have to change the IR status
            \* to IR_DONE. 
            ControllerUpdateIRDone:
                controllerWaitForLockFree(); 
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    FirstInstall[irID] := 1;
                    ControllerUpdateIRDone1:
                    if NIBIRStatus[irID] = IR_SENT then \* Should be done in one atomic operation using CAS 
                            NIBIRStatus[irID] := IR_DONE; 
                            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]);
                    end if;
                    
                    ControllerUpdateIRDone2:
                    if msg.type = DELETED_SUCCESSFULLY then 
                        ControllerUpdateIRDone3: removedIR := getRemovedIRID(msg.flow);
                        ControllerMonUpdateIRNone:
                            controllerWaitForLockFree(); 
                            controllerModuleFailOrNot();
                            NIBIRStatus[removedIR] := IR_NONE; 
                            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]);
                    end if;
                else
                    goto ControllerMonitorCheckIfMastr;
                end if;
        end if;
        
        \*end if;
        
        \* MonitoringServerRemoveFromQueue lazily removes the msg from queue. 
        MonitoringServerRemoveFromQueue: 
            \*controllerWaitForLockFree(); \* Commented for optimization
            controllerReleaseLock(); \* for optimization as we are not modeling OFC partial transient failure
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1f8f2c4c79611c3d669c9d57bdd1d35e
\* Process variable stepOfFailure of process controllerSequencer at line 1754 col 50 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 1924 col 64 changed to stepOfFailure_c
VARIABLES switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
          ContProcSet, SwProcSet, irTypeMapping, ir2sw, swSeqChangedStatus, 
          controller2Switch, switch2Controller, switchStatus, installedIRs, 
          NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
          Ofa2InstallerBuff, TCAM, controlMsgCounter, RecoveryStatus, 
          controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
          switchOrdering, TEEventQueue, DAGEventQueue, DAGQueue, DAGID, 
          MaxDAGID, DAGState, RCNIBEventQueue, RCIRStatus, 
          RCSwSuspensionStatus, nxtRCIRID, idWorkerWorkingOnDAG, 
          RCSeqWorkerStatus, IRDoneSet, idThreadWorkingOnIR, 
          workerThreadRanking, masterState, controllerStateNIB, NIBIRStatus, 
          SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, pc

(* define statement *)
max(set) == CHOOSE x \in set: \A y \in set: x \geq y
min(set) == CHOOSE x \in set: \A y \in set: x \leq y
rangeSeq(seq) == {seq[i]: i \in DOMAIN seq}
indexInSeq(seq, val) == CHOOSE i \in DOMAIN seq: seq[i] = val
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



listDownSwitches(swList) == {sw \in swList: \/ switchStatus[sw].cpu = Failed
                                \/ switchStatus[sw].ofa = Failed
                                \/ switchStatus[sw].installer = Failed
                                \/ switchStatus[sw].nicAsic = Failed}


whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID]

swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed


swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed

swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed


returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                                                     /\ \/ /\ WHICH_SWITCH_MODEL[x] = SW_COMPLEX_MODEL
                                                                           /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1
                                                                        \/ /\ WHICH_SWITCH_MODEL[x] = SW_SIMPLE_MODEL
                                                                           /\ x = "nicAsic"}

getSetIRsForSwitch(SID) == {x \in 1..MaxNumIRs: ir2sw[x] = SID}


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
existIRIndexToRead(threadID) == \E x \in DOMAIN IRQueueNIB: \/ IRQueueNIB[x].tag = threadID
                                                            \/ /\ NoEntryTaggedWith(threadID)
                                                               /\ FirstUntaggedEntry(threadID, x)
                                                               /\ IRQueueNIB[x].tag = NO_TAG
getFirstIndexWith(RID, threadID) == CHOOSE x \in DOMAIN IRQueueNIB: /\ IRQueueNIB[x].tag = threadID
                                                                    /\ IRQueueNIB[x].IR = RID



getSetRemovableIRs(CID, swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ RCIRStatus[CID][x] # IR_NONE
                                                                   \/ x \in SetScheduledIRs[ir2sw[x]]
                                                                /\ x \notin nxtDAGV
                                                                /\ ir2sw[x] \in swSet}
getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: ir2sw[x] = swID}


isDependencySatisfied(CID, DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                        /\ RCIRStatus[CID][y] # IR_DONE
getSetIRsCanBeScheduledNext(CID, DAG)  == {x \in DAG.v: /\ RCIRStatus[CID][x] = IR_NONE
                                                        /\ isDependencySatisfied(CID, DAG, x)
                                                        /\ RCSwSuspensionStatus[CID][ir2sw[x]] = SW_RUN
                                                        /\ x \notin SetScheduledIRs[ir2sw[x]]}
allIRsInDAGInstalled(CID, DAG) == ~\E y \in DAG.v: RCIRStatus[CID][y] # IR_DONE
isDAGStale(id) == DAGState[id] # DAG_SUBMIT


existIRInSetScheduledIRs(CID, swID, type, flowID) == \E x \in SetScheduledIRs[swID]: /\ irTypeMapping[x].type = type
                                                                                     /\ ir2sw[x] = swID
                                                                                     /\ irTypeMapping[x].flow = flowID
existIRDeletionInIRSent(CID, swID, flowID) == \E x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = DELETE_FLOW
                                                                             /\ ir2sw[x] = swID
                                                                             /\ irTypeMapping[x].flow = flowID
                                                                             /\ RCIRStatus[CID][x] = IR_SENT
irMonitorShouldScheduleIR(CID, irID) == \/ /\ irID \in IRDoneSet[CID]
                                           /\ RCIRStatus[CID][irID] = IR_NONE
                                           /\ RCSwSuspensionStatus[CID][IR2SW[irID]] = SW_RUN
                                           /\ ~existIRInSetScheduledIRs(CID, ir2sw[irID], INSTALL_FLOW, irTypeMapping[irID].flow)
                                        \/ /\ irID \in (1..MaxNumIRs) \ IRDoneSet[CID]
                                           /\ RCIRStatus[CID][irID] = IR_DONE
                                           /\ RCSwSuspensionStatus[CID][IR2SW[irID]] = SW_RUN
                                           /\ ~ existIRInSetScheduledIRs(CID, ir2sw[irID], DELETE_FLOW, irTypeMapping[irID].flow)
                                           /\ ~ existIRDeletionInIRSent(CID, ir2sw[irID], irTypeMapping[irID].flow)
setIRMonitorShouldSchedule(CID) == {x \in 1..MaxNumIRs: irMonitorShouldScheduleIR(CID, x)}



isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND



setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(<<CID, y>>)
                                                      /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}
canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                          \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NO_TAG
                                             /\ NoEntryTaggedWith(threadID)
                                             /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
setThreadsAttemptingForLock(CID, nIR, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ y.IR = nIR
                                                                                                                /\ y.tag = <<CID, x>>
                                                                                 /\ pc[<<CID, x>>] = "ControllerThread3"}
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




getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                             /\ NIBIRStatus[x] \notin {IR_NONE}}



getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                        \/ /\ irType = DELETED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = DELETE_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID
getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                             /\ irTypeMapping[x].flow = flowID

returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                           /\ controllerSubmoduleFailStat[x] = Failed}


isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, obj, failedSet, 
          statusResolveMsg, recoveredElem, event, topoChangeEvent, 
          currSetDownSw, prev_dag_id, init, nxtDAG, setRemovableIRs, currIR, 
          currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, 
          worker, toBeScheduledIRs, nextIR, stepOfFailure_, currDAG, IRSet, 
          currIRMon, nextIRToSent, rowIndex, rowRemove, stepOfFailure_c, 
          monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, irID, 
          removedIR, controllerFailedModules

vars == << switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
           ContProcSet, SwProcSet, irTypeMapping, ir2sw, swSeqChangedStatus, 
           controller2Switch, switch2Controller, switchStatus, installedIRs, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
           Ofa2InstallerBuff, TCAM, controlMsgCounter, RecoveryStatus, 
           controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
           switchOrdering, TEEventQueue, DAGEventQueue, DAGQueue, DAGID, 
           MaxDAGID, DAGState, RCNIBEventQueue, RCIRStatus, 
           RCSwSuspensionStatus, nxtRCIRID, idWorkerWorkingOnDAG, 
           RCSeqWorkerStatus, IRDoneSet, idThreadWorkingOnIR, 
           workerThreadRanking, masterState, controllerStateNIB, NIBIRStatus, 
           SwSuspensionStatus, IRQueueNIB, SetScheduledIRs, pc, ingressPkt, 
           ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, installerInIR, 
           statusMsg, notFailedSet, failedElem, obj, failedSet, 
           statusResolveMsg, recoveredElem, event, topoChangeEvent, 
           currSetDownSw, prev_dag_id, init, nxtDAG, setRemovableIRs, currIR, 
           currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, 
           worker, toBeScheduledIRs, nextIR, stepOfFailure_, currDAG, IRSet, 
           currIRMon, nextIRToSent, rowIndex, rowRemove, stepOfFailure_c, 
           monitoringEvent, setIRsToReset, resetIR, stepOfFailure, msg, irID, 
           removedIR, controllerFailedModules >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({rc0} \X {CONT_MONITOR})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR})) \cup (({ofc0, rc0} \X {WATCH_DOG}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..MaxNumIRs |-> 0]
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ ContProcSet = ({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR,
                                       NIB_EVENT_HANDLER, CONT_TE}) \cup
                             ({ofc0} \X {CONT_EVENT, CONT_MONITOR}) \cup
                             ({ofc0} \X CONTROLLER_THREAD_POOL)
        /\ SwProcSet = ((({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW))
                          \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW))
                          \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW))
                          \cup (({SW_RESOLVE_PROC} \X SW)))
        /\ irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]]
        /\ ir2sw = IR2SW
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x\in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ switchStatus = [x \in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed,
                           ofa |-> NotFailed, installer |-> NotFailed]]
        /\ installedIRs = <<>>
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> <<>>]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ switchOrdering = (CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ TEEventQueue = [x \in {rc0} |-> <<>>]
        /\ DAGEventQueue = [x \in {rc0} |-> <<>>]
        /\ DAGQueue = [x \in {rc0} |-> <<>>]
        /\ DAGID = 0
        /\ MaxDAGID = 15
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCNIBEventQueue = [x \in {rc0} |-> <<>>]
        /\ RCIRStatus = [x \in {rc0} |-> [y \in 1..MaxNumIRs |-> IR_NONE]]
        /\ RCSwSuspensionStatus = [x \in {rc0} |-> [y \in SW |-> SW_RUN]]
        /\ nxtRCIRID = MaxNumIRs + 10
        /\ idWorkerWorkingOnDAG = [x \in 1..MaxDAGID |-> DAG_UNLOCK]
        /\ RCSeqWorkerStatus = (CONT_WORKER_SEQ :> SEQ_WORKER_RUN)
        /\ IRDoneSet = [x \in {rc0} |-> {}]
        /\ idThreadWorkingOnIR = [x \in 1..MaxNumIRs |-> IR_UNLOCK] @@ [x \in (MaxNumIRs + 10)..(MaxNumIRs + 20) |-> IR_UNLOCK]
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ masterState = [ofc0 |-> "primary", rc0 |-> "primary"]
        /\ controllerStateNIB = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> IR_NONE]
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
        /\ ofaOutConfirmation = [self \in ({OFA_OUT} \X SW) |-> [type |-> 0, flow |-> 0]]
        (* Process installerModuleProc *)
        /\ installerInIR = [self \in ({INSTALLER} \X SW) |-> [type |-> 0, flow |-> 0]]
        (* Process swFailureProc *)
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> <<>>]
        /\ notFailedSet = [self \in ({SW_FAILURE_PROC} \X SW) |-> {}]
        /\ failedElem = [self \in ({SW_FAILURE_PROC} \X SW) |-> ""]
        /\ obj = [self \in ({SW_FAILURE_PROC} \X SW) |-> [type |-> 0]]
        (* Process swResolveFailure *)
        /\ failedSet = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> <<>>]
        /\ recoveredElem = [self \in ({SW_RESOLVE_PROC} \X SW) |-> ""]
        (* Process rcNibEventHandler *)
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> [type |-> 0]]
        (* Process controllerTrafficEngineering *)
        /\ topoChangeEvent = [self \in ({rc0} \X {CONT_TE}) |-> [type |-> 0]]
        /\ currSetDownSw = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag_id = [self \in ({rc0} \X {CONT_TE}) |-> 0]
        /\ init = [self \in ({rc0} \X {CONT_TE}) |-> 1]
        /\ nxtDAG = [self \in ({rc0} \X {CONT_TE}) |-> [type |-> 0]]
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
        /\ stepOfFailure_ = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> [dag |-> 0]]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        (* Process rcIRMonitor *)
        /\ currIRMon = [self \in ({rc0} \X {CONT_MONITOR}) |-> 0]
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
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
        /\ removedIR = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
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
                                        [] self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({rc0} \X {CONT_MONITOR}) -> "controllerIRMonitor"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"
                                        [] self \in ({ofc0, rc0} \X {WATCH_DOG}) -> "ControllerWatchDogProc"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ swCanReceivePackets(self[2])
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ TRUE
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                       "Failure of assertion at line 1175, column 9.")
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ IF ingressPkt'[self].type = INSTALL_FLOW
                                   THEN /\ installedIRs' = Append(installedIRs, ingressPkt'[self].flow)
                                        /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], ingressPkt'[self].flow)]
                                        /\ switch2Controller' = Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                                                           from |-> self[2],
                                                                                           flow |-> ingressPkt'[self].flow])
                                   ELSE /\ IF \E i \in DOMAIN TCAM[self[2]]: TCAM[self[2]][i] = ingressPkt'[self].flow
                                              THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], ingressPkt'[self].flow))]
                                              ELSE /\ TRUE
                                                   /\ TCAM' = TCAM
                                        /\ switch2Controller' = Append(switch2Controller, [type |-> DELETED_SUCCESSFULLY,
                                                                                           from |-> self[2],
                                                                                           flow |-> ingressPkt'[self].flow])
                                        /\ UNCHANGED installedIRs
                             /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, switchStatus, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, DAGID, 
                                             MaxDAGID, DAGState, 
                                             RCNIBEventQueue, RCIRStatus, 
                                             RCSwSuspensionStatus, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, masterState, 
                                             controllerStateNIB, NIBIRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressIR, 
                                             egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             nxtDAG, setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket1"]
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstall, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         ir2sw, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, TEEventQueue, 
                                         DAGEventQueue, DAGQueue, DAGID, 
                                         MaxDAGID, DAGState, RCNIBEventQueue, 
                                         RCIRStatus, RCSwSuspensionStatus, 
                                         nxtRCIRID, idWorkerWorkingOnDAG, 
                                         RCSeqWorkerStatus, IRDoneSet, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, masterState, 
                                         controllerStateNIB, NIBIRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         ingressIR, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, event, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, seqEvent, 
                                         worker, toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, currDAG, IRSet, 
                                         currIRMon, nextIRToSent, rowIndex, 
                                         rowRemove, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, irID, 
                                         removedIR, controllerFailedModules >>

SwitchRcvPacket1(self) == /\ pc[self] = "SwitchRcvPacket1"
                          /\ IF swCanReceivePackets(self[2])
                                THEN /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                                     /\ Assert(ingressIR'[self].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                               "Failure of assertion at line 1218, column 17.")
                                     /\ TRUE
                                     /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                                     /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                                ELSE /\ ingressIR' = [ingressIR EXCEPT ![self] = [type |-> 0]]
                                     /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                     /\ UNCHANGED controller2Switch
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          switch2Controller, switchStatus, 
                                          installedIRs, NicAsic2OfaBuff, 
                                          Ofa2NicAsicBuff, Installer2OfaBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, TEEventQueue, 
                                          DAGEventQueue, DAGQueue, DAGID, 
                                          MaxDAGID, DAGState, RCNIBEventQueue, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          RCSeqWorkerStatus, IRDoneSet, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, masterState, 
                                          controllerStateNIB, NIBIRStatus, 
                                          SwSuspensionStatus, IRQueueNIB, 
                                          SetScheduledIRs, ingressPkt, 
                                          egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          obj, failedSet, statusResolveMsg, 
                                          recoveredElem, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, rowIndex, 
                                          rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR, controllerFailedModules >>

SwitchNicAsicInsertToOfaBuff(self) == /\ pc[self] = "SwitchNicAsicInsertToOfaBuff"
                                      /\ IF swCanReceivePackets(self[2])
                                            THEN /\ TRUE
                                                 /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Append(NicAsic2OfaBuff[self[2]], ingressIR[self])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                                 /\ UNCHANGED ingressIR
                                            ELSE /\ ingressIR' = [ingressIR EXCEPT ![self] = [type |-> 0]]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                                 /\ UNCHANGED NicAsic2OfaBuff
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      irTypeMapping, ir2sw, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      RecoveryStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      DAGID, MaxDAGID, 
                                                      DAGState, 
                                                      RCNIBEventQueue, 
                                                      RCIRStatus, 
                                                      RCSwSuspensionStatus, 
                                                      nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      RCSeqWorkerStatus, 
                                                      IRDoneSet, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      NIBIRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, event, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, 
                                                      nxtDAG, setRemovableIRs, 
                                                      currIR, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      removedIR, 
                                                      controllerFailedModules >>

swNicAsicProcPacketIn(self) == SwitchRcvPacket(self)
                                  \/ SwitchRcvPacket1(self)
                                  \/ SwitchNicAsicInsertToOfaBuff(self)

SwitchFromOFAPacket(self) == /\ pc[self] = "SwitchFromOFAPacket"
                             /\ swCanReceivePackets(self[2])
                             /\ Len(Ofa2NicAsicBuff[self[2]]) > 0
                             /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket1"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, DAGID, 
                                             MaxDAGID, DAGState, 
                                             RCNIBEventQueue, RCIRStatus, 
                                             RCSwSuspensionStatus, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, masterState, 
                                             controllerStateNIB, NIBIRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             nxtDAG, setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

SwitchFromOFAPacket1(self) == /\ pc[self] = "SwitchFromOFAPacket1"
                              /\ IF swCanReceivePackets(self[2])
                                    THEN /\ egressMsg' = [egressMsg EXCEPT ![self] = Head(Ofa2NicAsicBuff[self[2]])]
                                         /\ TRUE
                                         /\ Assert(\/ egressMsg'[self].type = INSTALLED_SUCCESSFULLY
                                                   \/ egressMsg'[self].type = DELETED_SUCCESSFULLY, 
                                                   "Failure of assertion at line 1251, column 17.")
                                         /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                                    ELSE /\ egressMsg' = [egressMsg EXCEPT ![self] = [type |-> 0]]
                                         /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                         /\ UNCHANGED Ofa2NicAsicBuff
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, 
                                              RCNIBEventQueue, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, 
                                              RCSeqWorkerStatus, IRDoneSet, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR, 
                                              controllerFailedModules >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ TRUE
                                            /\ TRUE
                                            /\ switch2Controller' = Append(switch2Controller, egressMsg[self])
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED egressMsg
                                       ELSE /\ egressMsg' = [egressMsg EXCEPT ![self] = [type |-> 0]]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED switch2Controller
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCNIBEventQueue, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

swNicAsicProcPacketOut(self) == SwitchFromOFAPacket(self)
                                   \/ SwitchFromOFAPacket1(self)
                                   \/ SwitchNicAsicSendOutMsg(self)

SwitchOfaProcIn(self) == /\ pc[self] = "SwitchOfaProcIn"
                         /\ swOFACanProcessIRs(self[2])
                         /\ Len(NicAsic2OfaBuff[self[2]]) > 0
                         /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn1"]
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstall, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         ir2sw, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, TEEventQueue, 
                                         DAGEventQueue, DAGQueue, DAGID, 
                                         MaxDAGID, DAGState, RCNIBEventQueue, 
                                         RCIRStatus, RCSwSuspensionStatus, 
                                         nxtRCIRID, idWorkerWorkingOnDAG, 
                                         RCSeqWorkerStatus, IRDoneSet, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, masterState, 
                                         controllerStateNIB, NIBIRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         ingressIR, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, event, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, seqEvent, 
                                         worker, toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, currDAG, IRSet, 
                                         currIRMon, nextIRToSent, rowIndex, 
                                         rowRemove, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, irID, 
                                         removedIR, controllerFailedModules >>

SwitchOfaProcIn1(self) == /\ pc[self] = "SwitchOfaProcIn1"
                          /\ IF swOFACanProcessIRs(self[2])
                                THEN /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = Head(NicAsic2OfaBuff[self[2]])]
                                     /\ Assert(ofaInMsg'[self].to = self[2], 
                                               "Failure of assertion at line 1293, column 16.")
                                     /\ Assert(ofaInMsg'[self].flow  \in 1..MaxNumFlows, 
                                               "Failure of assertion at line 1294, column 16.")
                                     /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                                     /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                                ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                     /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                     /\ UNCHANGED NicAsic2OfaBuff
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          Ofa2NicAsicBuff, Installer2OfaBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, TEEventQueue, 
                                          DAGEventQueue, DAGQueue, DAGID, 
                                          MaxDAGID, DAGState, RCNIBEventQueue, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          RCSeqWorkerStatus, IRDoneSet, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, masterState, 
                                          controllerStateNIB, NIBIRStatus, 
                                          SwSuspensionStatus, IRQueueNIB, 
                                          SetScheduledIRs, ingressPkt, 
                                          ingressIR, egressMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          obj, failedSet, statusResolveMsg, 
                                          recoveredElem, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, rowIndex, 
                                          rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR, controllerFailedModules >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ TRUE
                                           /\ IF ofaInMsg[self].type \in {INSTALL_FLOW, DELETE_FLOW}
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket1"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED ofaInMsg
                                      ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, ir2sw, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                RecoveryStatus, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, 
                                                RCNIBEventQueue, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                RCSeqWorkerStatus, IRDoneSet, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                masterState, 
                                                controllerStateNIB, 
                                                NIBIRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, nxtDAG, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR, 
                                                controllerFailedModules >>

SwitchOfaProcessPacket1(self) == /\ pc[self] = "SwitchOfaProcessPacket1"
                                 /\ IF swOFACanProcessIRs(self[2])
                                       THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], [type |-> ofaInMsg[self].type,
                                                                                                                                       flow |-> ofaInMsg[self].flow])]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                            /\ UNCHANGED ofaInMsg
                                       ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                            /\ UNCHANGED Ofa2InstallerBuff
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCNIBEventQueue, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ofaModuleProcPacketIn(self) == SwitchOfaProcIn(self)
                                  \/ SwitchOfaProcIn1(self)
                                  \/ SwitchOfaProcessPacket(self)
                                  \/ SwitchOfaProcessPacket1(self)

SwitchOfaProcOut(self) == /\ pc[self] = "SwitchOfaProcOut"
                          /\ swOFACanProcessIRs(self[2])
                          /\ Installer2OfaBuff[self[2]] # <<>>
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut1"]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, TEEventQueue, 
                                          DAGEventQueue, DAGQueue, DAGID, 
                                          MaxDAGID, DAGState, RCNIBEventQueue, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          RCSeqWorkerStatus, IRDoneSet, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, masterState, 
                                          controllerStateNIB, NIBIRStatus, 
                                          SwSuspensionStatus, IRQueueNIB, 
                                          SetScheduledIRs, ingressPkt, 
                                          ingressIR, egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          obj, failedSet, statusResolveMsg, 
                                          recoveredElem, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, rowIndex, 
                                          rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR, controllerFailedModules >>

SwitchOfaProcOut1(self) == /\ pc[self] = "SwitchOfaProcOut1"
                           /\ IF swOFACanProcessIRs(self[2])
                                 THEN /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = Head(Installer2OfaBuff[self[2]])]
                                      /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Tail(Installer2OfaBuff[self[2]])]
                                      /\ Assert(ofaOutConfirmation'[self].flow \in 1..MaxNumFlows, 
                                                "Failure of assertion at line 1336, column 17.")
                                      /\ Assert(ofaOutConfirmation'[self].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                                "Failure of assertion at line 1337, column 17.")
                                      /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                                 ELSE /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                      /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                      /\ UNCHANGED Installer2OfaBuff
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           irTypeMapping, ir2sw, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Ofa2InstallerBuff, 
                                           TCAM, controlMsgCounter, 
                                           RecoveryStatus, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, DAGID, 
                                           MaxDAGID, DAGState, RCNIBEventQueue, 
                                           RCIRStatus, RCSwSuspensionStatus, 
                                           nxtRCIRID, idWorkerWorkingOnDAG, 
                                           RCSeqWorkerStatus, IRDoneSet, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, masterState, 
                                           controllerStateNIB, NIBIRStatus, 
                                           SwSuspensionStatus, IRQueueNIB, 
                                           SetScheduledIRs, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, obj, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, currDAG, IRSet, 
                                           currIRMon, nextIRToSent, rowIndex, 
                                           rowRemove, stepOfFailure_c, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure, msg, irID, 
                                           removedIR, controllerFailedModules >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ TRUE
                                                 /\ IF ofaOutConfirmation[self].type = INSTALL_FLOW
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation1"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation2"]
                                                 /\ UNCHANGED ofaOutConfirmation
                                            ELSE /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      irTypeMapping, ir2sw, 
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
                                                      RecoveryStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      DAGID, MaxDAGID, 
                                                      DAGState, 
                                                      RCNIBEventQueue, 
                                                      RCIRStatus, 
                                                      RCSwSuspensionStatus, 
                                                      nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      RCSeqWorkerStatus, 
                                                      IRDoneSet, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      NIBIRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, event, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, 
                                                      nxtDAG, setRemovableIRs, 
                                                      currIR, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      removedIR, 
                                                      controllerFailedModules >>

SendInstallationConfirmation1(self) == /\ pc[self] = "SendInstallationConfirmation1"
                                       /\ IF swOFACanProcessIRs(self[2])
                                             THEN /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> INSTALLED_SUCCESSFULLY,
                                                                                                                                       from |-> self[2],
                                                                                                                                       flow |-> ofaOutConfirmation[self].flow])]
                                                  /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                  /\ UNCHANGED ofaOutConfirmation
                                             ELSE /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                                  /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                  /\ UNCHANGED Ofa2NicAsicBuff
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       FirstInstall, 
                                                       sw_fail_ordering_var, 
                                                       ContProcSet, SwProcSet, 
                                                       irTypeMapping, ir2sw, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       switchStatus, 
                                                       installedIRs, 
                                                       NicAsic2OfaBuff, 
                                                       Installer2OfaBuff, 
                                                       Ofa2InstallerBuff, TCAM, 
                                                       controlMsgCounter, 
                                                       RecoveryStatus, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       switchOrdering, 
                                                       TEEventQueue, 
                                                       DAGEventQueue, DAGQueue, 
                                                       DAGID, MaxDAGID, 
                                                       DAGState, 
                                                       RCNIBEventQueue, 
                                                       RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       nxtRCIRID, 
                                                       idWorkerWorkingOnDAG, 
                                                       RCSeqWorkerStatus, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       masterState, 
                                                       controllerStateNIB, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, obj, 
                                                       failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, event, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       nxtDAG, setRemovableIRs, 
                                                       currIR, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, msg, 
                                                       irID, removedIR, 
                                                       controllerFailedModules >>

SendInstallationConfirmation2(self) == /\ pc[self] = "SendInstallationConfirmation2"
                                       /\ IF swOFACanProcessIRs(self[2])
                                             THEN /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], [type |-> DELETED_SUCCESSFULLY,
                                                                                                                                       from |-> self[2],
                                                                                                                                       flow |-> ofaOutConfirmation[self].flow])]
                                                  /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                  /\ UNCHANGED ofaOutConfirmation
                                             ELSE /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                                  /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                  /\ UNCHANGED Ofa2NicAsicBuff
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       FirstInstall, 
                                                       sw_fail_ordering_var, 
                                                       ContProcSet, SwProcSet, 
                                                       irTypeMapping, ir2sw, 
                                                       swSeqChangedStatus, 
                                                       controller2Switch, 
                                                       switch2Controller, 
                                                       switchStatus, 
                                                       installedIRs, 
                                                       NicAsic2OfaBuff, 
                                                       Installer2OfaBuff, 
                                                       Ofa2InstallerBuff, TCAM, 
                                                       controlMsgCounter, 
                                                       RecoveryStatus, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       switchOrdering, 
                                                       TEEventQueue, 
                                                       DAGEventQueue, DAGQueue, 
                                                       DAGID, MaxDAGID, 
                                                       DAGState, 
                                                       RCNIBEventQueue, 
                                                       RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       nxtRCIRID, 
                                                       idWorkerWorkingOnDAG, 
                                                       RCSeqWorkerStatus, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       masterState, 
                                                       controllerStateNIB, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, obj, 
                                                       failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, event, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       nxtDAG, setRemovableIRs, 
                                                       currIR, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, msg, 
                                                       irID, removedIR, 
                                                       controllerFailedModules >>

ofaModuleProcPacketOut(self) == SwitchOfaProcOut(self)
                                   \/ SwitchOfaProcOut1(self)
                                   \/ SendInstallationConfirmation(self)
                                   \/ SendInstallationConfirmation1(self)
                                   \/ SendInstallationConfirmation2(self)

SwitchInstallerProc(self) == /\ pc[self] = "SwitchInstallerProc"
                             /\ swCanInstallIRs(self[2])
                             /\ Len(Ofa2InstallerBuff[self[2]]) > 0
                             /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc1"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, DAGID, 
                                             MaxDAGID, DAGState, 
                                             RCNIBEventQueue, RCIRStatus, 
                                             RCSwSuspensionStatus, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, masterState, 
                                             controllerStateNIB, NIBIRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             nxtDAG, setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

SwitchInstallerProc1(self) == /\ pc[self] = "SwitchInstallerProc1"
                              /\ IF swCanInstallIRs(self[2])
                                    THEN /\ installerInIR' = [installerInIR EXCEPT ![self] = Head(Ofa2InstallerBuff[self[2]])]
                                         /\ Assert(installerInIR'[self].flow \in 1..MaxNumFlows, 
                                                   "Failure of assertion at line 1392, column 17.")
                                         /\ Assert(installerInIR'[self].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                                   "Failure of assertion at line 1393, column 17.")
                                         /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                                         /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                                    ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                         /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                         /\ UNCHANGED Ofa2InstallerBuff
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, 
                                              RCNIBEventQueue, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, 
                                              RCSeqWorkerStatus, IRDoneSet, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR, 
                                              controllerFailedModules >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ TRUE
                                               /\ IF installerInIR[self].type = INSTALL_FLOW
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM1"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM2"]
                                               /\ UNCHANGED installerInIR
                                          ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    irTypeMapping, ir2sw, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    RecoveryStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    RCNIBEventQueue, 
                                                    RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    RCSeqWorkerStatus, 
                                                    IRDoneSet, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, obj, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    removedIR, 
                                                    controllerFailedModules >>

SwitchInstallerInsert2TCAM1(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM1"
                                     /\ IF swCanInstallIRs(self[2])
                                           THEN /\ installedIRs' = Append(installedIRs, installerInIR[self].flow)
                                                /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], installerInIR[self].flow)]
                                                /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerSendConfirmation"]
                                                /\ UNCHANGED installerInIR
                                           ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                                /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                /\ UNCHANGED << installedIRs, 
                                                                TCAM >>
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     FirstInstall, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, ir2sw, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     switchStatus, 
                                                     NicAsic2OfaBuff, 
                                                     Ofa2NicAsicBuff, 
                                                     Installer2OfaBuff, 
                                                     Ofa2InstallerBuff, 
                                                     controlMsgCounter, 
                                                     RecoveryStatus, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     switchOrdering, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     masterState, 
                                                     controllerStateNIB, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     ingressPkt, ingressIR, 
                                                     egressMsg, ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     statusMsg, notFailedSet, 
                                                     failedElem, obj, 
                                                     failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

SwitchInstallerInsert2TCAM2(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM2"
                                     /\ IF swCanInstallIRs(self[2])
                                           THEN /\ IF \E i \in DOMAIN TCAM[self[2]]: TCAM[self[2]][i] = installerInIR[self].flow
                                                      THEN /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM3"]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerSendConfirmation"]
                                                /\ UNCHANGED installerInIR
                                           ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                                /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     FirstInstall, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, ir2sw, 
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
                                                     RecoveryStatus, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     switchOrdering, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     masterState, 
                                                     controllerStateNIB, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     ingressPkt, ingressIR, 
                                                     egressMsg, ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     statusMsg, notFailedSet, 
                                                     failedElem, obj, 
                                                     failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

SwitchInstallerInsert2TCAM3(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM3"
                                     /\ IF swCanInstallIRs(self[2])
                                           THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], installerInIR[self].flow))]
                                                /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerSendConfirmation"]
                                                /\ UNCHANGED installerInIR
                                           ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                                /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                /\ TCAM' = TCAM
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     FirstInstall, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, ir2sw, 
                                                     swSeqChangedStatus, 
                                                     controller2Switch, 
                                                     switch2Controller, 
                                                     switchStatus, 
                                                     installedIRs, 
                                                     NicAsic2OfaBuff, 
                                                     Ofa2NicAsicBuff, 
                                                     Installer2OfaBuff, 
                                                     Ofa2InstallerBuff, 
                                                     controlMsgCounter, 
                                                     RecoveryStatus, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     switchOrdering, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     masterState, 
                                                     controllerStateNIB, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     ingressPkt, ingressIR, 
                                                     egressMsg, ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     statusMsg, notFailedSet, 
                                                     failedElem, obj, 
                                                     failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

SwitchInstallerSendConfirmation(self) == /\ pc[self] = "SwitchInstallerSendConfirmation"
                                         /\ IF swCanInstallIRs(self[2])
                                               THEN /\ TRUE
                                                    /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Append(Installer2OfaBuff[self[2]], installerInIR[self])]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED installerInIR
                                               ELSE /\ installerInIR' = [installerInIR EXCEPT ![self] = [type |-> 0, flow |-> 0]]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED Installer2OfaBuff
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         sw_fail_ordering_var, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         irTypeMapping, ir2sw, 
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
                                                         RecoveryStatus, 
                                                         controllerSubmoduleFailNum, 
                                                         controllerSubmoduleFailStat, 
                                                         switchOrdering, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, DAGID, 
                                                         MaxDAGID, DAGState, 
                                                         RCNIBEventQueue, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         nxtRCIRID, 
                                                         idWorkerWorkingOnDAG, 
                                                         RCSeqWorkerStatus, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, obj, 
                                                         failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
                                                         controllerFailedModules >>

installerModuleProc(self) == SwitchInstallerProc(self)
                                \/ SwitchInstallerProc1(self)
                                \/ SwitchInstallerInsert2TCAM(self)
                                \/ SwitchInstallerInsert2TCAM1(self)
                                \/ SwitchInstallerInsert2TCAM2(self)
                                \/ SwitchInstallerInsert2TCAM3(self)
                                \/ SwitchInstallerSendConfirmation(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                             \/ switchLock[2] = self[2]
                       /\ sw_fail_ordering_var # <<>>
                       /\ \E x \in Head(sw_fail_ordering_var): x.sw = self[2]
                       /\ obj' = [obj EXCEPT ![self] = CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2]]
                       /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]].transient = obj'[self].transient,
                                                                   ![self[2]].partial = obj'[self].partial]
                       /\ Assert(obj'[self] \in Head(sw_fail_ordering_var), 
                                 "Failure of assertion at line 544, column 9 of macro called at line 1472, column 9.")
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{obj'[self]})>> \o Tail(sw_fail_ordering_var)
                       /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                       /\ IF obj'[self].partial = 0
                             THEN /\ IF switchStatus[self[2]].nicAsic = NotFailed
                                        THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                             /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                            swID |-> self[2],
                                                                                            num |-> controlMsgCounter'[self[2]]]]
                                             /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << swSeqChangedStatus, 
                                                             controlMsgCounter, 
                                                             statusMsg >>
                                  /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> Failed, nicAsic |-> Failed,
                                                                                          ofa |-> Failed, installer |-> Failed]]
                                  /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                  /\ TCAM' = [TCAM EXCEPT ![self[2]] = <<>>]
                                  /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                  /\ UNCHANGED << notFailedSet, failedElem >>
                             ELSE /\ notFailedSet' = [notFailedSet EXCEPT ![self] = returnSwitchElementsNotFailed(self[2])]
                                  /\ notFailedSet'[self] # {}
                                  /\ \E elem \in notFailedSet'[self]:
                                       failedElem' = [failedElem EXCEPT ![self] = elem]
                                  /\ IF failedElem'[self] = "cpu"
                                        THEN /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                                       "Failure of assertion at line 669, column 9 of macro called at line 1492, column 17.")
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
                                                   THEN /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed, 
                                                                  "Failure of assertion at line 721, column 9 of macro called at line 1494, column 17.")
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
                                                              THEN /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed, 
                                                                             "Failure of assertion at line 765, column 9 of macro called at line 1496, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                                   /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                         THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                                        "Failure of assertion at line 768, column 13 of macro called at line 1496, column 17.")
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
                                                                         THEN /\ Assert(switchStatus[self[2]].nicAsic = NotFailed, 
                                                                                        "Failure of assertion at line 615, column 9 of macro called at line 1498, column 17.")
                                                                              /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                              /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                              /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                           swID |-> self[2],
                                                                                                                           num |-> controlMsgCounter'[self[2]]]]
                                                                              /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                                                         ELSE /\ Assert(FALSE, 
                                                                                        "Failure of assertion at line 1499, column 18.")
                                                                              /\ UNCHANGED << swSeqChangedStatus, 
                                                                                              controller2Switch, 
                                                                                              switchStatus, 
                                                                                              controlMsgCounter, 
                                                                                              statusMsg >>
                                             /\ UNCHANGED << NicAsic2OfaBuff, 
                                                             Ofa2NicAsicBuff, 
                                                             Installer2OfaBuff, 
                                                             Ofa2InstallerBuff >>
                                  /\ TCAM' = TCAM
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstall, ContProcSet, SwProcSet, 
                                       irTypeMapping, ir2sw, switch2Controller, 
                                       installedIRs, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, TEEventQueue, 
                                       DAGEventQueue, DAGQueue, DAGID, 
                                       MaxDAGID, DAGState, RCNIBEventQueue, 
                                       RCIRStatus, RCSwSuspensionStatus, 
                                       nxtRCIRID, idWorkerWorkingOnDAG, 
                                       RCSeqWorkerStatus, IRDoneSet, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, masterState, 
                                       controllerStateNIB, NIBIRStatus, 
                                       SwSuspensionStatus, IRQueueNIB, 
                                       SetScheduledIRs, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, failedSet, 
                                       statusResolveMsg, recoveredElem, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, nxtDAG, 
                                       setRemovableIRs, currIR, currIRInDAG, 
                                       nxtDAGVertices, setIRsInDAG, prev_dag, 
                                       seqEvent, worker, toBeScheduledIRs, 
                                       nextIR, stepOfFailure_, currDAG, IRSet, 
                                       currIRMon, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, irID, removedIR, 
                                       controllerFailedModules >>

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ RecoveryStatus[self[2]].transient = 1
                              /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF RecoveryStatus[self[2]].partial = 0
                                    THEN /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                   "Failure of assertion at line 581, column 9 of macro called at line 1521, column 13.")
                                         /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                   "Failure of assertion at line 582, column 9 of macro called at line 1521, column 13.")
                                         /\ Assert(switchStatus[self[2]].ofa = Failed, 
                                                   "Failure of assertion at line 583, column 9 of macro called at line 1521, column 13.")
                                         /\ Assert(switchStatus[self[2]].installer = Failed, 
                                                   "Failure of assertion at line 584, column 9 of macro called at line 1521, column 13.")
                                         /\ nicAsicStartingMode(self[2])
                                         /\ ofaStartingMode(self[2])
                                         /\ installerInStartingMode(self[2])
                                         /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> NotFailed, nicAsic |-> NotFailed,
                                                                                                 ofa |-> NotFailed, installer |-> NotFailed]]
                                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                         /\ TCAM' = [TCAM EXCEPT ![self[2]] = <<>>]
                                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                         /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                         /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] = [type |-> KEEP_ALIVE,
                                                                                                    swID |-> self[2],
                                                                                                    num |-> controlMsgCounter'[self[2]],
                                                                                                    status |-> [installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)]]]
                                         /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusResolveMsg'[self])
                                         /\ UNCHANGED << failedSet, 
                                                         recoveredElem >>
                                    ELSE /\ failedSet' = [failedSet EXCEPT ![self] = returnSwitchFailedElements(self[2])]
                                         /\ Cardinality(failedSet'[self]) > 0
                                         /\ \E elem \in failedSet'[self]:
                                              recoveredElem' = [recoveredElem EXCEPT ![self] = elem]
                                         /\ IF recoveredElem'[self] = "cpu"
                                               THEN /\ ofaStartingMode(self[2]) /\ installerInStartingMode(self[2])
                                                    /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                              "Failure of assertion at line 696, column 9 of macro called at line 1529, column 43.")
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
                                                                         "Failure of assertion at line 641, column 9 of macro called at line 1530, column 50.")
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
                                                                                    "Failure of assertion at line 743, column 9 of macro called at line 1531, column 46.")
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
                                                                                               "Failure of assertion at line 787, column 9 of macro called at line 1532, column 52.")
                                                                                     /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                                     /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                           THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                                          "Failure of assertion at line 790, column 13 of macro called at line 1532, column 52.")
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
                                                                                               "Failure of assertion at line 1533, column 18.")
                                                                                     /\ UNCHANGED << swSeqChangedStatus, 
                                                                                                     switchStatus, 
                                                                                                     controlMsgCounter, 
                                                                                                     statusResolveMsg >>
                                                               /\ UNCHANGED controller2Switch
                                                    /\ UNCHANGED << NicAsic2OfaBuff, 
                                                                    Ofa2NicAsicBuff, 
                                                                    Installer2OfaBuff, 
                                                                    Ofa2InstallerBuff >>
                                         /\ TCAM' = TCAM
                              /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]] = [transient |-> 0, partial |-> 0]]
                              /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              switch2Controller, installedIRs, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, 
                                              RCNIBEventQueue, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, 
                                              RCSeqWorkerStatus, IRDoneSet, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              event, topoChangeEvent, 
                                              currSetDownSw, prev_dag_id, init, 
                                              nxtDAG, setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR, 
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
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                   sw_fail_ordering_var, ContProcSet, 
                                   SwProcSet, irTypeMapping, ir2sw, 
                                   swSeqChangedStatus, controller2Switch, 
                                   switch2Controller, switchStatus, 
                                   installedIRs, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   RecoveryStatus, controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   TEEventQueue, DAGEventQueue, DAGQueue, 
                                   DAGID, MaxDAGID, DAGState, RCNIBEventQueue, 
                                   RCIRStatus, RCSwSuspensionStatus, nxtRCIRID, 
                                   idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                   IRDoneSet, idThreadWorkingOnIR, 
                                   workerThreadRanking, masterState, 
                                   controllerStateNIB, NIBIRStatus, 
                                   SwSuspensionStatus, IRQueueNIB, 
                                   SetScheduledIRs, ingressPkt, ingressIR, 
                                   egressMsg, ofaInMsg, ofaOutConfirmation, 
                                   installerInIR, statusMsg, notFailedSet, 
                                   failedElem, obj, failedSet, 
                                   statusResolveMsg, recoveredElem, event, 
                                   topoChangeEvent, currSetDownSw, prev_dag_id, 
                                   init, nxtDAG, setRemovableIRs, currIR, 
                                   currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                   prev_dag, seqEvent, worker, 
                                   toBeScheduledIRs, nextIR, stepOfFailure_, 
                                   currDAG, IRSet, currIRMon, nextIRToSent, 
                                   rowIndex, rowRemove, stepOfFailure_c, 
                                   monitoringEvent, setIRsToReset, resetIR, 
                                   stepOfFailure, msg, irID, removedIR, 
                                   controllerFailedModules >>

ghostUnlockProcess(self) == ghostProc(self)

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ controllerIsMaster(self[1])
                               /\ moduleIsUp(self)
                               /\ RCNIBEventQueue[self[1]] # <<>>
                               /\ TRUE
                               /\ pc' = [pc EXCEPT ![self] = "rcReadEvent"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstall, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, ir2sw, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               RecoveryStatus, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, DAGID, 
                                               MaxDAGID, DAGState, 
                                               RCNIBEventQueue, RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
                                               RCSeqWorkerStatus, IRDoneSet, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               masterState, controllerStateNIB, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, currDAG, 
                                               IRSet, currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

rcReadEvent(self) == /\ pc[self] = "rcReadEvent"
                     /\ event' = [event EXCEPT ![self] = Head(RCNIBEventQueue[self[1]])]
                     /\ Assert(event'[self].type \in {TOPO_MOD, IR_MOD}, 
                               "Failure of assertion at line 1589, column 9.")
                     /\ pc' = [pc EXCEPT ![self] = "rcCheckType"]
                     /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                     sw_fail_ordering_var, ContProcSet, 
                                     SwProcSet, irTypeMapping, ir2sw, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, switchStatus, 
                                     installedIRs, NicAsic2OfaBuff, 
                                     Ofa2NicAsicBuff, Installer2OfaBuff, 
                                     Ofa2InstallerBuff, TCAM, 
                                     controlMsgCounter, RecoveryStatus, 
                                     controllerSubmoduleFailNum, 
                                     controllerSubmoduleFailStat, 
                                     switchOrdering, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                     DAGState, RCNIBEventQueue, RCIRStatus, 
                                     RCSwSuspensionStatus, nxtRCIRID, 
                                     idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                     IRDoneSet, idThreadWorkingOnIR, 
                                     workerThreadRanking, masterState, 
                                     controllerStateNIB, NIBIRStatus, 
                                     SwSuspensionStatus, IRQueueNIB, 
                                     SetScheduledIRs, ingressPkt, ingressIR, 
                                     egressMsg, ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, obj, failedSet, 
                                     statusResolveMsg, recoveredElem, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, nxtDAG, 
                                     setRemovableIRs, currIR, currIRInDAG, 
                                     nxtDAGVertices, setIRsInDAG, prev_dag, 
                                     seqEvent, worker, toBeScheduledIRs, 
                                     nextIR, stepOfFailure_, currDAG, IRSet, 
                                     currIRMon, nextIRToSent, rowIndex, 
                                     rowRemove, stepOfFailure_c, 
                                     monitoringEvent, setIRsToReset, resetIR, 
                                     stepOfFailure, msg, irID, removedIR, 
                                     controllerFailedModules >>

rcCheckType(self) == /\ pc[self] = "rcCheckType"
                     /\ IF (event[self].type = TOPO_MOD)
                           THEN /\ pc' = [pc EXCEPT ![self] = "rcTopoModEvent"]
                           ELSE /\ IF (event[self].type = IR_MOD)
                                      THEN /\ pc' = [pc EXCEPT ![self] = "rcIRModEvent"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "rcRemoveEvent"]
                     /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                     sw_fail_ordering_var, ContProcSet, 
                                     SwProcSet, irTypeMapping, ir2sw, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, switchStatus, 
                                     installedIRs, NicAsic2OfaBuff, 
                                     Ofa2NicAsicBuff, Installer2OfaBuff, 
                                     Ofa2InstallerBuff, TCAM, 
                                     controlMsgCounter, RecoveryStatus, 
                                     controllerSubmoduleFailNum, 
                                     controllerSubmoduleFailStat, 
                                     switchOrdering, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                     DAGState, RCNIBEventQueue, RCIRStatus, 
                                     RCSwSuspensionStatus, nxtRCIRID, 
                                     idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                     IRDoneSet, idThreadWorkingOnIR, 
                                     workerThreadRanking, masterState, 
                                     controllerStateNIB, NIBIRStatus, 
                                     SwSuspensionStatus, IRQueueNIB, 
                                     SetScheduledIRs, ingressPkt, ingressIR, 
                                     egressMsg, ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, obj, failedSet, 
                                     statusResolveMsg, recoveredElem, event, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, nxtDAG, 
                                     setRemovableIRs, currIR, currIRInDAG, 
                                     nxtDAGVertices, setIRsInDAG, prev_dag, 
                                     seqEvent, worker, toBeScheduledIRs, 
                                     nextIR, stepOfFailure_, currDAG, IRSet, 
                                     currIRMon, nextIRToSent, rowIndex, 
                                     rowRemove, stepOfFailure_c, 
                                     monitoringEvent, setIRsToReset, resetIR, 
                                     stepOfFailure, msg, irID, removedIR, 
                                     controllerFailedModules >>

rcTopoModEvent(self) == /\ pc[self] = "rcTopoModEvent"
                        /\ IF RCSwSuspensionStatus[self[1]][event[self].sw] # event[self].state
                              THEN /\ pc' = [pc EXCEPT ![self] = "rcSwSuspend"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "rcRemoveEvent"]
                        /\ UNCHANGED << switchLock, controllerLock, 
                                        FirstInstall, sw_fail_ordering_var, 
                                        ContProcSet, SwProcSet, irTypeMapping, 
                                        ir2sw, swSeqChangedStatus, 
                                        controller2Switch, switch2Controller, 
                                        switchStatus, installedIRs, 
                                        NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                        Installer2OfaBuff, Ofa2InstallerBuff, 
                                        TCAM, controlMsgCounter, 
                                        RecoveryStatus, 
                                        controllerSubmoduleFailNum, 
                                        controllerSubmoduleFailStat, 
                                        switchOrdering, TEEventQueue, 
                                        DAGEventQueue, DAGQueue, DAGID, 
                                        MaxDAGID, DAGState, RCNIBEventQueue, 
                                        RCIRStatus, RCSwSuspensionStatus, 
                                        nxtRCIRID, idWorkerWorkingOnDAG, 
                                        RCSeqWorkerStatus, IRDoneSet, 
                                        idThreadWorkingOnIR, 
                                        workerThreadRanking, masterState, 
                                        controllerStateNIB, NIBIRStatus, 
                                        SwSuspensionStatus, IRQueueNIB, 
                                        SetScheduledIRs, ingressPkt, ingressIR, 
                                        egressMsg, ofaInMsg, 
                                        ofaOutConfirmation, installerInIR, 
                                        statusMsg, notFailedSet, failedElem, 
                                        obj, failedSet, statusResolveMsg, 
                                        recoveredElem, event, topoChangeEvent, 
                                        currSetDownSw, prev_dag_id, init, 
                                        nxtDAG, setRemovableIRs, currIR, 
                                        currIRInDAG, nxtDAGVertices, 
                                        setIRsInDAG, prev_dag, seqEvent, 
                                        worker, toBeScheduledIRs, nextIR, 
                                        stepOfFailure_, currDAG, IRSet, 
                                        currIRMon, nextIRToSent, rowIndex, 
                                        rowRemove, stepOfFailure_c, 
                                        monitoringEvent, setIRsToReset, 
                                        resetIR, stepOfFailure, msg, irID, 
                                        removedIR, controllerFailedModules >>

rcSwSuspend(self) == /\ pc[self] = "rcSwSuspend"
                     /\ RCSwSuspensionStatus' = [RCSwSuspensionStatus EXCEPT ![self[1]][event[self].sw] = event[self].state]
                     /\ pc' = [pc EXCEPT ![self] = "rcTEEventQue"]
                     /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                     sw_fail_ordering_var, ContProcSet, 
                                     SwProcSet, irTypeMapping, ir2sw, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, switchStatus, 
                                     installedIRs, NicAsic2OfaBuff, 
                                     Ofa2NicAsicBuff, Installer2OfaBuff, 
                                     Ofa2InstallerBuff, TCAM, 
                                     controlMsgCounter, RecoveryStatus, 
                                     controllerSubmoduleFailNum, 
                                     controllerSubmoduleFailStat, 
                                     switchOrdering, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                     DAGState, RCNIBEventQueue, RCIRStatus, 
                                     nxtRCIRID, idWorkerWorkingOnDAG, 
                                     RCSeqWorkerStatus, IRDoneSet, 
                                     idThreadWorkingOnIR, workerThreadRanking, 
                                     masterState, controllerStateNIB, 
                                     NIBIRStatus, SwSuspensionStatus, 
                                     IRQueueNIB, SetScheduledIRs, ingressPkt, 
                                     ingressIR, egressMsg, ofaInMsg, 
                                     ofaOutConfirmation, installerInIR, 
                                     statusMsg, notFailedSet, failedElem, obj, 
                                     failedSet, statusResolveMsg, 
                                     recoveredElem, event, topoChangeEvent, 
                                     currSetDownSw, prev_dag_id, init, nxtDAG, 
                                     setRemovableIRs, currIR, currIRInDAG, 
                                     nxtDAGVertices, setIRsInDAG, prev_dag, 
                                     seqEvent, worker, toBeScheduledIRs, 
                                     nextIR, stepOfFailure_, currDAG, IRSet, 
                                     currIRMon, nextIRToSent, rowIndex, 
                                     rowRemove, stepOfFailure_c, 
                                     monitoringEvent, setIRsToReset, resetIR, 
                                     stepOfFailure, msg, irID, removedIR, 
                                     controllerFailedModules >>

rcTEEventQue(self) == /\ pc[self] = "rcTEEventQue"
                      /\ TEEventQueue' = [TEEventQueue EXCEPT ![self[1]] = Append(TEEventQueue[self[1]], event[self])]
                      /\ pc' = [pc EXCEPT ![self] = "rcRemoveEvent"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, DAGEventQueue, DAGQueue, 
                                      DAGID, MaxDAGID, DAGState, 
                                      RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRModEvent(self) == /\ pc[self] = "rcIRModEvent"
                      /\ IF RCIRStatus[self[1]][event[self].IR] # event[self].state
                            THEN /\ pc' = [pc EXCEPT ![self] = "rcIRStatus"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcRemoveEvent"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRStatus(self) == /\ pc[self] = "rcIRStatus"
                    /\ RCIRStatus' = [RCIRStatus EXCEPT ![self[1]][event[self].IR] = event[self].state]
                    /\ pc' = [pc EXCEPT ![self] = "rcCheckIRStatus"]
                    /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                    sw_fail_ordering_var, ContProcSet, 
                                    SwProcSet, irTypeMapping, ir2sw, 
                                    swSeqChangedStatus, controller2Switch, 
                                    switch2Controller, switchStatus, 
                                    installedIRs, NicAsic2OfaBuff, 
                                    Ofa2NicAsicBuff, Installer2OfaBuff, 
                                    Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                    RecoveryStatus, controllerSubmoduleFailNum, 
                                    controllerSubmoduleFailStat, 
                                    switchOrdering, TEEventQueue, 
                                    DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                    DAGState, RCNIBEventQueue, 
                                    RCSwSuspensionStatus, nxtRCIRID, 
                                    idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                    IRDoneSet, idThreadWorkingOnIR, 
                                    workerThreadRanking, masterState, 
                                    controllerStateNIB, NIBIRStatus, 
                                    SwSuspensionStatus, IRQueueNIB, 
                                    SetScheduledIRs, ingressPkt, ingressIR, 
                                    egressMsg, ofaInMsg, ofaOutConfirmation, 
                                    installerInIR, statusMsg, notFailedSet, 
                                    failedElem, obj, failedSet, 
                                    statusResolveMsg, recoveredElem, event, 
                                    topoChangeEvent, currSetDownSw, 
                                    prev_dag_id, init, nxtDAG, setRemovableIRs, 
                                    currIR, currIRInDAG, nxtDAGVertices, 
                                    setIRsInDAG, prev_dag, seqEvent, worker, 
                                    toBeScheduledIRs, nextIR, stepOfFailure_, 
                                    currDAG, IRSet, currIRMon, nextIRToSent, 
                                    rowIndex, rowRemove, stepOfFailure_c, 
                                    monitoringEvent, setIRsToReset, resetIR, 
                                    stepOfFailure, msg, irID, removedIR, 
                                    controllerFailedModules >>

rcCheckIRStatus(self) == /\ pc[self] = "rcCheckIRStatus"
                         /\ IF event[self].state \in {IR_SENT, IR_NONE, IR_DONE}
                               THEN /\ pc' = [pc EXCEPT ![self] = "rcChangeIRStatus"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "rcRemoveEvent"]
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstall, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         ir2sw, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, TEEventQueue, 
                                         DAGEventQueue, DAGQueue, DAGID, 
                                         MaxDAGID, DAGState, RCNIBEventQueue, 
                                         RCIRStatus, RCSwSuspensionStatus, 
                                         nxtRCIRID, idWorkerWorkingOnDAG, 
                                         RCSeqWorkerStatus, IRDoneSet, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, masterState, 
                                         controllerStateNIB, NIBIRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         ingressIR, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, event, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, seqEvent, 
                                         worker, toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, currDAG, IRSet, 
                                         currIRMon, nextIRToSent, rowIndex, 
                                         rowRemove, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, irID, 
                                         removedIR, controllerFailedModules >>

rcChangeIRStatus(self) == /\ pc[self] = "rcChangeIRStatus"
                          /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[event[self].IR]] = SetScheduledIRs[ir2sw[event[self].IR]]\{event[self].IR}]
                          /\ pc' = [pc EXCEPT ![self] = "rcRemoveEvent"]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, TEEventQueue, 
                                          DAGEventQueue, DAGQueue, DAGID, 
                                          MaxDAGID, DAGState, RCNIBEventQueue, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          RCSeqWorkerStatus, IRDoneSet, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, masterState, 
                                          controllerStateNIB, NIBIRStatus, 
                                          SwSuspensionStatus, IRQueueNIB, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, obj, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, rowIndex, 
                                          rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR, controllerFailedModules >>

rcRemoveEvent(self) == /\ pc[self] = "rcRemoveEvent"
                       /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![self[1]] = Tail(RCNIBEventQueue[self[1]])]
                       /\ pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstall, sw_fail_ordering_var, 
                                       ContProcSet, SwProcSet, irTypeMapping, 
                                       ir2sw, swSeqChangedStatus, 
                                       controller2Switch, switch2Controller, 
                                       switchStatus, installedIRs, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Installer2OfaBuff, Ofa2InstallerBuff, 
                                       TCAM, controlMsgCounter, RecoveryStatus, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, TEEventQueue, 
                                       DAGEventQueue, DAGQueue, DAGID, 
                                       MaxDAGID, DAGState, RCIRStatus, 
                                       RCSwSuspensionStatus, nxtRCIRID, 
                                       idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                       IRDoneSet, idThreadWorkingOnIR, 
                                       workerThreadRanking, masterState, 
                                       controllerStateNIB, NIBIRStatus, 
                                       SwSuspensionStatus, IRQueueNIB, 
                                       SetScheduledIRs, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, obj, failedSet, 
                                       statusResolveMsg, recoveredElem, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, nxtDAG, 
                                       setRemovableIRs, currIR, currIRInDAG, 
                                       nxtDAGVertices, setIRsInDAG, prev_dag, 
                                       seqEvent, worker, toBeScheduledIRs, 
                                       nextIR, stepOfFailure_, currDAG, IRSet, 
                                       currIRMon, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, irID, removedIR, 
                                       controllerFailedModules >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self) \/ rcReadEvent(self)
                              \/ rcCheckType(self) \/ rcTopoModEvent(self)
                              \/ rcSwSuspend(self) \/ rcTEEventQue(self)
                              \/ rcIRModEvent(self) \/ rcIRStatus(self)
                              \/ rcCheckIRStatus(self)
                              \/ rcChangeIRStatus(self)
                              \/ rcRemoveEvent(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ controllerIsMaster(self[1])
                          /\ moduleIsUp(self)
                          /\ init[self] = 1 \/ TEEventQueue[self[1]] # <<>>
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, TEEventQueue, 
                                          DAGEventQueue, DAGQueue, DAGID, 
                                          MaxDAGID, DAGState, RCNIBEventQueue, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          RCSeqWorkerStatus, IRDoneSet, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, masterState, 
                                          controllerStateNIB, NIBIRStatus, 
                                          SwSuspensionStatus, IRQueueNIB, 
                                          SetScheduledIRs, ingressPkt, 
                                          ingressIR, egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          obj, failedSet, statusResolveMsg, 
                                          recoveredElem, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, rowIndex, 
                                          rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR, controllerFailedModules >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF TEEventQueue[self[1]] # <<>>
                                           THEN /\ TRUE
                                                /\ pc' = [pc EXCEPT ![self] = "ReadHeadTEEvent"]
                                           ELSE /\ TRUE
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     FirstInstall, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, ir2sw, 
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
                                                     RecoveryStatus, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     switchOrdering, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     masterState, 
                                                     controllerStateNIB, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     ingressPkt, ingressIR, 
                                                     egressMsg, ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     installerInIR, statusMsg, 
                                                     notFailedSet, failedElem, 
                                                     obj, failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

ReadHeadTEEvent(self) == /\ pc[self] = "ReadHeadTEEvent"
                         /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue[self[1]])]
                         /\ Assert(topoChangeEvent'[self].type \in {TOPO_MOD}, 
                                   "Failure of assertion at line 1626, column 17.")
                         /\ pc' = [pc EXCEPT ![self] = "ComputeTopoUpdates"]
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstall, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         ir2sw, swSeqChangedStatus, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, TEEventQueue, 
                                         DAGEventQueue, DAGQueue, DAGID, 
                                         MaxDAGID, DAGState, RCNIBEventQueue, 
                                         RCIRStatus, RCSwSuspensionStatus, 
                                         nxtRCIRID, idWorkerWorkingOnDAG, 
                                         RCSeqWorkerStatus, IRDoneSet, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, masterState, 
                                         controllerStateNIB, NIBIRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         ingressIR, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, event, currSetDownSw, 
                                         prev_dag_id, init, nxtDAG, 
                                         setRemovableIRs, currIR, currIRInDAG, 
                                         nxtDAGVertices, setIRsInDAG, prev_dag, 
                                         seqEvent, worker, toBeScheduledIRs, 
                                         nextIR, stepOfFailure_, currDAG, 
                                         IRSet, currIRMon, nextIRToSent, 
                                         rowIndex, rowRemove, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, irID, 
                                         removedIR, controllerFailedModules >>

ComputeTopoUpdates(self) == /\ pc[self] = "ComputeTopoUpdates"
                            /\ IF topoChangeEvent[self].state = SW_SUSPEND
                                  THEN /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \cup {topoChangeEvent[self].sw}]
                                  ELSE /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \ {topoChangeEvent[self].sw}]
                            /\ pc' = [pc EXCEPT ![self] = "RemoveFromTEEventQueue"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstall, sw_fail_ordering_var, 
                                            ContProcSet, SwProcSet, 
                                            irTypeMapping, ir2sw, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, DAGID, 
                                            MaxDAGID, DAGState, 
                                            RCNIBEventQueue, RCIRStatus, 
                                            RCSwSuspensionStatus, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, 
                                            RCSeqWorkerStatus, IRDoneSet, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, masterState, 
                                            controllerStateNIB, NIBIRStatus, 
                                            SwSuspensionStatus, IRQueueNIB, 
                                            SetScheduledIRs, ingressPkt, 
                                            ingressIR, egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, obj, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            event, topoChangeEvent, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, nextIR, 
                                            stepOfFailure_, currDAG, IRSet, 
                                            currIRMon, nextIRToSent, rowIndex, 
                                            rowRemove, stepOfFailure_c, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, msg, irID, 
                                            removedIR, controllerFailedModules >>

RemoveFromTEEventQueue(self) == /\ pc[self] = "RemoveFromTEEventQueue"
                                /\ TEEventQueue' = [TEEventQueue EXCEPT ![self[1]] = Tail(TEEventQueue[self[1]])]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, ir2sw, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                RecoveryStatus, 
                                                controllerSubmoduleFailNum, 
                                                controllerSubmoduleFailStat, 
                                                switchOrdering, DAGEventQueue, 
                                                DAGQueue, DAGID, MaxDAGID, 
                                                DAGState, RCNIBEventQueue, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                RCSeqWorkerStatus, IRDoneSet, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                masterState, 
                                                controllerStateNIB, 
                                                NIBIRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, nxtDAG, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR, 
                                                controllerFailedModules >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ TRUE
                                           /\ DAGID' = (DAGID % MaxDAGID) + 1
                                           /\ nxtDAG' = [nxtDAG EXCEPT ![self] = [id |-> DAGID', dag |-> TOPO_DAG_MAPPING[currSetDownSw[self]]]]
                                           /\ IF prev_dag[self] = nxtDAG'[self].dag
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                                      /\ UNCHANGED << prev_dag_id, 
                                                                      init, 
                                                                      nxtDAGVertices >>
                                                 ELSE /\ nxtDAGVertices' = [nxtDAGVertices EXCEPT ![self] = nxtDAG'[self].dag.v]
                                                      /\ IF init[self] = 0
                                                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateDAGState"]
                                                                 /\ UNCHANGED << prev_dag_id, 
                                                                                 init >>
                                                            ELSE /\ init' = [init EXCEPT ![self] = 0]
                                                                 /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID']
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                           /\ UNCHANGED << switchLock, 
                                                           controllerLock, 
                                                           FirstInstall, 
                                                           sw_fail_ordering_var, 
                                                           ContProcSet, 
                                                           SwProcSet, 
                                                           irTypeMapping, 
                                                           ir2sw, 
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
                                                           RecoveryStatus, 
                                                           controllerSubmoduleFailNum, 
                                                           controllerSubmoduleFailStat, 
                                                           switchOrdering, 
                                                           TEEventQueue, 
                                                           DAGEventQueue, 
                                                           DAGQueue, MaxDAGID, 
                                                           DAGState, 
                                                           RCNIBEventQueue, 
                                                           RCIRStatus, 
                                                           RCSwSuspensionStatus, 
                                                           nxtRCIRID, 
                                                           idWorkerWorkingOnDAG, 
                                                           RCSeqWorkerStatus, 
                                                           IRDoneSet, 
                                                           idThreadWorkingOnIR, 
                                                           workerThreadRanking, 
                                                           masterState, 
                                                           controllerStateNIB, 
                                                           NIBIRStatus, 
                                                           SwSuspensionStatus, 
                                                           IRQueueNIB, 
                                                           SetScheduledIRs, 
                                                           ingressPkt, 
                                                           ingressIR, 
                                                           egressMsg, ofaInMsg, 
                                                           ofaOutConfirmation, 
                                                           installerInIR, 
                                                           statusMsg, 
                                                           notFailedSet, 
                                                           failedElem, obj, 
                                                           failedSet, 
                                                           statusResolveMsg, 
                                                           recoveredElem, 
                                                           event, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           setRemovableIRs, 
                                                           currIR, currIRInDAG, 
                                                           setIRsInDAG, 
                                                           prev_dag, seqEvent, 
                                                           worker, 
                                                           toBeScheduledIRs, 
                                                           nextIR, 
                                                           stepOfFailure_, 
                                                           currDAG, IRSet, 
                                                           currIRMon, 
                                                           nextIRToSent, 
                                                           rowIndex, rowRemove, 
                                                           stepOfFailure_c, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, 
                                                           stepOfFailure, msg, 
                                                           irID, removedIR, 
                                                           controllerFailedModules >>

ControllerUpdateDAGState(self) == /\ pc[self] = "ControllerUpdateDAGState"
                                  /\ DAGState' = [DAGState EXCEPT ![prev_dag_id[self]] = DAG_STALE]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTESendDagStaleNotif"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstall, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, ir2sw, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  switchStatus, installedIRs, 
                                                  NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  RecoveryStatus, 
                                                  controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat, 
                                                  switchOrdering, TEEventQueue, 
                                                  DAGEventQueue, DAGQueue, 
                                                  DAGID, MaxDAGID, 
                                                  RCNIBEventQueue, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  RCSeqWorkerStatus, IRDoneSet, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  masterState, 
                                                  controllerStateNIB, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
                                                  statusResolveMsg, 
                                                  recoveredElem, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR, 
                                                  controllerFailedModules >>

ControllerTESendDagStaleNotif(self) == /\ pc[self] = "ControllerTESendDagStaleNotif"
                                       /\ TRUE
                                       /\ DAGEventQueue' = [DAGEventQueue EXCEPT ![self[1]] = Append(DAGEventQueue[self[1]], [type |-> DAG_STALE, id |-> prev_dag_id[self]])]
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       FirstInstall, 
                                                       sw_fail_ordering_var, 
                                                       ContProcSet, SwProcSet, 
                                                       irTypeMapping, ir2sw, 
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
                                                       RecoveryStatus, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       switchOrdering, 
                                                       TEEventQueue, DAGQueue, 
                                                       DAGID, MaxDAGID, 
                                                       DAGState, 
                                                       RCNIBEventQueue, 
                                                       RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       nxtRCIRID, 
                                                       idWorkerWorkingOnDAG, 
                                                       RCSeqWorkerStatus, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       masterState, 
                                                       controllerStateNIB, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, obj, 
                                                       failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, event, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       nxtDAG, setRemovableIRs, 
                                                       currIR, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, msg, 
                                                       irID, removedIR, 
                                                       controllerFailedModules >>

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ TRUE
                                                /\ DAGState[prev_dag_id[self]] = DAG_NONE
                                                /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID]
                                                /\ prev_dag' = [prev_dag EXCEPT ![self] = nxtDAG[self].dag]
                                                /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = getSetRemovableIRs(self[1], SW \ currSetDownSw[self], nxtDAGVertices[self])]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                /\ UNCHANGED << switchLock, 
                                                                controllerLock, 
                                                                FirstInstall, 
                                                                sw_fail_ordering_var, 
                                                                ContProcSet, 
                                                                SwProcSet, 
                                                                irTypeMapping, 
                                                                ir2sw, 
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
                                                                RecoveryStatus, 
                                                                controllerSubmoduleFailNum, 
                                                                controllerSubmoduleFailStat, 
                                                                switchOrdering, 
                                                                TEEventQueue, 
                                                                DAGEventQueue, 
                                                                DAGQueue, 
                                                                DAGID, 
                                                                MaxDAGID, 
                                                                DAGState, 
                                                                RCNIBEventQueue, 
                                                                RCIRStatus, 
                                                                RCSwSuspensionStatus, 
                                                                nxtRCIRID, 
                                                                idWorkerWorkingOnDAG, 
                                                                RCSeqWorkerStatus, 
                                                                IRDoneSet, 
                                                                idThreadWorkingOnIR, 
                                                                workerThreadRanking, 
                                                                masterState, 
                                                                controllerStateNIB, 
                                                                NIBIRStatus, 
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
                                                                obj, failedSet, 
                                                                statusResolveMsg, 
                                                                recoveredElem, 
                                                                event, 
                                                                topoChangeEvent, 
                                                                currSetDownSw, 
                                                                init, nxtDAG, 
                                                                currIR, 
                                                                currIRInDAG, 
                                                                nxtDAGVertices, 
                                                                setIRsInDAG, 
                                                                seqEvent, 
                                                                worker, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                stepOfFailure_, 
                                                                currDAG, IRSet, 
                                                                currIRMon, 
                                                                nextIRToSent, 
                                                                rowIndex, 
                                                                rowRemove, 
                                                                stepOfFailure_c, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, 
                                                                stepOfFailure, 
                                                                msg, irID, 
                                                                removedIR, 
                                                                controllerFailedModules >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF setRemovableIRs[self] # {}
                                                THEN /\ TRUE
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEChooseOneIR"]
                                                ELSE /\ TRUE
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEUpdateSetScheduledIR"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLock, 
                                                          FirstInstall, 
                                                          sw_fail_ordering_var, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          irTypeMapping, ir2sw, 
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
                                                          RecoveryStatus, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGID, 
                                                          MaxDAGID, DAGState, 
                                                          RCNIBEventQueue, 
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          RCSeqWorkerStatus, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          NIBIRStatus, 
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
                                                          failedElem, obj, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          nxtDAG, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, seqEvent, 
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

ControllerTEChooseOneIR(self) == /\ pc[self] = "ControllerTEChooseOneIR"
                                 /\ currIR' = [currIR EXCEPT ![self] = CHOOSE x \in setRemovableIRs[self]: TRUE]
                                 /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = setRemovableIRs[self] \ {currIR'[self]}]
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTEAdjustRCState"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCNIBEventQueue, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerTEAdjustRCState(self) == /\ pc[self] = "ControllerTEAdjustRCState"
                                   /\ RCIRStatus' = [RCIRStatus EXCEPT ![self[1]] = RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE)]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerTEAdjustNIBIRStatusState"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCNIBEventQueue, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

ControllerTEAdjustNIBIRStatusState(self) == /\ pc[self] = "ControllerTEAdjustNIBIRStatusState"
                                            /\ NIBIRStatus' = NIBIRStatus @@ (nxtRCIRID :> IR_NONE)
                                            /\ FirstInstall' = FirstInstall @@ (nxtRCIRID :> 0)
                                            /\ pc' = [pc EXCEPT ![self] = "ControllerTEIRMapping"]
                                            /\ UNCHANGED << switchLock, 
                                                            controllerLock, 
                                                            sw_fail_ordering_var, 
                                                            ContProcSet, 
                                                            SwProcSet, 
                                                            irTypeMapping, 
                                                            ir2sw, 
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
                                                            RecoveryStatus, 
                                                            controllerSubmoduleFailNum, 
                                                            controllerSubmoduleFailStat, 
                                                            switchOrdering, 
                                                            TEEventQueue, 
                                                            DAGEventQueue, 
                                                            DAGQueue, DAGID, 
                                                            MaxDAGID, DAGState, 
                                                            RCNIBEventQueue, 
                                                            RCIRStatus, 
                                                            RCSwSuspensionStatus, 
                                                            nxtRCIRID, 
                                                            idWorkerWorkingOnDAG, 
                                                            RCSeqWorkerStatus, 
                                                            IRDoneSet, 
                                                            idThreadWorkingOnIR, 
                                                            workerThreadRanking, 
                                                            masterState, 
                                                            controllerStateNIB, 
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
                                                            failedElem, obj, 
                                                            failedSet, 
                                                            statusResolveMsg, 
                                                            recoveredElem, 
                                                            event, 
                                                            topoChangeEvent, 
                                                            currSetDownSw, 
                                                            prev_dag_id, init, 
                                                            nxtDAG, 
                                                            setRemovableIRs, 
                                                            currIR, 
                                                            currIRInDAG, 
                                                            nxtDAGVertices, 
                                                            setIRsInDAG, 
                                                            prev_dag, seqEvent, 
                                                            worker, 
                                                            toBeScheduledIRs, 
                                                            nextIR, 
                                                            stepOfFailure_, 
                                                            currDAG, IRSet, 
                                                            currIRMon, 
                                                            nextIRToSent, 
                                                            rowIndex, 
                                                            rowRemove, 
                                                            stepOfFailure_c, 
                                                            monitoringEvent, 
                                                            setIRsToReset, 
                                                            resetIR, 
                                                            stepOfFailure, msg, 
                                                            irID, removedIR, 
                                                            controllerFailedModules >>

ControllerTEIRMapping(self) == /\ pc[self] = "ControllerTEIRMapping"
                               /\ irTypeMapping' = irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIR[self]]])
                               /\ ir2sw' = ir2sw @@ (nxtRCIRID :> ir2sw[currIR[self]])
                               /\ pc' = [pc EXCEPT ![self] = "ControllerTEIRAddNodesDAG"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstall, 
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
                                               RecoveryStatus, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, DAGID, 
                                               MaxDAGID, DAGState, 
                                               RCNIBEventQueue, RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
                                               RCSeqWorkerStatus, IRDoneSet, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               masterState, controllerStateNIB, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, currDAG, 
                                               IRSet, currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

ControllerTEIRAddNodesDAG(self) == /\ pc[self] = "ControllerTEIRAddNodesDAG"
                                   /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {nxtRCIRID}]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerTEGetIrsInDAG"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCNIBEventQueue, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, setRemovableIRs, 
                                                   currIR, currIRInDAG, 
                                                   nxtDAGVertices, setIRsInDAG, 
                                                   prev_dag, seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

ControllerTEGetIrsInDAG(self) == /\ pc[self] = "ControllerTEGetIrsInDAG"
                                 /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(ir2sw[currIR[self]], nxtDAGVertices[self])]
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCNIBEventQueue, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, prev_dag, 
                                                 seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerTEAddEdge(self) == /\ pc[self] = "ControllerTEAddEdge"
                             /\ IF setIRsInDAG[self] # {}
                                   THEN /\ TRUE
                                        /\ currIRInDAG' = [currIRInDAG EXCEPT ![self] = CHOOSE x \in setIRsInDAG[self]: TRUE]
                                        /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = setIRsInDAG[self] \ {currIRInDAG'[self]}]
                                        /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.e = nxtDAG[self].dag.e \cup {<<nxtRCIRID, currIRInDAG'[self]>>}]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                        /\ UNCHANGED nxtRCIRID
                                   ELSE /\ nxtRCIRID' = nxtRCIRID + 1
                                        /\ TRUE
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                        /\ UNCHANGED << nxtDAG, currIRInDAG, 
                                                        setIRsInDAG >>
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, DAGID, 
                                             MaxDAGID, DAGState, 
                                             RCNIBEventQueue, RCIRStatus, 
                                             RCSwSuspensionStatus, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, masterState, 
                                             controllerStateNIB, NIBIRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             setRemovableIRs, currIR, 
                                             nxtDAGVertices, prev_dag, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

ControllerTEUpdateSetScheduledIR(self) == /\ pc[self] = "ControllerTEUpdateSetScheduledIR"
                                          /\ SetScheduledIRs' = [x \in SW |-> (SetScheduledIRs[x] \ nxtDAG[self].dag.v)]
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLock, 
                                                          FirstInstall, 
                                                          sw_fail_ordering_var, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          irTypeMapping, ir2sw, 
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
                                                          RecoveryStatus, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGID, 
                                                          MaxDAGID, DAGState, 
                                                          RCNIBEventQueue, 
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          RCSeqWorkerStatus, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          ingressPkt, 
                                                          ingressIR, egressMsg, 
                                                          ofaInMsg, 
                                                          ofaOutConfirmation, 
                                                          installerInIR, 
                                                          statusMsg, 
                                                          notFailedSet, 
                                                          failedElem, obj, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          nxtDAG, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, seqEvent, 
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ TRUE
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddToDAGQueue"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstall, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, ir2sw, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  switchStatus, installedIRs, 
                                                  NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  RecoveryStatus, 
                                                  controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat, 
                                                  switchOrdering, TEEventQueue, 
                                                  DAGEventQueue, DAGQueue, 
                                                  DAGID, MaxDAGID, 
                                                  RCNIBEventQueue, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  RCSeqWorkerStatus, IRDoneSet, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  masterState, 
                                                  controllerStateNIB, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
                                                  statusResolveMsg, 
                                                  recoveredElem, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR, 
                                                  controllerFailedModules >>

ControllerTEAddToDAGQueue(self) == /\ pc[self] = "ControllerTEAddToDAGQueue"
                                   /\ DAGEventQueue' = [DAGEventQueue EXCEPT ![self[1]] = Append(DAGEventQueue[self[1]], [type |-> DAG_NEW, dag_obj |-> nxtDAG[self]])]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGQueue, 
                                                   DAGID, MaxDAGID, DAGState, 
                                                   RCNIBEventQueue, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ReadHeadTEEvent(self)
                                         \/ ComputeTopoUpdates(self)
                                         \/ RemoveFromTEEventQueue(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerUpdateDAGState(self)
                                         \/ ControllerTESendDagStaleNotif(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTEChooseOneIR(self)
                                         \/ ControllerTEAdjustRCState(self)
                                         \/ ControllerTEAdjustNIBIRStatusState(self)
                                         \/ ControllerTEIRMapping(self)
                                         \/ ControllerTEIRAddNodesDAG(self)
                                         \/ ControllerTEGetIrsInDAG(self)
                                         \/ ControllerTEAddEdge(self)
                                         \/ ControllerTEUpdateSetScheduledIR(self)
                                         \/ ControllerTESubmitNewDAG(self)
                                         \/ ControllerTEAddToDAGQueue(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ controllerIsMaster(self[1])
                               /\ moduleIsUp(self)
                               /\ DAGEventQueue[self[1]] # <<>>
                               /\ TRUE
                               /\ pc' = [pc EXCEPT ![self] = "ControllerBossDAGHead"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstall, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, ir2sw, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               RecoveryStatus, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, DAGID, 
                                               MaxDAGID, DAGState, 
                                               RCNIBEventQueue, RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
                                               RCSeqWorkerStatus, IRDoneSet, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               masterState, controllerStateNIB, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, currDAG, 
                                               IRSet, currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

ControllerBossDAGHead(self) == /\ pc[self] = "ControllerBossDAGHead"
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue[self[1]])]
                               /\ DAGEventQueue' = [DAGEventQueue EXCEPT ![self[1]] = Tail(DAGEventQueue[self[1]])]
                               /\ Assert(seqEvent'[self].type \in {DAG_NEW, DAG_STALE}, 
                                         "Failure of assertion at line 1724, column 9.")
                               /\ pc' = [pc EXCEPT ![self] = "ControllerBossCheckEventType"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstall, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, ir2sw, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               RecoveryStatus, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, TEEventQueue, 
                                               DAGQueue, DAGID, MaxDAGID, 
                                               DAGState, RCNIBEventQueue, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
                                               RCSeqWorkerStatus, IRDoneSet, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               masterState, controllerStateNIB, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, worker, 
                                               toBeScheduledIRs, nextIR, 
                                               stepOfFailure_, currDAG, IRSet, 
                                               currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

ControllerBossCheckEventType(self) == /\ pc[self] = "ControllerBossCheckEventType"
                                      /\ IF seqEvent[self].type = DAG_NEW
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerBossDAGSend"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerBossDAGTerminate"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      irTypeMapping, ir2sw, 
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
                                                      RecoveryStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      DAGID, MaxDAGID, 
                                                      DAGState, 
                                                      RCNIBEventQueue, 
                                                      RCIRStatus, 
                                                      RCSwSuspensionStatus, 
                                                      nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      RCSeqWorkerStatus, 
                                                      IRDoneSet, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      NIBIRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, event, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, 
                                                      nxtDAG, setRemovableIRs, 
                                                      currIR, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      removedIR, 
                                                      controllerFailedModules >>

ControllerBossDAGSend(self) == /\ pc[self] = "ControllerBossDAGSend"
                               /\ DAGQueue' = [DAGQueue EXCEPT ![self[1]] = Append(DAGQueue[self[1]], seqEvent[self].dag_obj)]
                               /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstall, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, ir2sw, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               RecoveryStatus, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, TEEventQueue, 
                                               DAGEventQueue, DAGID, MaxDAGID, 
                                               DAGState, RCNIBEventQueue, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
                                               RCSeqWorkerStatus, IRDoneSet, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               masterState, controllerStateNIB, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, currDAG, 
                                               IRSet, currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

ControllerBossDAGTerminate(self) == /\ pc[self] = "ControllerBossDAGTerminate"
                                    /\ worker' = [worker EXCEPT ![self] = idWorkerWorkingOnDAG[seqEvent[self].id]]
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerBossIfDAGUnlock"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    irTypeMapping, ir2sw, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    RecoveryStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    RCNIBEventQueue, 
                                                    RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    RCSeqWorkerStatus, 
                                                    IRDoneSet, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    obj, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, toBeScheduledIRs, 
                                                    nextIR, stepOfFailure_, 
                                                    currDAG, IRSet, currIRMon, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    removedIR, 
                                                    controllerFailedModules >>

ControllerBossIfDAGUnlock(self) == /\ pc[self] = "ControllerBossIfDAGUnlock"
                                   /\ IF worker[self] # DAG_UNLOCK
                                         THEN /\ pc' = [pc EXCEPT ![self] = "ControllerBossSendSignal"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerBossChangeDAGStateToNone"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCNIBEventQueue, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

ControllerBossSendSignal(self) == /\ pc[self] = "ControllerBossSendSignal"
                                  /\ RCSeqWorkerStatus' = [RCSeqWorkerStatus EXCEPT ![CONT_WORKER_SEQ] = SEQ_WORKER_STALE_SIGNAL]
                                  /\ pc' = [pc EXCEPT ![self] = "WaitForRCSeqWorkerTerminate"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstall, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, ir2sw, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  switchStatus, installedIRs, 
                                                  NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  RecoveryStatus, 
                                                  controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat, 
                                                  switchOrdering, TEEventQueue, 
                                                  DAGEventQueue, DAGQueue, 
                                                  DAGID, MaxDAGID, DAGState, 
                                                  RCNIBEventQueue, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  masterState, 
                                                  controllerStateNIB, 
                                                  NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
                                                  statusResolveMsg, 
                                                  recoveredElem, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR, 
                                                  controllerFailedModules >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ TRUE
                                     /\ idWorkerWorkingOnDAG[seqEvent[self].id] = DAG_UNLOCK
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossChangeDAGState"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     FirstInstall, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, ir2sw, 
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
                                                     RecoveryStatus, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     switchOrdering, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     masterState, 
                                                     controllerStateNIB, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     ingressPkt, ingressIR, 
                                                     egressMsg, ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     installerInIR, statusMsg, 
                                                     notFailedSet, failedElem, 
                                                     obj, failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

ControllerBossChangeDAGState(self) == /\ pc[self] = "ControllerBossChangeDAGState"
                                      /\ DAGState' = [DAGState EXCEPT ![seqEvent[self].id] = DAG_NONE]
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      irTypeMapping, ir2sw, 
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
                                                      RecoveryStatus, 
                                                      controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat, 
                                                      switchOrdering, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      DAGID, MaxDAGID, 
                                                      RCNIBEventQueue, 
                                                      RCIRStatus, 
                                                      RCSwSuspensionStatus, 
                                                      nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      RCSeqWorkerStatus, 
                                                      IRDoneSet, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      NIBIRStatus, 
                                                      SwSuspensionStatus, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem, event, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, 
                                                      nxtDAG, setRemovableIRs, 
                                                      currIR, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, rowIndex, 
                                                      rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      removedIR, 
                                                      controllerFailedModules >>

ControllerBossChangeDAGStateToNone(self) == /\ pc[self] = "ControllerBossChangeDAGStateToNone"
                                            /\ DAGState' = [DAGState EXCEPT ![seqEvent[self].id] = DAG_NONE]
                                            /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                            /\ UNCHANGED << switchLock, 
                                                            controllerLock, 
                                                            FirstInstall, 
                                                            sw_fail_ordering_var, 
                                                            ContProcSet, 
                                                            SwProcSet, 
                                                            irTypeMapping, 
                                                            ir2sw, 
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
                                                            RecoveryStatus, 
                                                            controllerSubmoduleFailNum, 
                                                            controllerSubmoduleFailStat, 
                                                            switchOrdering, 
                                                            TEEventQueue, 
                                                            DAGEventQueue, 
                                                            DAGQueue, DAGID, 
                                                            MaxDAGID, 
                                                            RCNIBEventQueue, 
                                                            RCIRStatus, 
                                                            RCSwSuspensionStatus, 
                                                            nxtRCIRID, 
                                                            idWorkerWorkingOnDAG, 
                                                            RCSeqWorkerStatus, 
                                                            IRDoneSet, 
                                                            idThreadWorkingOnIR, 
                                                            workerThreadRanking, 
                                                            masterState, 
                                                            controllerStateNIB, 
                                                            NIBIRStatus, 
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
                                                            failedElem, obj, 
                                                            failedSet, 
                                                            statusResolveMsg, 
                                                            recoveredElem, 
                                                            event, 
                                                            topoChangeEvent, 
                                                            currSetDownSw, 
                                                            prev_dag_id, init, 
                                                            nxtDAG, 
                                                            setRemovableIRs, 
                                                            currIR, 
                                                            currIRInDAG, 
                                                            nxtDAGVertices, 
                                                            setIRsInDAG, 
                                                            prev_dag, seqEvent, 
                                                            worker, 
                                                            toBeScheduledIRs, 
                                                            nextIR, 
                                                            stepOfFailure_, 
                                                            currDAG, IRSet, 
                                                            currIRMon, 
                                                            nextIRToSent, 
                                                            rowIndex, 
                                                            rowRemove, 
                                                            stepOfFailure_c, 
                                                            monitoringEvent, 
                                                            setIRsToReset, 
                                                            resetIR, 
                                                            stepOfFailure, msg, 
                                                            irID, removedIR, 
                                                            controllerFailedModules >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ ControllerBossDAGHead(self)
                                    \/ ControllerBossCheckEventType(self)
                                    \/ ControllerBossDAGSend(self)
                                    \/ ControllerBossDAGTerminate(self)
                                    \/ ControllerBossIfDAGUnlock(self)
                                    \/ ControllerBossSendSignal(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)
                                    \/ ControllerBossChangeDAGState(self)
                                    \/ ControllerBossChangeDAGStateToNone(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ controllerIsMaster(self[1])
                                 /\ moduleIsUp(self)
                                 /\ DAGQueue[self[1]] # <<>>
                                 /\ TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeq1"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCNIBEventQueue, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerWorkerSeq1(self) == /\ pc[self] = "ControllerWorkerSeq1"
                              /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue[self[1]])]
                              /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeq2"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, 
                                              RCNIBEventQueue, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, 
                                              RCSeqWorkerStatus, IRDoneSet, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, IRSet, currIRMon, 
                                              nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure_c, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, stepOfFailure, msg, 
                                              irID, removedIR, 
                                              controllerFailedModules >>

ControllerWorkerSeq2(self) == /\ pc[self] = "ControllerWorkerSeq2"
                              /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG[self].id] = self[2]]
                              /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, 
                                              RCNIBEventQueue, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              RCSeqWorkerStatus, IRDoneSet, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR, 
                                              controllerFailedModules >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF ~allIRsInDAGInstalled(self[1], currDAG[self].dag) /\ ~isDAGStale(currDAG[self].id)
                                              THEN /\ TRUE
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeq3"]
                                                   /\ UNCHANGED << idWorkerWorkingOnDAG, 
                                                                   RCSeqWorkerStatus, 
                                                                   IRSet >>
                                              ELSE /\ TRUE
                                                   /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG[self].id] = DAG_UNLOCK]
                                                   /\ RCSeqWorkerStatus' = [RCSeqWorkerStatus EXCEPT ![self[2]] = SEQ_WORKER_RUN]
                                                   /\ IRSet' = [IRSet EXCEPT ![self] = currDAG[self].dag.v]
                                                   /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                        /\ UNCHANGED << switchLock, 
                                                        controllerLock, 
                                                        FirstInstall, 
                                                        sw_fail_ordering_var, 
                                                        ContProcSet, SwProcSet, 
                                                        irTypeMapping, ir2sw, 
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
                                                        RecoveryStatus, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, DAGID, 
                                                        MaxDAGID, DAGState, 
                                                        RCNIBEventQueue, 
                                                        RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        nxtRCIRID, IRDoneSet, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        SetScheduledIRs, 
                                                        ingressPkt, ingressIR, 
                                                        egressMsg, ofaInMsg, 
                                                        ofaOutConfirmation, 
                                                        installerInIR, 
                                                        statusMsg, 
                                                        notFailedSet, 
                                                        failedElem, obj, 
                                                        failedSet, 
                                                        statusResolveMsg, 
                                                        recoveredElem, event, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        nxtDAG, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, worker, 
                                                        toBeScheduledIRs, 
                                                        nextIR, stepOfFailure_, 
                                                        currDAG, currIRMon, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        irID, removedIR, 
                                                        controllerFailedModules >>

ControllerWorkerSeq3(self) == /\ pc[self] = "ControllerWorkerSeq3"
                              /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1], currDAG[self].dag)]
                              /\ isDAGStale(currDAG[self].id) \/ toBeScheduledIRs'[self] # {}
                              /\ IF isDAGStale(currDAG[self].id)
                                    THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, 
                                              RCNIBEventQueue, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, 
                                              RCSeqWorkerStatus, IRDoneSet, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, nextIR, stepOfFailure_, 
                                              currDAG, IRSet, currIRMon, 
                                              nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure_c, 
                                              monitoringEvent, setIRsToReset, 
                                              resetIR, stepOfFailure, msg, 
                                              irID, removedIR, 
                                              controllerFailedModules >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ TRUE
                            /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                  THEN /\ \E num \in 0..3:
                                            stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                                  ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                            /\ IF (stepOfFailure_'[self] # 1)
                                  THEN /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                                       /\ IF (stepOfFailure_'[self] # 2)
                                             THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_START_SCHEDULING, next |-> nextIR'[self]]]
                                                  /\ IF (stepOfFailure_'[self] # 3)
                                                        THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[nextIR'[self]]] = SetScheduledIRs[ir2sw[nextIR'[self]]] \cup {nextIR'[self]}]
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
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "AddDeleteIRIRDoneSet"]
                                       /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat >>
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstall, sw_fail_ordering_var, 
                                            ContProcSet, SwProcSet, 
                                            irTypeMapping, ir2sw, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            switchOrdering, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, DAGID, 
                                            MaxDAGID, DAGState, 
                                            RCNIBEventQueue, RCIRStatus, 
                                            RCSwSuspensionStatus, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, 
                                            RCSeqWorkerStatus, IRDoneSet, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, masterState, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            IRQueueNIB, ingressPkt, ingressIR, 
                                            egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, obj, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            event, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            nxtDAG, setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, currDAG, 
                                            IRSet, currIRMon, nextIRToSent, 
                                            rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, irID, 
                                            removedIR, controllerFailedModules >>

AddDeleteIRIRDoneSet(self) == /\ pc[self] = "AddDeleteIRIRDoneSet"
                              /\ TRUE
                              /\ IF irTypeMapping[nextIR[self]].type = INSTALL_FLOW
                                    THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \cup {nextIR[self]}]
                                    ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR[self]].flow, INSTALLED_SUCCESSFULLY)}]
                              /\ pc' = [pc EXCEPT ![self] = "ScheduleTheIR"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, 
                                              RCNIBEventQueue, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, 
                                              RCSeqWorkerStatus, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR, 
                                              controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ TRUE
                       /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                             THEN /\ \E num \in 0..2:
                                       stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                             ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                       /\ IF (stepOfFailure_'[self] # 1)
                             THEN /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> nextIR[self], tag |-> NO_TAG])
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
                             ELSE /\ IF toBeScheduledIRs'[self] = {} \/ isDAGStale(currDAG[self].id)
                                        THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                  /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat >>
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstall, sw_fail_ordering_var, 
                                       ContProcSet, SwProcSet, irTypeMapping, 
                                       ir2sw, swSeqChangedStatus, 
                                       controller2Switch, switch2Controller, 
                                       switchStatus, installedIRs, 
                                       NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                       Installer2OfaBuff, Ofa2InstallerBuff, 
                                       TCAM, controlMsgCounter, RecoveryStatus, 
                                       switchOrdering, TEEventQueue, 
                                       DAGEventQueue, DAGQueue, DAGID, 
                                       MaxDAGID, DAGState, RCNIBEventQueue, 
                                       RCIRStatus, RCSwSuspensionStatus, 
                                       nxtRCIRID, idWorkerWorkingOnDAG, 
                                       RCSeqWorkerStatus, IRDoneSet, 
                                       idThreadWorkingOnIR, 
                                       workerThreadRanking, masterState, 
                                       NIBIRStatus, SwSuspensionStatus, 
                                       SetScheduledIRs, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, obj, failedSet, 
                                       statusResolveMsg, recoveredElem, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, nxtDAG, 
                                       setRemovableIRs, currIR, currIRInDAG, 
                                       nxtDAGVertices, setIRsInDAG, prev_dag, 
                                       seqEvent, worker, nextIR, currDAG, 
                                       IRSet, currIRMon, nextIRToSent, 
                                       rowIndex, rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, irID, removedIR, 
                                       controllerFailedModules >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {} /\ allIRsInDAGInstalled(self[1], currDAG[self].dag)
                                     THEN /\ TRUE
                                          /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF irTypeMapping[nextIR'[self]].type = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \cup {nextIR'[self]}]
                                                ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR'[self]].flow, INSTALLED_SUCCESSFULLY)}]
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                          /\ UNCHANGED DAGQueue
                                     ELSE /\ TRUE
                                          /\ DAGQueue' = [DAGQueue EXCEPT ![self[1]] = Tail(DAGQueue[self[1]])]
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << IRDoneSet, nextIR, 
                                                          IRSet >>
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstall, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, ir2sw, 
                                               swSeqChangedStatus, 
                                               controller2Switch, 
                                               switch2Controller, switchStatus, 
                                               installedIRs, NicAsic2OfaBuff, 
                                               Ofa2NicAsicBuff, 
                                               Installer2OfaBuff, 
                                               Ofa2InstallerBuff, TCAM, 
                                               controlMsgCounter, 
                                               RecoveryStatus, 
                                               controllerSubmoduleFailNum, 
                                               controllerSubmoduleFailStat, 
                                               switchOrdering, TEEventQueue, 
                                               DAGEventQueue, DAGID, MaxDAGID, 
                                               DAGState, RCNIBEventQueue, 
                                               RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
                                               RCSeqWorkerStatus, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               masterState, controllerStateNIB, 
                                               NIBIRStatus, SwSuspensionStatus, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, event, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               stepOfFailure_, currDAG, 
                                               currIRMon, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, removedIR, 
                                               controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ controllerIsMaster(self[1])
                                          /\ moduleIsUp(self)
                                          /\ TRUE
                                          /\ IF (controllerStateNIB[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[controllerStateNIB[self].next]] = SetScheduledIRs[ir2sw[controllerStateNIB[self].next]]\{controllerStateNIB[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLock, 
                                                          FirstInstall, 
                                                          sw_fail_ordering_var, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          irTypeMapping, ir2sw, 
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
                                                          RecoveryStatus, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGID, 
                                                          MaxDAGID, DAGState, 
                                                          RCNIBEventQueue, 
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          RCSeqWorkerStatus, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          NIBIRStatus, 
                                                          SwSuspensionStatus, 
                                                          IRQueueNIB, 
                                                          ingressPkt, 
                                                          ingressIR, egressMsg, 
                                                          ofaInMsg, 
                                                          ofaOutConfirmation, 
                                                          installerInIR, 
                                                          statusMsg, 
                                                          notFailedSet, 
                                                          failedElem, obj, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          nxtDAG, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, seqEvent, 
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeq1(self)
                                \/ ControllerWorkerSeq2(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ ControllerWorkerSeq3(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteIRIRDoneSet(self)
                                \/ ScheduleTheIR(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ ControllerSeqStateReconciliation(self)

controllerIRMonitor(self) == /\ pc[self] = "controllerIRMonitor"
                             /\ controllerIsMaster(self[1])
                             /\ moduleIsUp(self)
                             /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor1"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, DAGID, 
                                             MaxDAGID, DAGState, 
                                             RCNIBEventQueue, RCIRStatus, 
                                             RCSwSuspensionStatus, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, masterState, 
                                             controllerStateNIB, NIBIRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             nxtDAG, setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

rcIRMonitor1(self) == /\ pc[self] = "rcIRMonitor1"
                      /\ setIRMonitorShouldSchedule(self[1]) # {}
                      /\ currIRMon' = [currIRMon EXCEPT ![self] = CHOOSE x \in setIRMonitorShouldSchedule(self[1]): TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor2"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      nextIRToSent, rowIndex, rowRemove, 
                                      stepOfFailure_c, monitoringEvent, 
                                      setIRsToReset, resetIR, stepOfFailure, 
                                      msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor2(self) == /\ pc[self] = "rcIRMonitor2"
                      /\ IF currIRMon[self] \in IRDoneSet[self[1]]
                            THEN /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor3"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor5"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor3(self) == /\ pc[self] = "rcIRMonitor3"
                      /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[currIRMon[self]]] = SetScheduledIRs[ir2sw[currIRMon[self]]] \cup {currIRMon[self]}]
                      /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor4"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      ingressPkt, ingressIR, egressMsg, 
                                      ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor4(self) == /\ pc[self] = "rcIRMonitor4"
                      /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> currIRMon[self], tag |-> NO_TAG])
                      /\ pc' = [pc EXCEPT ![self] = "controllerIRMonitor"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, SetScheduledIRs, 
                                      ingressPkt, ingressIR, egressMsg, 
                                      ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor5(self) == /\ pc[self] = "rcIRMonitor5"
                      /\ RCIRStatus' = [RCIRStatus EXCEPT ![self[1]] = RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE)]
                      /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor6"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor6(self) == /\ pc[self] = "rcIRMonitor6"
                      /\ NIBIRStatus' = NIBIRStatus @@ (nxtRCIRID :> IR_NONE)
                      /\ FirstInstall' = FirstInstall @@ (nxtRCIRID :> 0)
                      /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor7"]
                      /\ UNCHANGED << switchLock, controllerLock, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, SwSuspensionStatus, 
                                      IRQueueNIB, SetScheduledIRs, ingressPkt, 
                                      ingressIR, egressMsg, ofaInMsg, 
                                      ofaOutConfirmation, installerInIR, 
                                      statusMsg, notFailedSet, failedElem, obj, 
                                      failedSet, statusResolveMsg, 
                                      recoveredElem, event, topoChangeEvent, 
                                      currSetDownSw, prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor7(self) == /\ pc[self] = "rcIRMonitor7"
                      /\ irTypeMapping' = irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIRMon[self]]])
                      /\ ir2sw' = ir2sw @@ (nxtRCIRID :> ir2sw[currIRMon[self]])
                      /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor8"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, swSeqChangedStatus, 
                                      controller2Switch, switch2Controller, 
                                      switchStatus, installedIRs, 
                                      NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                      Installer2OfaBuff, Ofa2InstallerBuff, 
                                      TCAM, controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor8(self) == /\ pc[self] = "rcIRMonitor8"
                      /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[nxtRCIRID]] = SetScheduledIRs[ir2sw[nxtRCIRID]] \cup {nxtRCIRID}]
                      /\ pc' = [pc EXCEPT ![self] = "rcIRMonitor9"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      ingressPkt, ingressIR, egressMsg, 
                                      ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor9(self) == /\ pc[self] = "rcIRMonitor9"
                      /\ IRQueueNIB' = Append(IRQueueNIB, [IR |-> nxtRCIRID, tag |-> NO_TAG])
                      /\ nxtRCIRID' = nxtRCIRID + 1
                      /\ pc' = [pc EXCEPT ![self] = "controllerIRMonitor"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, SetScheduledIRs, 
                                      ingressPkt, ingressIR, egressMsg, 
                                      ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

rcIRMonitor(self) == controllerIRMonitor(self) \/ rcIRMonitor1(self)
                        \/ rcIRMonitor2(self) \/ rcIRMonitor3(self)
                        \/ rcIRMonitor4(self) \/ rcIRMonitor5(self)
                        \/ rcIRMonitor6(self) \/ rcIRMonitor7(self)
                        \/ rcIRMonitor8(self) \/ rcIRMonitor9(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerIsMaster(self[1])
                          /\ moduleIsUp(self)
                          /\ IRQueueNIB # <<>>
                          /\ canWorkerThreadContinue(self[1], self)
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThread1"]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstall, sw_fail_ordering_var, 
                                          ContProcSet, SwProcSet, 
                                          irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, TEEventQueue, 
                                          DAGEventQueue, DAGQueue, DAGID, 
                                          MaxDAGID, DAGState, RCNIBEventQueue, 
                                          RCIRStatus, RCSwSuspensionStatus, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          RCSeqWorkerStatus, IRDoneSet, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, masterState, 
                                          controllerStateNIB, NIBIRStatus, 
                                          SwSuspensionStatus, IRQueueNIB, 
                                          SetScheduledIRs, ingressPkt, 
                                          ingressIR, egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          obj, failedSet, statusResolveMsg, 
                                          recoveredElem, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, seqEvent, worker, 
                                          toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, rowIndex, 
                                          rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          removedIR, controllerFailedModules >>

ControllerThread1(self) == /\ pc[self] = "ControllerThread1"
                           /\ existIRIndexToRead(self)
                           /\ IRQueueNIB # <<>>
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
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThread2"]
                                      /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat >>
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           irTypeMapping, ir2sw, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, RecoveryStatus, 
                                           switchOrdering, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, DAGID, 
                                           MaxDAGID, DAGState, RCNIBEventQueue, 
                                           RCIRStatus, RCSwSuspensionStatus, 
                                           nxtRCIRID, idWorkerWorkingOnDAG, 
                                           RCSeqWorkerStatus, IRDoneSet, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, masterState, 
                                           controllerStateNIB, NIBIRStatus, 
                                           SwSuspensionStatus, SetScheduledIRs, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, obj, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, currDAG, IRSet, 
                                           currIRMon, rowRemove, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure, msg, irID, 
                                           removedIR, controllerFailedModules >>

ControllerThread2(self) == /\ pc[self] = "ControllerThread2"
                           /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_LOCKING, next |-> nextIRToSent[self]]]
                           /\ IF (stepOfFailure_c[self] = 2)
                                 THEN /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                      /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThread3"]
                                      /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                      controllerSubmoduleFailStat >>
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           irTypeMapping, ir2sw, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, RecoveryStatus, 
                                           switchOrdering, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, DAGID, 
                                           MaxDAGID, DAGState, RCNIBEventQueue, 
                                           RCIRStatus, RCSwSuspensionStatus, 
                                           nxtRCIRID, idWorkerWorkingOnDAG, 
                                           RCSeqWorkerStatus, IRDoneSet, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, masterState, 
                                           NIBIRStatus, SwSuspensionStatus, 
                                           IRQueueNIB, SetScheduledIRs, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, obj, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, currDAG, IRSet, 
                                           currIRMon, nextIRToSent, rowIndex, 
                                           rowRemove, stepOfFailure_c, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure, msg, irID, 
                                           removedIR, controllerFailedModules >>

ControllerThread3(self) == /\ pc[self] = "ControllerThread3"
                           /\ IF idThreadWorkingOnIR[nextIRToSent[self]] = IR_UNLOCK
                                 THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent[self]] = self[2]]
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadWaitForIRUnlock"]
                                      /\ UNCHANGED idThreadWorkingOnIR
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           irTypeMapping, ir2sw, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, RecoveryStatus, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, DAGID, 
                                           MaxDAGID, DAGState, RCNIBEventQueue, 
                                           RCIRStatus, RCSwSuspensionStatus, 
                                           nxtRCIRID, idWorkerWorkingOnDAG, 
                                           RCSeqWorkerStatus, IRDoneSet, 
                                           workerThreadRanking, masterState, 
                                           controllerStateNIB, NIBIRStatus, 
                                           SwSuspensionStatus, IRQueueNIB, 
                                           SetScheduledIRs, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           obj, failedSet, statusResolveMsg, 
                                           recoveredElem, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, currDAG, IRSet, 
                                           currIRMon, nextIRToSent, rowIndex, 
                                           rowRemove, stepOfFailure_c, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure, msg, irID, 
                                           removedIR, controllerFailedModules >>

ControllerThreadWaitForIRUnlock(self) == /\ pc[self] = "ControllerThreadWaitForIRUnlock"
                                         /\ TRUE
                                         /\ idThreadWorkingOnIR[nextIRToSent[self]] = IR_UNLOCK
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         sw_fail_ordering_var, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         irTypeMapping, ir2sw, 
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
                                                         RecoveryStatus, 
                                                         controllerSubmoduleFailNum, 
                                                         controllerSubmoduleFailStat, 
                                                         switchOrdering, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, DAGID, 
                                                         MaxDAGID, DAGState, 
                                                         RCNIBEventQueue, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         nxtRCIRID, 
                                                         idWorkerWorkingOnDAG, 
                                                         RCSeqWorkerStatus, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, obj, 
                                                         failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
                                                         controllerFailedModules >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ TRUE
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
                                      THEN /\ IF ~isSwitchSuspended(ir2sw[nextIRToSent[self]]) /\ NIBIRStatus[nextIRToSent[self]] = IR_NONE
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR1"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, ir2sw, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                RecoveryStatus, switchOrdering, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, DAGID, MaxDAGID, 
                                                DAGState, RCNIBEventQueue, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                RCSeqWorkerStatus, IRDoneSet, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                masterState, 
                                                controllerStateNIB, 
                                                NIBIRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, nxtDAG, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR, 
                                                controllerFailedModules >>

ControllerThreadSendIR1(self) == /\ pc[self] = "ControllerThreadSendIR1"
                                 /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![nextIRToSent[self]] = IR_SENT]
                                 /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> nextIRToSent[self], state |-> IR_SENT])]
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ TRUE
                                   /\ Assert(irTypeMapping[nextIRToSent[self]].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                             "Failure of assertion at line 956, column 9 of macro called at line 1999, column 29.")
                                   /\ Assert(irTypeMapping[nextIRToSent[self]].flow \in 1..MaxNumFlows, 
                                             "Failure of assertion at line 957, column 9 of macro called at line 1999, column 29.")
                                   /\ controller2Switch' = [controller2Switch EXCEPT ![ir2sw[nextIRToSent[self]]] = Append(controller2Switch[ir2sw[nextIRToSent[self]]], [type |-> irTypeMapping[nextIRToSent[self]].type,
                                                                                                                                                                          to |-> ir2sw[nextIRToSent[self]],
                                                                                                                                                                          flow |-> irTypeMapping[nextIRToSent[self]].flow])]
                                   /\ IF whichSwitchModel(ir2sw[nextIRToSent[self]]) = SW_COMPLEX_MODEL
                                         THEN /\ switchLock' = <<NIC_ASIC_IN, ir2sw[nextIRToSent[self]]>>
                                         ELSE /\ switchLock' = <<SW_SIMPLE_ID, ir2sw[nextIRToSent[self]]>>
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR1"]
                                   /\ UNCHANGED << controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCNIBEventQueue, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

ControllerThreadForwardIR1(self) == /\ pc[self] = "ControllerThreadForwardIR1"
                                    /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> STATUS_SENT_DONE, next |-> nextIRToSent[self]]]
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    irTypeMapping, ir2sw, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    RecoveryStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    RCNIBEventQueue, 
                                                    RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    RCSeqWorkerStatus, 
                                                    IRDoneSet, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    masterState, NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    obj, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    removedIR, 
                                                    controllerFailedModules >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
                                         /\ TRUE
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
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore1"]
                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                         /\ UNCHANGED << switchLock, 
                                                         controllerLock, 
                                                         FirstInstall, 
                                                         sw_fail_ordering_var, 
                                                         ContProcSet, 
                                                         SwProcSet, 
                                                         irTypeMapping, ir2sw, 
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
                                                         RecoveryStatus, 
                                                         switchOrdering, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, DAGID, 
                                                         MaxDAGID, DAGState, 
                                                         RCNIBEventQueue, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         nxtRCIRID, 
                                                         idWorkerWorkingOnDAG, 
                                                         RCSeqWorkerStatus, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, obj, 
                                                         failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
                                                         controllerFailedModules >>

ControllerThreadUnlockSemaphore1(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore1"
                                          /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![nextIRToSent[self]] = IR_UNLOCK]
                                          /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLock, 
                                                          FirstInstall, 
                                                          sw_fail_ordering_var, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          irTypeMapping, ir2sw, 
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
                                                          RecoveryStatus, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGID, 
                                                          MaxDAGID, DAGState, 
                                                          RCNIBEventQueue, 
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          RCSeqWorkerStatus, 
                                                          IRDoneSet, 
                                                          workerThreadRanking, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          NIBIRStatus, 
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
                                                          failedElem, obj, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          nxtDAG, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, seqEvent, 
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ TRUE
                                  /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                  /\ pc' = [pc EXCEPT ![self] = "RemoveFromScheduledIRSet1"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstall, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, ir2sw, 
                                                  swSeqChangedStatus, 
                                                  controller2Switch, 
                                                  switch2Controller, 
                                                  switchStatus, installedIRs, 
                                                  NicAsic2OfaBuff, 
                                                  Ofa2NicAsicBuff, 
                                                  Installer2OfaBuff, 
                                                  Ofa2InstallerBuff, TCAM, 
                                                  controlMsgCounter, 
                                                  RecoveryStatus, 
                                                  controllerSubmoduleFailNum, 
                                                  controllerSubmoduleFailStat, 
                                                  switchOrdering, TEEventQueue, 
                                                  DAGEventQueue, DAGQueue, 
                                                  DAGID, MaxDAGID, DAGState, 
                                                  RCNIBEventQueue, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  RCSeqWorkerStatus, IRDoneSet, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  masterState, NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
                                                  statusResolveMsg, 
                                                  recoveredElem, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  removedIR, 
                                                  controllerFailedModules >>

RemoveFromScheduledIRSet1(self) == /\ pc[self] = "RemoveFromScheduledIRSet1"
                                   /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(nextIRToSent[self], self)]
                                   /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCNIBEventQueue, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   SetScheduledIRs, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ controllerIsMaster(self[1])
                                             /\ moduleIsUp(self)
                                             /\ IRQueueNIB # <<>>
                                             /\ canWorkerThreadContinue(self[1], self)
                                             /\ TRUE
                                             /\ IF (controllerStateNIB[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (NIBIRStatus[controllerStateNIB[self].next] = IR_SENT)
                                                              THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![controllerStateNIB[self].next] = IR_NONE]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED NIBIRStatus
                                                        /\ IF (idThreadWorkingOnIR[controllerStateNIB[self].next] = self[2])
                                                              THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![controllerStateNIB[self].next] = IR_UNLOCK]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                   ELSE /\ IF (controllerStateNIB[self].type = STATUS_SENT_DONE)
                                                              THEN /\ IF (idThreadWorkingOnIR[controllerStateNIB[self].next] = self[2])
                                                                         THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![controllerStateNIB[self].next] = IR_UNLOCK]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED idThreadWorkingOnIR
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED idThreadWorkingOnIR
                                                        /\ UNCHANGED NIBIRStatus
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << switchLock, 
                                                             controllerLock, 
                                                             FirstInstall, 
                                                             sw_fail_ordering_var, 
                                                             ContProcSet, 
                                                             SwProcSet, 
                                                             irTypeMapping, 
                                                             ir2sw, 
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
                                                             RecoveryStatus, 
                                                             controllerSubmoduleFailNum, 
                                                             controllerSubmoduleFailStat, 
                                                             switchOrdering, 
                                                             TEEventQueue, 
                                                             DAGEventQueue, 
                                                             DAGQueue, DAGID, 
                                                             MaxDAGID, 
                                                             DAGState, 
                                                             RCNIBEventQueue, 
                                                             RCIRStatus, 
                                                             RCSwSuspensionStatus, 
                                                             nxtRCIRID, 
                                                             idWorkerWorkingOnDAG, 
                                                             RCSeqWorkerStatus, 
                                                             IRDoneSet, 
                                                             workerThreadRanking, 
                                                             masterState, 
                                                             controllerStateNIB, 
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
                                                             failedElem, obj, 
                                                             failedSet, 
                                                             statusResolveMsg, 
                                                             recoveredElem, 
                                                             event, 
                                                             topoChangeEvent, 
                                                             currSetDownSw, 
                                                             prev_dag_id, init, 
                                                             nxtDAG, 
                                                             setRemovableIRs, 
                                                             currIR, 
                                                             currIRInDAG, 
                                                             nxtDAGVertices, 
                                                             setIRsInDAG, 
                                                             prev_dag, 
                                                             seqEvent, worker, 
                                                             toBeScheduledIRs, 
                                                             nextIR, 
                                                             stepOfFailure_, 
                                                             currDAG, IRSet, 
                                                             currIRMon, 
                                                             nextIRToSent, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             stepOfFailure_c, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, 
                                                             stepOfFailure, 
                                                             msg, irID, 
                                                             removedIR, 
                                                             controllerFailedModules >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThread1(self)
                                    \/ ControllerThread2(self)
                                    \/ ControllerThread3(self)
                                    \/ ControllerThreadWaitForIRUnlock(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadSendIR1(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadForwardIR1(self)
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ ControllerThreadUnlockSemaphore1(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ RemoveFromScheduledIRSet1(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerIsMaster(self[1])
                                    /\ moduleIsUp(self)
                                    /\ swSeqChangedStatus # <<>>
                                    /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc1"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    irTypeMapping, ir2sw, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    RecoveryStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    RCNIBEventQueue, 
                                                    RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    RCSeqWorkerStatus, 
                                                    IRDoneSet, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    NIBIRStatus, 
                                                    SwSuspensionStatus, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    obj, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    removedIR, 
                                                    controllerFailedModules >>

ControllerEventHandlerProc1(self) == /\ pc[self] = "ControllerEventHandlerProc1"
                                     /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc2"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     FirstInstall, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, ir2sw, 
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
                                                     RecoveryStatus, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     switchOrdering, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     masterState, 
                                                     controllerStateNIB, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     ingressPkt, ingressIR, 
                                                     egressMsg, ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     installerInIR, statusMsg, 
                                                     notFailedSet, failedElem, 
                                                     obj, failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

ControllerEventHandlerProc2(self) == /\ pc[self] = "ControllerEventHandlerProc2"
                                     /\ IF shouldSuspendSw(monitoringEvent[self]) /\ SwSuspensionStatus[monitoringEvent[self].swID] = SW_RUN
                                           THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                           ELSE /\ IF canfreeSuspendedSw(monitoringEvent[self]) /\ SwSuspensionStatus[monitoringEvent[self].swID] = SW_SUSPEND
                                                      THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                     /\ UNCHANGED << switchLock, 
                                                     controllerLock, 
                                                     FirstInstall, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, ir2sw, 
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
                                                     RecoveryStatus, 
                                                     controllerSubmoduleFailNum, 
                                                     controllerSubmoduleFailStat, 
                                                     switchOrdering, 
                                                     TEEventQueue, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     masterState, 
                                                     controllerStateNIB, 
                                                     NIBIRStatus, 
                                                     SwSuspensionStatus, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     ingressPkt, ingressIR, 
                                                     egressMsg, ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     installerInIR, statusMsg, 
                                                     notFailedSet, failedElem, 
                                                     obj, failedSet, 
                                                     statusResolveMsg, 
                                                     recoveredElem, event, 
                                                     topoChangeEvent, 
                                                     currSetDownSw, 
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     removedIR, 
                                                     controllerFailedModules >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ TRUE
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
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW1"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED SwSuspensionStatus
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             switchOrdering, TEEventQueue, 
                                             DAGEventQueue, DAGQueue, DAGID, 
                                             MaxDAGID, DAGState, 
                                             RCNIBEventQueue, RCIRStatus, 
                                             RCSwSuspensionStatus, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, masterState, 
                                             controllerStateNIB, NIBIRStatus, 
                                             IRQueueNIB, SetScheduledIRs, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, obj, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, event, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, rowIndex, 
                                             rowRemove, stepOfFailure_c, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, msg, irID, 
                                             removedIR, 
                                             controllerFailedModules >>

ControllerSuspendSW1(self) == /\ pc[self] = "ControllerSuspendSW1"
                              /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                               sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND])]
                              /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstall, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, ir2sw, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, RCIRStatus, 
                                              RCSwSuspensionStatus, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, 
                                              RCSeqWorkerStatus, IRDoneSet, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, event, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, 
                                              removedIR, 
                                              controllerFailedModules >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ TRUE
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
                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                          /\ UNCHANGED << switchLock, 
                                                          controllerLock, 
                                                          FirstInstall, 
                                                          sw_fail_ordering_var, 
                                                          ContProcSet, 
                                                          SwProcSet, 
                                                          irTypeMapping, ir2sw, 
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
                                                          RecoveryStatus, 
                                                          switchOrdering, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGID, 
                                                          MaxDAGID, DAGState, 
                                                          RCNIBEventQueue, 
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          RCSeqWorkerStatus, 
                                                          IRDoneSet, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          NIBIRStatus, 
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
                                                          failedElem, obj, 
                                                          failedSet, 
                                                          statusResolveMsg, 
                                                          recoveredElem, event, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          nxtDAG, 
                                                          setRemovableIRs, 
                                                          currIR, currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          setIRsInDAG, 
                                                          prev_dag, seqEvent, 
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, removedIR, 
                                                          controllerFailedModules >>

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ TRUE
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
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                      /\ UNCHANGED setIRsToReset
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstall, sw_fail_ordering_var, 
                                           ContProcSet, SwProcSet, 
                                           irTypeMapping, ir2sw, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, RecoveryStatus, 
                                           switchOrdering, TEEventQueue, 
                                           DAGEventQueue, DAGQueue, DAGID, 
                                           MaxDAGID, DAGState, RCNIBEventQueue, 
                                           RCIRStatus, RCSwSuspensionStatus, 
                                           nxtRCIRID, idWorkerWorkingOnDAG, 
                                           RCSeqWorkerStatus, IRDoneSet, 
                                           idThreadWorkingOnIR, 
                                           workerThreadRanking, masterState, 
                                           controllerStateNIB, NIBIRStatus, 
                                           SwSuspensionStatus, IRQueueNIB, 
                                           SetScheduledIRs, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           obj, failedSet, statusResolveMsg, 
                                           recoveredElem, event, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, seqEvent, 
                                           worker, toBeScheduledIRs, nextIR, 
                                           stepOfFailure_, currDAG, IRSet, 
                                           currIRMon, nextIRToSent, rowIndex, 
                                           rowRemove, stepOfFailure_c, 
                                           monitoringEvent, resetIR, 
                                           stepOfFailure, msg, irID, removedIR, 
                                           controllerFailedModules >>

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ TRUE
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
                                /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs1"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                /\ UNCHANGED resetIR
                     /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                     sw_fail_ordering_var, ContProcSet, 
                                     SwProcSet, irTypeMapping, ir2sw, 
                                     swSeqChangedStatus, controller2Switch, 
                                     switch2Controller, switchStatus, 
                                     installedIRs, NicAsic2OfaBuff, 
                                     Ofa2NicAsicBuff, Installer2OfaBuff, 
                                     Ofa2InstallerBuff, TCAM, 
                                     controlMsgCounter, RecoveryStatus, 
                                     switchOrdering, TEEventQueue, 
                                     DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                     DAGState, RCNIBEventQueue, RCIRStatus, 
                                     RCSwSuspensionStatus, nxtRCIRID, 
                                     idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                     IRDoneSet, idThreadWorkingOnIR, 
                                     workerThreadRanking, masterState, 
                                     controllerStateNIB, NIBIRStatus, 
                                     SwSuspensionStatus, IRQueueNIB, 
                                     SetScheduledIRs, ingressPkt, ingressIR, 
                                     egressMsg, ofaInMsg, ofaOutConfirmation, 
                                     installerInIR, statusMsg, notFailedSet, 
                                     failedElem, obj, failedSet, 
                                     statusResolveMsg, recoveredElem, event, 
                                     topoChangeEvent, currSetDownSw, 
                                     prev_dag_id, init, nxtDAG, 
                                     setRemovableIRs, currIR, currIRInDAG, 
                                     nxtDAGVertices, setIRsInDAG, prev_dag, 
                                     seqEvent, worker, toBeScheduledIRs, 
                                     nextIR, stepOfFailure_, currDAG, IRSet, 
                                     currIRMon, nextIRToSent, rowIndex, 
                                     rowRemove, stepOfFailure_c, 
                                     monitoringEvent, setIRsToReset, 
                                     stepOfFailure, msg, irID, removedIR, 
                                     controllerFailedModules >>

ResetAllIRs1(self) == /\ pc[self] = "ResetAllIRs1"
                      /\ setIRsToReset' = [setIRsToReset EXCEPT ![self] = setIRsToReset[self] \ {resetIR[self]}]
                      /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs2"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCNIBEventQueue, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, NIBIRStatus, 
                                      SwSuspensionStatus, IRQueueNIB, 
                                      SetScheduledIRs, ingressPkt, ingressIR, 
                                      egressMsg, ofaInMsg, ofaOutConfirmation, 
                                      installerInIR, statusMsg, notFailedSet, 
                                      failedElem, obj, failedSet, 
                                      statusResolveMsg, recoveredElem, event, 
                                      topoChangeEvent, currSetDownSw, 
                                      prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, resetIR, stepOfFailure, 
                                      msg, irID, removedIR, 
                                      controllerFailedModules >>

ResetAllIRs2(self) == /\ pc[self] = "ResetAllIRs2"
                      /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR[self]] = IR_NONE]
                      /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0],
                                                                                 [type |-> IR_MOD, IR |-> resetIR[self], state |-> IR_NONE])]
                      /\ IF setIRsToReset[self] = {}
                            THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]
                      /\ UNCHANGED << switchLock, controllerLock, FirstInstall, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, ir2sw, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, TEEventQueue, 
                                      DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                      DAGState, RCIRStatus, 
                                      RCSwSuspensionStatus, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, RCSeqWorkerStatus, 
                                      IRDoneSet, idThreadWorkingOnIR, 
                                      workerThreadRanking, masterState, 
                                      controllerStateNIB, SwSuspensionStatus, 
                                      IRQueueNIB, SetScheduledIRs, ingressPkt, 
                                      ingressIR, egressMsg, ofaInMsg, 
                                      ofaOutConfirmation, installerInIR, 
                                      statusMsg, notFailedSet, failedElem, obj, 
                                      failedSet, statusResolveMsg, 
                                      recoveredElem, event, topoChangeEvent, 
                                      currSetDownSw, prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      seqEvent, worker, toBeScheduledIRs, 
                                      nextIR, stepOfFailure_, currDAG, IRSet, 
                                      currIRMon, nextIRToSent, rowIndex, 
                                      rowRemove, stepOfFailure_c, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, msg, irID, removedIR, 
                                      controllerFailedModules >>

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ TRUE
                                   /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> START_RESET_IR, sw |-> monitoringEvent[self].swID]]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW1"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   controllerSubmoduleFailNum, 
                                                   controllerSubmoduleFailStat, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCNIBEventQueue, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, NIBIRStatus, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

ControllerFreeSuspendedSW1(self) == /\ pc[self] = "ControllerFreeSuspendedSW1"
                                    /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                    /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                                                       sw |-> monitoringEvent[self].swID, state |-> SW_RUN])]
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstall, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    irTypeMapping, ir2sw, 
                                                    swSeqChangedStatus, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, installedIRs, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, TCAM, 
                                                    controlMsgCounter, 
                                                    RecoveryStatus, 
                                                    controllerSubmoduleFailNum, 
                                                    controllerSubmoduleFailStat, 
                                                    switchOrdering, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    RCIRStatus, 
                                                    RCSwSuspensionStatus, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    RCSeqWorkerStatus, 
                                                    IRDoneSet, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    masterState, 
                                                    controllerStateNIB, 
                                                    NIBIRStatus, IRQueueNIB, 
                                                    SetScheduledIRs, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    obj, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem, event, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    removedIR, 
                                                    controllerFailedModules >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ TRUE
                                                   /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue1"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   controllerLock, 
                                                                   FirstInstall, 
                                                                   sw_fail_ordering_var, 
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   irTypeMapping, 
                                                                   ir2sw, 
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
                                                                   RecoveryStatus, 
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   switchOrdering, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   DAGID, 
                                                                   MaxDAGID, 
                                                                   DAGState, 
                                                                   RCNIBEventQueue, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   nxtRCIRID, 
                                                                   idWorkerWorkingOnDAG, 
                                                                   RCSeqWorkerStatus, 
                                                                   IRDoneSet, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   masterState, 
                                                                   NIBIRStatus, 
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
                                                                   obj, 
                                                                   failedSet, 
                                                                   statusResolveMsg, 
                                                                   recoveredElem, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, 
                                                                   nxtDAG, 
                                                                   setRemovableIRs, 
                                                                   currIR, 
                                                                   currIRInDAG, 
                                                                   nxtDAGVertices, 
                                                                   setIRsInDAG, 
                                                                   prev_dag, 
                                                                   seqEvent, 
                                                                   worker, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   currIRMon, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
                                                                   msg, irID, 
                                                                   removedIR, 
                                                                   controllerFailedModules >>

ControllerEvenHanlderRemoveEventFromQueue1(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue1"
                                                    /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                    /\ UNCHANGED << switchLock, 
                                                                    controllerLock, 
                                                                    FirstInstall, 
                                                                    sw_fail_ordering_var, 
                                                                    ContProcSet, 
                                                                    SwProcSet, 
                                                                    irTypeMapping, 
                                                                    ir2sw, 
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
                                                                    RecoveryStatus, 
                                                                    controllerSubmoduleFailNum, 
                                                                    controllerSubmoduleFailStat, 
                                                                    switchOrdering, 
                                                                    TEEventQueue, 
                                                                    DAGEventQueue, 
                                                                    DAGQueue, 
                                                                    DAGID, 
                                                                    MaxDAGID, 
                                                                    DAGState, 
                                                                    RCNIBEventQueue, 
                                                                    RCIRStatus, 
                                                                    RCSwSuspensionStatus, 
                                                                    nxtRCIRID, 
                                                                    idWorkerWorkingOnDAG, 
                                                                    RCSeqWorkerStatus, 
                                                                    IRDoneSet, 
                                                                    idThreadWorkingOnIR, 
                                                                    workerThreadRanking, 
                                                                    masterState, 
                                                                    controllerStateNIB, 
                                                                    NIBIRStatus, 
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
                                                                    obj, 
                                                                    failedSet, 
                                                                    statusResolveMsg, 
                                                                    recoveredElem, 
                                                                    event, 
                                                                    topoChangeEvent, 
                                                                    currSetDownSw, 
                                                                    prev_dag_id, 
                                                                    init, 
                                                                    nxtDAG, 
                                                                    setRemovableIRs, 
                                                                    currIR, 
                                                                    currIRInDAG, 
                                                                    nxtDAGVertices, 
                                                                    setIRsInDAG, 
                                                                    prev_dag, 
                                                                    seqEvent, 
                                                                    worker, 
                                                                    toBeScheduledIRs, 
                                                                    nextIR, 
                                                                    stepOfFailure_, 
                                                                    currDAG, 
                                                                    IRSet, 
                                                                    currIRMon, 
                                                                    nextIRToSent, 
                                                                    rowIndex, 
                                                                    rowRemove, 
                                                                    stepOfFailure_c, 
                                                                    monitoringEvent, 
                                                                    setIRsToReset, 
                                                                    resetIR, 
                                                                    stepOfFailure, 
                                                                    msg, irID, 
                                                                    removedIR, 
                                                                    controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ controllerIsMaster(self[1])
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus # <<>>
                                                   /\ TRUE
                                                   /\ IF (controllerStateNIB[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![controllerStateNIB[self].sw] = SW_SUSPEND]
                                                              /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                                                                                     sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND])]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                                              SwSuspensionStatus >>
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   controllerLock, 
                                                                   FirstInstall, 
                                                                   sw_fail_ordering_var, 
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   irTypeMapping, 
                                                                   ir2sw, 
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
                                                                   RecoveryStatus, 
                                                                   controllerSubmoduleFailNum, 
                                                                   controllerSubmoduleFailStat, 
                                                                   switchOrdering, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   DAGID, 
                                                                   MaxDAGID, 
                                                                   DAGState, 
                                                                   RCIRStatus, 
                                                                   RCSwSuspensionStatus, 
                                                                   nxtRCIRID, 
                                                                   idWorkerWorkingOnDAG, 
                                                                   RCSeqWorkerStatus, 
                                                                   IRDoneSet, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   masterState, 
                                                                   controllerStateNIB, 
                                                                   NIBIRStatus, 
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
                                                                   obj, 
                                                                   failedSet, 
                                                                   statusResolveMsg, 
                                                                   recoveredElem, 
                                                                   event, 
                                                                   topoChangeEvent, 
                                                                   currSetDownSw, 
                                                                   prev_dag_id, 
                                                                   init, 
                                                                   nxtDAG, 
                                                                   setRemovableIRs, 
                                                                   currIR, 
                                                                   currIRInDAG, 
                                                                   nxtDAGVertices, 
                                                                   setIRsInDAG, 
                                                                   prev_dag, 
                                                                   seqEvent, 
                                                                   worker, 
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   stepOfFailure_, 
                                                                   currDAG, 
                                                                   IRSet, 
                                                                   currIRMon, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
                                                                   msg, irID, 
                                                                   removedIR, 
                                                                   controllerFailedModules >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEventHandlerProc1(self)
                                   \/ ControllerEventHandlerProc2(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerSuspendSW1(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ResetAllIRs1(self)
                                   \/ ResetAllIRs2(self)
                                   \/ ControllerFreeSuspendedSW(self)
                                   \/ ControllerFreeSuspendedSW1(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue1(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ controllerIsMaster(self[1])
                                       /\ moduleIsUp(self)
                                       /\ switch2Controller # <<>>
                                       /\ TRUE
                                       /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr1"]
                                       /\ UNCHANGED << switchLock, 
                                                       controllerLock, 
                                                       FirstInstall, 
                                                       sw_fail_ordering_var, 
                                                       ContProcSet, SwProcSet, 
                                                       irTypeMapping, ir2sw, 
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
                                                       RecoveryStatus, 
                                                       controllerSubmoduleFailNum, 
                                                       controllerSubmoduleFailStat, 
                                                       switchOrdering, 
                                                       TEEventQueue, 
                                                       DAGEventQueue, DAGQueue, 
                                                       DAGID, MaxDAGID, 
                                                       DAGState, 
                                                       RCNIBEventQueue, 
                                                       RCIRStatus, 
                                                       RCSwSuspensionStatus, 
                                                       nxtRCIRID, 
                                                       idWorkerWorkingOnDAG, 
                                                       RCSeqWorkerStatus, 
                                                       IRDoneSet, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       masterState, 
                                                       controllerStateNIB, 
                                                       NIBIRStatus, 
                                                       SwSuspensionStatus, 
                                                       IRQueueNIB, 
                                                       SetScheduledIRs, 
                                                       ingressPkt, ingressIR, 
                                                       egressMsg, ofaInMsg, 
                                                       ofaOutConfirmation, 
                                                       installerInIR, 
                                                       statusMsg, notFailedSet, 
                                                       failedElem, obj, 
                                                       failedSet, 
                                                       statusResolveMsg, 
                                                       recoveredElem, event, 
                                                       topoChangeEvent, 
                                                       currSetDownSw, 
                                                       prev_dag_id, init, 
                                                       nxtDAG, setRemovableIRs, 
                                                       currIR, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       rowIndex, rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, msg, 
                                                       irID, removedIR, 
                                                       controllerFailedModules >>

ControllerMonitorCheckIfMastr1(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr1"
                                        /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                        /\ Assert(msg'[self].flow \in 1..MaxNumFlows, 
                                                  "Failure of assertion at line 2296, column 9.")
                                        /\ Assert(msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}, 
                                                  "Failure of assertion at line 2297, column 9.")
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr2"]
                                        /\ UNCHANGED << switchLock, 
                                                        controllerLock, 
                                                        FirstInstall, 
                                                        sw_fail_ordering_var, 
                                                        ContProcSet, SwProcSet, 
                                                        irTypeMapping, ir2sw, 
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
                                                        RecoveryStatus, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, DAGID, 
                                                        MaxDAGID, DAGState, 
                                                        RCNIBEventQueue, 
                                                        RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        nxtRCIRID, 
                                                        idWorkerWorkingOnDAG, 
                                                        RCSeqWorkerStatus, 
                                                        IRDoneSet, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        SetScheduledIRs, 
                                                        ingressPkt, ingressIR, 
                                                        egressMsg, ofaInMsg, 
                                                        ofaOutConfirmation, 
                                                        installerInIR, 
                                                        statusMsg, 
                                                        notFailedSet, 
                                                        failedElem, obj, 
                                                        failedSet, 
                                                        statusResolveMsg, 
                                                        recoveredElem, event, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        nxtDAG, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, worker, 
                                                        toBeScheduledIRs, 
                                                        nextIR, stepOfFailure_, 
                                                        currDAG, IRSet, 
                                                        currIRMon, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, irID, 
                                                        removedIR, 
                                                        controllerFailedModules >>

ControllerMonitorCheckIfMastr2(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr2"
                                        /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg[self].flow, msg[self].type)]
                                        /\ Assert(msg[self].from = ir2sw[irID'[self]], 
                                                  "Failure of assertion at line 2299, column 9.")
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr3"]
                                        /\ UNCHANGED << switchLock, 
                                                        controllerLock, 
                                                        FirstInstall, 
                                                        sw_fail_ordering_var, 
                                                        ContProcSet, SwProcSet, 
                                                        irTypeMapping, ir2sw, 
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
                                                        RecoveryStatus, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, DAGID, 
                                                        MaxDAGID, DAGState, 
                                                        RCNIBEventQueue, 
                                                        RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        nxtRCIRID, 
                                                        idWorkerWorkingOnDAG, 
                                                        RCSeqWorkerStatus, 
                                                        IRDoneSet, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        SetScheduledIRs, 
                                                        ingressPkt, ingressIR, 
                                                        egressMsg, ofaInMsg, 
                                                        ofaOutConfirmation, 
                                                        installerInIR, 
                                                        statusMsg, 
                                                        notFailedSet, 
                                                        failedElem, obj, 
                                                        failedSet, 
                                                        statusResolveMsg, 
                                                        recoveredElem, event, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        nxtDAG, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, worker, 
                                                        toBeScheduledIRs, 
                                                        nextIR, stepOfFailure_, 
                                                        currDAG, IRSet, 
                                                        currIRMon, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        removedIR, 
                                                        controllerFailedModules >>

ControllerMonitorCheckIfMastr3(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr3"
                                        /\ IF msg[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                              THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                        /\ UNCHANGED << switchLock, 
                                                        controllerLock, 
                                                        FirstInstall, 
                                                        sw_fail_ordering_var, 
                                                        ContProcSet, SwProcSet, 
                                                        irTypeMapping, ir2sw, 
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
                                                        RecoveryStatus, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, DAGID, 
                                                        MaxDAGID, DAGState, 
                                                        RCNIBEventQueue, 
                                                        RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        nxtRCIRID, 
                                                        idWorkerWorkingOnDAG, 
                                                        RCSeqWorkerStatus, 
                                                        IRDoneSet, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        masterState, 
                                                        controllerStateNIB, 
                                                        NIBIRStatus, 
                                                        SwSuspensionStatus, 
                                                        IRQueueNIB, 
                                                        SetScheduledIRs, 
                                                        ingressPkt, ingressIR, 
                                                        egressMsg, ofaInMsg, 
                                                        ofaOutConfirmation, 
                                                        installerInIR, 
                                                        statusMsg, 
                                                        notFailedSet, 
                                                        failedElem, obj, 
                                                        failedSet, 
                                                        statusResolveMsg, 
                                                        recoveredElem, event, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        nxtDAG, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, worker, 
                                                        toBeScheduledIRs, 
                                                        nextIR, stepOfFailure_, 
                                                        currDAG, IRSet, 
                                                        currIRMon, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        irID, removedIR, 
                                                        controllerFailedModules >>

ControllerUpdateIRDone(self) == /\ pc[self] = "ControllerUpdateIRDone"
                                /\ TRUE
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
                                      THEN /\ FirstInstall' = [FirstInstall EXCEPT ![irID[self]] = 1]
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone1"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                           /\ UNCHANGED FirstInstall
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, ir2sw, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                RecoveryStatus, switchOrdering, 
                                                TEEventQueue, DAGEventQueue, 
                                                DAGQueue, DAGID, MaxDAGID, 
                                                DAGState, RCNIBEventQueue, 
                                                RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                RCSeqWorkerStatus, IRDoneSet, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                masterState, 
                                                controllerStateNIB, 
                                                NIBIRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, nxtDAG, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR, 
                                                controllerFailedModules >>

ControllerUpdateIRDone1(self) == /\ pc[self] = "ControllerUpdateIRDone1"
                                 /\ IF NIBIRStatus[irID[self]] = IR_SENT
                                       THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID[self]] = IR_DONE]
                                            /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> irID[self], state |-> IR_DONE])]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << RCNIBEventQueue, 
                                                            NIBIRStatus >>
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone2"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerUpdateIRDone2(self) == /\ pc[self] = "ControllerUpdateIRDone2"
                                 /\ IF msg[self].type = DELETED_SUCCESSFULLY
                                       THEN /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone3"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCNIBEventQueue, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 removedIR, 
                                                 controllerFailedModules >>

ControllerUpdateIRDone3(self) == /\ pc[self] = "ControllerUpdateIRDone3"
                                 /\ removedIR' = [removedIR EXCEPT ![self] = getRemovedIRID(msg[self].flow)]
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerMonUpdateIRNone"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstall, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, ir2sw, 
                                                 swSeqChangedStatus, 
                                                 controller2Switch, 
                                                 switch2Controller, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, 
                                                 controllerSubmoduleFailNum, 
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCNIBEventQueue, RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, 
                                                 SwSuspensionStatus, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 controllerFailedModules >>

ControllerMonUpdateIRNone(self) == /\ pc[self] = "ControllerMonUpdateIRNone"
                                   /\ TRUE
                                   /\ IF (controllerSubmoduleFailStat[self] = NotFailed /\
                                                  controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \/ /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![self] = Failed]
                                                    /\ controllerSubmoduleFailNum' = [controllerSubmoduleFailNum EXCEPT ![self[1]] = controllerSubmoduleFailNum[self[1]] + 1]
                                                 \/ /\ TRUE
                                                    /\ UNCHANGED <<controllerSubmoduleFailNum, controllerSubmoduleFailStat>>
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
                                   /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![removedIR[self]] = IR_NONE]
                                   /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> removedIR[self], state |-> IR_NONE])]
                                   /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstall, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, ir2sw, 
                                                   swSeqChangedStatus, 
                                                   controller2Switch, 
                                                   switch2Controller, 
                                                   switchStatus, installedIRs, 
                                                   NicAsic2OfaBuff, 
                                                   Ofa2NicAsicBuff, 
                                                   Installer2OfaBuff, 
                                                   Ofa2InstallerBuff, TCAM, 
                                                   controlMsgCounter, 
                                                   RecoveryStatus, 
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   masterState, 
                                                   controllerStateNIB, 
                                                   SwSuspensionStatus, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   ingressPkt, ingressIR, 
                                                   egressMsg, ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
                                                   statusResolveMsg, 
                                                   recoveredElem, event, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   removedIR, 
                                                   controllerFailedModules >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ TRUE
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
                                                         irTypeMapping, ir2sw, 
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
                                                         RecoveryStatus, 
                                                         switchOrdering, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, DAGID, 
                                                         MaxDAGID, DAGState, 
                                                         RCNIBEventQueue, 
                                                         RCIRStatus, 
                                                         RCSwSuspensionStatus, 
                                                         nxtRCIRID, 
                                                         idWorkerWorkingOnDAG, 
                                                         RCSeqWorkerStatus, 
                                                         IRDoneSet, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         masterState, 
                                                         controllerStateNIB, 
                                                         NIBIRStatus, 
                                                         SwSuspensionStatus, 
                                                         IRQueueNIB, 
                                                         SetScheduledIRs, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, obj, 
                                                         failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem, event, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, removedIR, 
                                                         controllerFailedModules >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ ControllerMonitorCheckIfMastr1(self)
                                       \/ ControllerMonitorCheckIfMastr2(self)
                                       \/ ControllerMonitorCheckIfMastr3(self)
                                       \/ ControllerUpdateIRDone(self)
                                       \/ ControllerUpdateIRDone1(self)
                                       \/ ControllerUpdateIRDone2(self)
                                       \/ ControllerUpdateIRDone3(self)
                                       \/ ControllerMonUpdateIRNone(self)
                                       \/ MonitoringServerRemoveFromQueue(self)

ControllerWatchDogProc(self) == /\ pc[self] = "ControllerWatchDogProc"
                                /\ TRUE
                                /\ controllerFailedModules' = [controllerFailedModules EXCEPT ![self] = returnControllerFailedModules(self[1])]
                                /\ Cardinality(controllerFailedModules'[self]) > 0
                                /\ \E module \in controllerFailedModules'[self]:
                                     /\ Assert(controllerSubmoduleFailStat[module] = Failed, 
                                               "Failure of assertion at line 2364, column 13.")
                                     /\ controllerLock' = module
                                     /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![module] = NotFailed]
                                /\ pc' = [pc EXCEPT ![self] = "ControllerWatchDogProc"]
                                /\ UNCHANGED << switchLock, FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, ir2sw, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                RecoveryStatus, 
                                                controllerSubmoduleFailNum, 
                                                switchOrdering, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, 
                                                RCNIBEventQueue, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                RCSeqWorkerStatus, IRDoneSet, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                masterState, 
                                                controllerStateNIB, 
                                                NIBIRStatus, 
                                                SwSuspensionStatus, IRQueueNIB, 
                                                SetScheduledIRs, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, event, 
                                                topoChangeEvent, currSetDownSw, 
                                                prev_dag_id, init, nxtDAG, 
                                                setRemovableIRs, currIR, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                rowIndex, rowRemove, 
                                                stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, removedIR >>

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
           \/ (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_MONITOR}): rcIRMonitor(self))
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
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_MONITOR}) : WF_vars(rcIRMonitor(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))
        /\ \A self \in ({ofc0, rc0} \X {WATCH_DOG}) : WF_vars(watchDog(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-df10ba78ef79126e5c7b036fa2f8f5ed
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
CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in TOPO_DAG_MAPPING[listDownSwitches(SW)].v
                                                  /\ \E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x]
                                               \/ /\ x \notin TOPO_DAG_MAPPING[listDownSwitches(SW)].v
                                                  /\ ~\E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x])
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ NIBIRStatus[x] = IR_DONE
                                                       \/ x \notin TOPO_DAG_MAPPING[listDownSwitches(SW)].v)
                                                       
InstallationLivenessProp == <>[] (/\ CorrectDAGInstalled 
                                  /\ CorrectDoneStatusController)
InstallationInvProp == \/ ENABLED Next
                       \/ /\ CorrectDAGInstalled
                          /\ CorrectDoneStatusController
\* Safety Properties
IRCriticalSection == LET 
                        IRCriticalSet == {"ControllerThreadSendIR", "ControllerThreadForwardIR", "ControllerThreadSaveToDB2", "WaitForIRToHaveCorrectStatus", "ReScheduleifIRNone"}
                     IN   
                        \A x, y \in {ofc0} \X CONTROLLER_THREAD_POOL: \/ x = y
                                                                      \/ <<pc[x], pc[y]>> \notin IRCriticalSet \X IRCriticalSet
                                                                      \/ /\ <<pc[x], pc[y]>> \in IRCriticalSet \X IRCriticalSet
                                                                         /\ nextIRToSent[x] # nextIRToSent[y]

RedundantInstallation == \A x \in 1..MaxNumIRs: \/ NIBIRStatus[x] = IR_DONE
                                                \/ FirstInstall[x] = 0
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
whichDAG(ir) == CHOOSE x \in rangeSeq(TOPO_DAG_MAPPING): ir \in x.v

ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ whichDAG(getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)) # whichDAG(getIRIDForFlow(y, INSTALLED_SUCCESSFULLY))
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)                                                         
                                                         /\ <<getIRIDForFlow(y, INSTALLED_SUCCESSFULLY), getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<getIRIDForFlow(x, INSTALLED_SUCCESSFULLY), getIRIDForFlow(y, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e
EachIRAtMostOnce == ~\E x, y \in DOMAIN installedIRs: /\ x # y
                                                      /\ installedIRs[x] = installedIRs[y]
=============================================================================
\* Modification History
\* Last modified Fri Jan 26 18:20:56 PST 2024 by root
\* Created Sun Mar 28 03:06:08 PDT 2021 by root


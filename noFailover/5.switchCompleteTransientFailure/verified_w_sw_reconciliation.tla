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
          IR_DONE,
          SW_RUN,
          SW_SUSPEND,
          SW_RECONCILE,
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
          STATUS_NONE,
          ALL_FLOW,
          FLOW_STAT_REQ,
          FLOW_STAT_REPLY,          
          NO_ENTRY,
          ENTRY_FOUND
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
              \* irCounter is an indexing method used to synchronization
              \* between workers. Each IR is assigned an index and based
              \* on this index each worker would know whether the IR is 
              \* locked by another worker or not. 
              irCounter = 0, 
              MAX_IR_COUNTER = 15, 
              \* idThreadWorkingOnIR is a logical semaphore used for 
              \* synchronization between IRs
              idThreadWorkingOnIR = [x \in 1..MAX_IR_COUNTER |-> IR_UNLOCK],
              \* WorkerThreadRanking is an auxiliary variable used for 
              \* reducing the number of possible behaviours by applying
              \* the following rule; if two workers try to get the lock 
              \* for an IR, the one with lower ranking always gets it. 
              workerThreadRanking = CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z],
              \* keeps track of flow stat messages' cycle
              flowStatReqStatus = [x \in {ofc0} |-> [y \in SW |-> IR_NONE]],
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
        
        (***************************** Switch ********************************)                                  
        whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID] 
        \***************************** NIC/ASIC ******************************
        swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed 
        
        \***************************** OFA **********************************
        swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                                  /\ switchStatus[sw].ofa = NotFailed
        
        existMatchingEntryTCAM(swID, flowID) == \E x \in rangeSeq(TCAM[swID]): x = flowID
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
                                                                /\ x \notin SetScheduledIRs[ir2sw[x]]
                                                                /\ ~\E p \in Paths(Cardinality(DAG.v), DAG.e): /\ p[Len(p)] = x
                                                                                                               /\ RCSwSuspensionStatus[CID][ir2sw[p[1]]] # SW_RUN}
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
        setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(IRQueueNIB, <<CID, y>>)
                                                              /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}        
        canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                                  \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NO_TAG 
                                                     /\ NoEntryTaggedWith(IRQueueNIB, threadID) 
                                                     /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
        setThreadsAttemptingForLock(CID, item, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ isIdenticalElement(y.item, item)
                                                                                                                         /\ y.tag = <<CID, x>>
                                                                                          /\ pc[<<CID, x>>] = "ControllerThread"}
        threadWithLowerIDGetsTheLock(CID, threadID, item, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: 
                                                                                                                 z \in setThreadsAttemptingForLock(CID, item, IRQueue)}) 
        
        workerCanSendTheIR(CID, nextToSent) == /\ ~isSwitchSuspended(nextToSent.to)
                                               /\ \/ /\ nextToSent.type \in {DELETE_FLOW, INSTALL_FLOW}
                                                     /\ NIBIRStatus[nextToSent.IR] = IR_NONE
                                                  \/ /\ nextToSent.type = FLOW_STAT_REQ
                                                     /\ flowStatReqStatus[CID][nextToSent.to] = IR_NONE
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
                                                     /\ NIBIRStatus[x] \notin {IR_DONE, IR_NONE}}
        \* getIRSetToSuspend(CID, SID) == {x \in SetScheduledIRs[SID]: NIBIRStatus[x] = IR_NONE}           
                                                                             
        \*************************** Monitoring Server **********************
        getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                                \/ /\ irType = DELETED_SUCCESSFULLY
                                                                                   /\ irTypeMapping[x].type = DELETE_FLOW
                                                                             /\ irTypeMapping[x].flow = flowID
        getInstallationIRIDForFlow(flowID) == CHOOSE x \in 1..MaxNumIRs: IR2FLOW[x] = flowID
        
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
    
    macro increment(value, mod)
    begin
        value := (value % mod) + 1;
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

    \* ==== Install IR to TCAM =========
    macro installToTCAM(newFlow)
    begin
        installedIRs := Append(installedIRs, newFlow);
        TCAM[self[2]] := Append(TCAM[self[2]], newFlow);
    end macro
    \* =================================
    
    \* ==== DELETE FLOW from TCAM ======
    macro removeFromTCAM(flowID)
    begin
        if flowID \in rangeSeq(TCAM[self[2]]) then
            TCAM[self[2]] := removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], flowID));
        end if;
    end macro
    \* =================================
    
    \* ====== Forwarding the msg =======
    macro switchSend(msg)
    begin
        if WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL then
            switch2Controller := Append(switch2Controller, msg);
        else
            Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], msg);
        end if;
    end macro
    \* =================================
    
    \* == Acknowledge the Installaiton =
    macro sendConfirmation(controllerID, flowID, statusType)
    begin
        switchSend([type |-> statusType, from |-> self[2], to |-> controllerID,
                        flow |-> flowID]);
    end macro
    \* =================================
    
    \* == Flow Stat Reply (Not Found) ==
    macro sendFlowStatReplyNotFound(controllerID, flowID)
    begin
        switchSend([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> controllerID, 
                        status |-> NO_ENTRY, flow |-> flowID]);
    end macro
    \* =================================
    
    \* == Flow Stat Reply (Found) ======
    macro sendFlowStatReplyEntryFound(controllerID, flowID)
    begin
        switchSend([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> controllerID,
                        status |-> ENTRY_FOUND, flow |-> flowID]); 
    end macro
    \* =================================
    
    \* == Flow Stat Reply (All) ========
    macro sendFlowStatReplyAllEntries(controllerID)
    begin 
        switchSend([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> controllerID,
                        status |-> ALL_FLOW, flow |-> rangeSeq(TCAM[self[2]])]);
    end macro
    
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
    macro switchAcquireLock()
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
        await controllerLock \in {self, <<NO_LOCK, NO_LOCK>>};
        await switchLock = <<NO_LOCK, NO_LOCK>>;
    end macro
    \* =================================
    
    \* ========= controller acquire Lock ==========
    macro controllerAcquireLock()
    begin
        controllerWaitForLockFree();
        controllerLock := self;
    end macro    
    \* ============================================
    
    \* ========= controller release Lock ==========
    macro controllerReleaseLock()
    begin
        \* only the controller process itself can release the controller lock. 
        controllerWaitForLockFree();
        controllerLock := <<NO_LOCK, NO_LOCK>>;
    end macro
    \* =================================  
                      
    (*******************************************************************)
    (*                     NIB   (Macros)                              *)
    (*******************************************************************)
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
    macro controllerSendIR(nextIR)
    begin
        \* this macro mimics all the sending function;
        \* 1. append the message to the OpenFlow channel between controller and switch
        \* 2. give the lock of the system to the switch. 
        if nextIR.type = INSTALL_FLOW then
            assert irTypeMapping[nextIR.IR].type \in {INSTALL_FLOW, DELETE_FLOW};
            assert irTypeMapping[nextIR.IR].flow \in 1..MaxNumFlows;
            controller2Switch[ir2sw[nextIR.IR]] := Append(controller2Switch[ir2sw[nextIR.IR]], [type |-> irTypeMapping[nextIR.IR].type,
                                                                                                from |-> self[1],
                                                                                                to |-> nextIR.to,
                                                                                                flow |-> irTypeMapping[nextIR.IR].flow]);
        elsif nextIR.type = FLOW_STAT_REQ then
            controller2Switch[nextIR.to] := Append(controller2Switch[nextIR.to], [type |-> FLOW_STAT_REQ,
                                                                                  from |-> self[1],
                                                                                  to |-> nextIR.to,
                                                                                  flow |-> nextIR.flow]);
        end if;
        if whichSwitchModel(nextIR.to) = SW_COMPLEX_MODEL then 
            switchLock := <<NIC_ASIC_IN, nextIR.to>>;
        else
            switchLock := <<SW_SIMPLE_ID, nextIR.to>>;
        end if;
    end macro;
    \* =================================
    
    \* === Schedule FLowStatReq Msg =
    macro scheduleFlowStatReqAllEntries(swID)
    begin
        SwSuspensionStatus[swID] := SW_RECONCILE;
        RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
                                                              sw |-> monitoringEvent.swID, 
                                                              state |-> SW_RECONCILE]);
        modifiedEnqueue(IRQueueNIB, [type |-> FLOW_STAT_REQ, 
                                     to |-> swID, 
                                     flow |-> ALL_FLOW]); 
    end macro 
    \* ==============================    
    
        
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
        assert ingressPkt.type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ};
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        if ingressPkt.type = INSTALL_FLOW then
            installToTCAM(ingressPkt.flow);
            sendConfirmation(ingressPkt.from, ingressPkt.flow, INSTALLED_SUCCESSFULLY);
        elsif ingressPkt.type = DELETE_FLOW then
            removeFromTCAM(ingressPkt.flow);
            sendConfirmation(ingressPkt.from, ingressPkt.flow, DELETED_SUCCESSFULLY);
        elsif ingressPkt.type = FLOW_STAT_REQ then
            \* should check whether there is a matching entry in the TCAM or not.
            if ingressPkt.flow = ALL_FLOW then
                sendFlowStatReplyAllEntries(ingressPkt.from);
            elsif existMatchingEntryTCAM(self[2], ingressPkt.flow) then
                sendFlowStatReplyEntryFound(ingressPkt.from, ingressPkt.flow);
            else
                sendFlowStatReplyNotFound(ingressPkt.from, ingressPkt.flow);
            end if;             
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
        assert ingressIR.type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ};
        switchAcquireLock();
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
        switchAcquireLock();
        assert egressMsg.type \in {INSTALLED_SUCCESSFULLY, 
                                   DELETED_SUCCESSFULLY,
                                   FLOW_STAT_REPLY};
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
        switchAcquireLock();
        ofaInMsg := Head(NicAsic2OfaBuff[self[2]]);           
        assert ofaInMsg.to = self[2];
        assert \/ /\ ofaInMsg.type \in {INSTALL_FLOW, DELETE_FLOW}
                  /\ ofaInMsg.flow  \in 1..MaxNumFlows
               \/ /\ ofaInMsg.type = FLOW_STAT_REQ
                  /\ \/ ofaInMsg.flow = ALL_FLOW
                     \/ ofaInMsg.flow \in 1..MaxNumFlows;
        assert ofaInMsg.from \in {ofc0};
        NicAsic2OfaBuff[self[2]] := Tail(NicAsic2OfaBuff[self[2]]);
        
        \* Step 2: append the IR to the installer buffer
        SwitchOfaProcessPacket:
           if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<INSTALLER, self[2]>>);
                if ofaInMsg.type \in {INSTALL_FLOW, DELETE_FLOW} then
                    Ofa2InstallerBuff[self[2]] := Append(Ofa2InstallerBuff[self[2]], [type |-> ofaInMsg.type, 
                                                                                      flow |-> ofaInMsg.flow]);
                elsif ofaInMsg.type = FLOW_STAT_REQ then
                    \* Switch upon receiving FLOW_STAT_REQ message must check whether there is a matching 
                    \* entry in the TCAM or not. If there is it should reply with FLOW_STAT_REPLY with body 
                    \* containing specific information regarding the IR. Otherwise, should reply with FLOW_STAT_REPLY
                    \* message with empy body. Here, a simplified version is implemented. If entry found, switch
                    \* replies with status -> ENTRY_FOUND. Otherwise, it replies with status -> NO_ENTRY.
                    assert \/ ofaInMsg.flow = ALL_FLOW 
                           \/ ofaInMsg.flow \in 1..MaxNumFlows;
                    if ofaInMsg.flow = ALL_FLOW then
                        sendFlowStatReplyAllEntries(ofaInMsg.from);
                    elsif existMatchingEntryTCAM(self[2], ofaInMsg.flow) then
                        sendFlowStatReplyEntryFound(ofaInMsg.from, ofaInMsg.flow);
                    else
                        sendFlowStatReplyNotFound(ofaInMsg.from, ofaInMsg.flow);
                    end if;
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
        switchAcquireLock();
        ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
        Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
        assert ofaOutConfirmation.flow \in 1..MaxNumFlows;
        assert ofaOutConfirmation.type \in {INSTALL_FLOW, DELETE_FLOW};
        
        \* Step 2: prepare an installation confirmation message and send it to the controller
        \* through the NIC/ASIC
        SendInstallationConfirmation:
            if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                if ofaOutConfirmation.type = INSTALL_FLOW then
                    sendConfirmation(ofaOutConfirmation.from, ofaOutConfirmation.flow, INSTALLED_SUCCESSFULLY); 
                else
                    sendConfirmation(ofaOutConfirmation.from, ofaOutConfirmation.flow, DELETED_SUCCESSFULLY); 
                end if;
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
       switchAcquireLock();
       installerInIR := Head(Ofa2InstallerBuff[self[2]]);
       assert installerInIR.flow \in 1..MaxNumFlows;
       assert installerInIR.type \in {INSTALL_FLOW, DELETE_FLOW};
       
       Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);
       
       \* Step 2: install the IR to the TCAM
       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then
                switchAcquireLock();
                if installerInIR.type = INSTALL_FLOW then    
                    installToTCAM(installerInIR.flow);
                else
                    removeFromTCAM(installerInIR.flow);
                end if; 
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
        if WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL then
            await switchStatus[switchLock[2]].nicAsic = Failed;
        else
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
        event := Head(RCNIBEventQueue[self[1]]);
        assert event.type \in {TOPO_MOD, IR_MOD};
        if (event.type = TOPO_MOD) then
            if RCSwSuspensionStatus[self[1]][event.sw] # event.state then    
                RCSwSuspensionStatus[self[1]][event.sw] := event.state;
                TEEventQueue[self[1]] := Append(TEEventQueue[self[1]], event);
                if event.state = SW_RUN then
                    SetScheduledIRs[event.sw] := SetScheduledIRs[event.sw] \ getSetIRsForSwitch(event.sw);
                end if;
            end if;
        elsif (event.type = IR_MOD) then
            if RCIRStatus[self[1]][event.IR] # event.state then
                RCIRStatus[self[1]][event.IR] := event.state;
                if event.state \in {IR_SENT, IR_DONE} then
                    \* remove the IR from setscheduledIRs
                    SetScheduledIRs[ir2sw[event.IR]] := SetScheduledIRs[ir2sw[event.IR]]\{event.IR};    
                end if;
            end if;
        end if;
        RCNIBEventQueue[self[1]] := Tail(RCNIBEventQueue[self[1]]);
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
                topoChangeEvent := Head(TEEventQueue[self[1]]);
                assert topoChangeEvent.type \in {TOPO_MOD};
                if topoChangeEvent.state = SW_SUSPEND then
                    currSetDownSw := currSetDownSw \cup {topoChangeEvent.sw};
                else
                    currSetDownSw := currSetDownSw \ {topoChangeEvent.sw};
                end if; 
                TEEventQueue[self[1]] := Tail(TEEventQueue[self[1]]);
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
                    prev_dag := nxtDAG.dag;
                end if;
            end if;
        
        ControllerTERemoveUnnecessaryIRs:
            while setRemovableIRs # {} do
                controllerAcquireLock();
                currIR := CHOOSE x \in setRemovableIRs: TRUE;
                setRemovableIRs := setRemovableIRs \ {currIR};
                
                \* adjust data structures
                RCIRStatus[self[1]] := RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE);
                NIBIRStatus := NIBIRStatus @@ (nxtRCIRID :> IR_NONE);
                FirstInstall := FirstInstall @@ (nxtRCIRID :> 0);
                irTypeMapping := irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIR]]);
                ir2sw := ir2sw @@ (nxtRCIRID :> ir2sw[currIR]);
                nxtDAG.dag.v := nxtDAG.dag.v \cup {nxtRCIRID};
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
            
        ControllerTESubmitNewDAG:
            controllerReleaseLock();
            DAGState[nxtDAG.id] := DAG_SUBMIT;
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
        seqEvent := Head(DAGEventQueue[self[1]]);
        DAGEventQueue[self[1]] := Tail(DAGEventQueue[self[1]]);
        assert seqEvent.type \in {DAG_NEW, DAG_STALE};
        if seqEvent.type = DAG_NEW then
            DAGQueue[self[1]] := Append(DAGQueue[self[1]], seqEvent.dag_obj);
        else
            worker := idWorkerWorkingOnDAG[seqEvent.id];
            if worker # DAG_UNLOCK then
                RCSeqWorkerStatus[CONT_WORKER_SEQ] := SEQ_WORKER_STALE_SIGNAL;
                WaitForRCSeqWorkerTerminate:
                    await idWorkerWorkingOnDAG[seqEvent.id] = DAG_UNLOCK;
                    DAGState[seqEvent.id] := DAG_NONE;
            else
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
        currDAG := Head(DAGQueue[self[1]]);
        idWorkerWorkingOnDAG[currDAG.id] := self[2];
        
        ControllerWorkerSeqScheduleDAG:
            while ~allIRsInDAGInstalled(self[1], currDAG.dag) /\ ~isDAGStale(currDAG.id) do
                controllerWaitForLockFree();
                toBeScheduledIRs := getSetIRsCanBeScheduledNext(self[1], currDAG.dag);
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
                            modifiedEnqueue(IRQueueNIB, [type |-> INSTALL_FLOW, to |-> ir2sw[nextIR], IR |-> nextIR]);
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
            controllerWaitForLockFree();
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
                if allIRsInDAGInstalled(self[1], currDAG.dag) \/ isDAGStale(currDAG.id) then
                    RemoveDAGfromDAGQueue: 
                        controllerWaitForLockFree();
                        DAGQueue[self[1]] := Tail(DAGQueue[self[1]]);
                end if;
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
        await setIRMonitorShouldSchedule(self[1]) # {};
        controllerWaitForLockFree();
        currIRMon := CHOOSE x \in setIRMonitorShouldSchedule(self[1]): TRUE;
        if currIRMon \in IRDoneSet[self[1]] then 
            SetScheduledIRs[ir2sw[currIRMon]] := SetScheduledIRs[ir2sw[currIRMon]] \cup {currIRMon};
            modifiedEnqueue(IRQueueNIB, [type |-> INSTALL_FLOW, to |-> ir2sw[currIRMon], IR |-> currIRMon]);
        else
            
            \* adjust data structures
            RCIRStatus[self[1]] := RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE);
            NIBIRStatus := NIBIRStatus @@ (nxtRCIRID :> IR_NONE);
            FirstInstall := FirstInstall @@ (nxtRCIRID :> 0);
            irTypeMapping := irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIRMon]]);
            ir2sw := ir2sw @@ (nxtRCIRID :> ir2sw[currIRMon]);
        
            SetScheduledIRs[ir2sw[nxtRCIRID]] := SetScheduledIRs[ir2sw[nxtRCIRID]] \cup {nxtRCIRID};
            modifiedEnqueue(IRQueueNIB, [type |-> INSTALL_FLOW, to |-> ir2sw[nxtRCIRID], IR |-> nxtRCIRID]);
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
    variables nextIRToSent = [type |-> 0], entryIndex = -1, rowIndex = -1, 
                rowRemove = -1, stepOfFailure = 0; 
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
        modifiedRead(IRQueueNIB, nextIRToSent, entryIndex);
        
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
                if idThreadWorkingOnIR[entryIndex] = IR_UNLOCK then
                    await threadWithLowerIDGetsTheLock(self[1], self, nextIRToSent, IRQueueNIB); \* For Reducing Space
                    idThreadWorkingOnIR[entryIndex] := self[2]
                else
                    ControllerThreadRemoveQueue1: 
                        controllerWaitForLockFree();
                        modifiedRemove(IRQueueNIB, nextIRToSent);
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
                if (workerCanSendTheIR(self[1], nextIRToSent)) then
                    \**** Step 1.1: change the status of the switch to IR_SENT before actually sending
                    \**** the IR (Update-before-Action) 
                    assert nextIRToSent.type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ};
                    if nextIRToSent.type \in {INSTALL_FLOW, DELETE_FLOW} then
                        NIBIRStatus[nextIRToSent.IR] := IR_SENT;
                        RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> nextIRToSent.IR, state |-> IR_SENT]); 
                    elsif nextIRToSent.type = FLOW_STAT_REQ then 
                        flowStatReqStatus[self[1]][nextIRToSent.to] := IR_SENT;
                    end if;
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
                if idThreadWorkingOnIR[entryIndex] = self[2] then
                    idThreadWorkingOnIR[entryIndex] := IR_UNLOCK;
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
            whichStepToFail(2);
            if (stepOfFailure # 1) then 
                \* Step 1: clear the state on NIB
                controllerStateNIB[self] := [type |-> NO_STATUS];
                if (stepOfFailure # 2) then
                    \* Step 3: remove from IRQueue
                    modifiedRemove(IRQueueNIB, nextIRToSent);
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
        controllerReleaseLock();
        if (controllerStateNIB[self].type = STATUS_LOCKING) then
            if (controllerStateNIB[self].next.type \in {INSTALL_FLOW, DELETE_FLOW}) then    
                if (NIBIRStatus[controllerStateNIB[self].next] = IR_SENT) then
                        NIBIRStatus[controllerStateNIB[self].next] := IR_NONE;
                end if;                 
            elsif (controllerStateNIB[self].next.type = FLOW_STAT_REQ) then
                if (flowStatReqStatus[self[1]][controllerStateNIB[self].next] = IR_SENT) then
                    flowStatReqStatus[self[1]][controllerStateNIB[self].next] := IR_NONE;
                end if;
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
                    RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
                                                                            sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]);        
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;
                
         elsif canfreeSuspendedSw(monitoringEvent) /\ SwSuspensionStatus[monitoringEvent.swID] = SW_SUSPEND then
            \*call suspendInSchedulingIRs(monitoringEvent.swID);
            
            \* ControllerFreeSuspendedSW consists of three operations; 
            \* 1. Save on db that it is going to reset the IRs
            \* 2. Change the SW status to SW_RUN (so all the corresponding IRs going to be scheduled immediately)
            \* (event handler may fail between any of these Ops.)
            \*ControllerFreeSuspendedSW: 
            \*    controllerWaitForLockFree();
            \*    whichStepToFail(2);
            \*    if (stepOfFailure # 1) then 
                    \* Step 1: save state on NIB
            \*        controllerStateNIB[self] := [type |-> START_RESET_IR, sw |-> monitoringEvent.swID]; 
            \*        if (stepOfFailure # 2) then
                        \* Step 2: change switch status to SW_RUN
            \*            SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
            \*            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
            \*                                                                    sw |-> monitoringEvent.swID, state |-> SW_RUN]);  
            \*        end if;
            \*    end if;
                
            \*    if (stepOfFailure # 0) then
            \*        controllerModuleFails();
            \*        goto ControllerEventHandlerStateReconciliation;
            \*    end if;
            
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
                        scheduleFlowStatReqAllEntries(monitoringEvent.swID); 
                        \* getIRsToBeChecked retrieves all the IRs need to reset
                        \*getIRsToBeChecked:
                        \*    controllerWaitForLockFree();
                        \*    controllerModuleFailOrNot();
                        \*    if (controllerSubmoduleFailStat[self] = NotFailed) then
                        \*        setIRsToReset := getIRSetToReset(monitoringEvent.swID);
                        \*        if (setIRsToReset = {}) then \* Do not do the operations in ResetAllIRs label if setIRsToReset is Empty *\
                        \*            goto ControllerEvenHanlderRemoveEventFromQueue;
                        \*        end if;
                        \*    else
                        \*        goto ControllerEventHandlerStateReconciliation;
                        \*    end if;
                            
                        \* ResetAllIRs reset all the IRs in IR_SENT mode to IR_NONE one by one
                        \*ResetAllIRs:
                        \*    while TRUE do \* Initially: while setIRsToReset # {} do
                        \*        controllerWaitForLockFree();
                        \*        controllerModuleFailOrNot();
                        \*        if (controllerSubmoduleFailStat[self] = NotFailed) then
                        \*            resetIR := CHOOSE x \in setIRsToReset: TRUE;
                        \*            setIRsToReset := setIRsToReset \ {resetIR};
                                    
                                    \* the following operation (if -- end if;) should be done atomically
                                    \* using CAS operation
                        \*            if NIBIRStatus[resetIR] # IR_DONE then
                        \*                NIBIRStatus[resetIR] := IR_NONE;
                        \*                RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], 
                        \*                                                [type |-> IR_MOD, IR |-> resetIR, state |-> IR_NONE]);
                        \*            end if;
                        \*            
                        \*            if setIRsToReset = {} then \* End of while *\
                        \*                goto ControllerEvenHanlderRemoveEventFromQueue;
                        \*            end if;
                        \*        else
                        \*            goto ControllerEventHandlerStateReconciliation;
                        \*        end if;
                        \*    end while;
                    else
                        SwSuspensionStatus[monitoringEvent.swID] := SW_RUN;
                        RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
                                                                                sw |-> monitoringEvent.swID, state |-> SW_RUN]); 
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
            controllerReleaseLock();
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
    variable msg = [type |-> 0], irID = 0, setIRs = {}, currIR = 0, removedIR = 0;
    begin
    ControllerMonitorCheckIfMastr:
    while TRUE do
        \* ControllerMonitor 
        \* 1. Picks the first packet from the packets received from the switches
        \* 2. Checks the message type;
        \***** 2.1. type = INSTALLED_SUCCESSFULLY -> sw has successfully installed the IR
        \***** 2.2. type = FLOW_STAT_REPLY -> sw's responce to the reconciliation request.
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await switch2Controller # <<>>;
        controllerAcquireLock();
        msg := Head(switch2Controller);
        assert msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, FLOW_STAT_REPLY};
        
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            \* If msg type is INSTALLED_SUCCESSFULLY, we have to change the IR status
            \* to IR_DONE. 
            irID := getIRIDForFlow(msg.flow, msg.type);
            assert msg.from = ir2sw[irID];
        
            ControllerUpdateIRDone:
                controllerReleaseLock(); 
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    FirstInstall[irID] := 1;
                    NIBIRStatus[irID] := IR_DONE; \* Should be done in one atomic operation
                    RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]);
                
                    if msg.type = DELETED_SUCCESSFULLY then
                        removedIR := getRemovedIRID(msg.flow);
                        ControllerMonUpdateIRNone:
                            controllerAcquireLock(); 
                            controllerModuleFailOrNot();
                            NIBIRStatus[removedIR] := IR_NONE; 
                            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> removedIR, state |-> IR_NONE]);
                    end if;                        
                else
                    goto ControllerMonitorCheckIfMastr;
                end if;
       elsif msg.type = FLOW_STAT_REPLY then  \* TODO(@Pooria): check labeling
                \* if monitoring server receives FLOW_STAT_REPLY, it should first 
                \* make sure the reply is for an SW with reconcile flag. then;
                \* 1. if all_entries, reconcile state of all IRs with NIB's state 
                \* 2. if specific entry found, set the flag of IR to IR_DONE
                \* 3. if specific entry not found, add the IR to reschedule set which is used by NIB event handler
                \* to reschedule the IRs that are not installed. 
                    assert msg.status \in {ALL_FLOW, NO_ENTRY, ENTRY_FOUND};
                    assert SwSuspensionStatus[msg.from] \in {SW_RECONCILE};
                    flowStatReqStatus[self[1]][msg.from] := IR_DONE;
                    
                    changeStatusOfSwToSwRun:
                        controllerReleaseLock();
                        SwSuspensionStatus[msg.from] := SW_RUN;
                        RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD, 
                                                                              sw |-> msg.from, 
                                                                              state |-> SW_RUN]);
                    
                    if msg.status = ALL_FLOW then
                        setIRs := getSetIRsForSwitch(msg.from);
                        changeStatusOfIRsUponAllFlow:
                            while TRUE do \* -- while setIRs # {} do --
                                controllerWaitForLockFree();
                                currIR := CHOOSE x \in setIRs: TRUE;
                                setIRs := setIRs \ {currIR};
                                if IR2FLOW[currIR] \in msg.flow /\ NIBIRStatus[currIR] # IR_DONE then
                                    NIBIRStatus[currIR] := IR_DONE;
                                    RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, 
                                                                                          IR |-> currIR, 
                                                                                          state |-> IR_DONE]);
                                elsif IR2FLOW[currIR] \notin msg.flow /\ NIBIRStatus[currIR] # IR_NONE then
                                    NIBIRStatus[currIR] := IR_NONE;
                                    RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, 
                                                                                          IR |-> currIR, 
                                                                                          state |-> IR_NONE]);
                                end if;
                                if setIRs = {} then 
                                    goto MonitoringServerRemoveFromQueue;
                                end if;
                            end while;
                            
                    elsif msg.status = ENTRY_FOUND /\ NIBIRStatus[getInstallationIRIDForFlow(msg.flow)] # IR_DONE then
                        changeStatusOfIRUponEntryFound:
                            controllerWaitForLockFree();
                            NIBIRStatus[IR2FLOW[msg.flow]] := IR_DONE;
                            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, 
                                                                                  IR |-> getInstallationIRIDForFlow(msg.flow), 
                                                                                  state |-> IR_DONE]);
                    elsif msg.status = NO_ENTRY /\ NIBIRStatus[getInstallationIRIDForFlow(msg.flow)] # IR_NONE then
                        changeStatusOfIRUponNoEntry:
                            controllerWaitForLockFree();
                            NIBIRStatus[IR2FLOW[msg.flow]] := IR_NONE;
                            RCNIBEventQueue[rc0] := Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, 
                                                                                  IR |-> getInstallationIRIDForFlow(msg.flow), 
                                                                                  state |-> IR_NONE]);
                    end if;
        end if;
        
        \*end if;
        
        \* MonitoringServerRemoveFromQueue lazily removes the msg from queue. 
        MonitoringServerRemoveFromQueue:
            controllerReleaseLock();
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ee4aa5721a83bb912d04e1620640af0b (chksum(pcal) = "4659e0c1" /\ chksum(tla) = "fbf6be4a") (chksum(pcal) = "7a2fe2c1" /\ chksum(tla) = "14ddaa3a") (chksum(pcal) = "82f87b30" /\ chksum(tla) = "47d3f7df") (chksum(pcal) = "82f87b30" /\ chksum(tla) = "47d3f7df") (chksum(pcal) = "23f446bc" /\ chksum(tla) = "723889b7") (chksum(pcal) = "c248126e" /\ chksum(tla) = "7c859022") (chksum(pcal) = "3b6de34d" /\ chksum(tla) = "ad4c98fd") (chksum(pcal) = "f50dd7cc" /\ chksum(tla) = "45c9e90e") (chksum(pcal) = "f50dd7cc" /\ chksum(tla) = "45c9e90e") (chksum(pcal) = "f50dd7cc" /\ chksum(tla) = "45c9e90e") (chksum(pcal) = "f50dd7cc" /\ chksum(tla) = "6e880c75") (chksum(pcal) = "9b7e9154" /\ chksum(tla) = "bcec9455") (chksum(pcal) = "31f89ec4" /\ chksum(tla) = "f49fed71") (chksum(pcal) = "31f89ec4" /\ chksum(tla) = "628eb008") (chksum(pcal) = "542cd8a0" /\ chksum(tla) = "d4de6745") (chksum(pcal) = "542cd8a0" /\ chksum(tla) = "d4de6745") (chksum(pcal) = "542cd8a0" /\ chksum(tla) = "d4de6745") (chksum(pcal) = "542cd8a0" /\ chksum(tla) = "d4de6745") (chksum(pcal) = "5bba88d3" /\ chksum(tla) = "48eae82e") (chksum(pcal) = "5bba88d3" /\ chksum(tla) = "a94d4467") (chksum(pcal) = "5bba88d3" /\ chksum(tla) = "8c5f03af") (chksum(pcal) = "5bba88d3" /\ chksum(tla) = "a94d4467") (chksum(pcal) = "5bba88d3" /\ chksum(tla) = "a94d4467") (chksum(pcal) = "1f2b9c17" /\ chksum(tla) = "fee3deed") (chksum(pcal) = "dfde1fce" /\ chksum(tla) = "fe789038") (chksum(pcal) = "6ddeb726" /\ chksum(tla) = "3beb8e13") (chksum(pcal) = "5a75ba25" /\ chksum(tla) = "93b9b20e") (chksum(pcal) = "c8de7fb9" /\ chksum(tla) = "b833b74c") (chksum(pcal) = "94f3909" /\ chksum(tla) = "8ad80f38") (chksum(pcal) = "5d2e9460" /\ chksum(tla) = "c8187013") (chksum(pcal) = "d247bf8c" /\ chksum(tla) = "985db525") (chksum(pcal) = "9d6e4c" /\ chksum(tla) = "7dacb4e3") (chksum(pcal) = "9bdecb49" /\ chksum(tla) = "98dd9b9e") (chksum(pcal) = "6b238baf" /\ chksum(tla) = "290afe3e") (chksum(pcal) = "76d2acc4" /\ chksum(tla) = "3544ab03") (chksum(pcal) = "c1a8d0c0" /\ chksum(tla) = "d6de12ac") (chksum(pcal) = "7d4e2ade" /\ chksum(tla) = "f9ee86e3") (chksum(pcal) = "95171eb" /\ chksum(tla) = "1aa9a66a") (chksum(pcal) = "7d9bcccc" /\ chksum(tla) = "c5bd2e16") (chksum(pcal) = "6bd52f45" /\ chksum(tla) = "155153ef") (chksum(pcal) = "bbc44abc" /\ chksum(tla) = "cbacbd3a") (chksum(pcal) = "7d9bcccc" /\ chksum(tla) = "c5bd2e16") (chksum(pcal) = "7d9bcccc" /\ chksum(tla) = "c5bd2e16") (chksum(pcal) = "3c7aeabb" /\ chksum(tla) = "e1e9121a") (chksum(pcal) = "c765cee3" /\ chksum(tla) = "b3676750") (chksum(pcal) = "c765cee3" /\ chksum(tla) = "b3676750") (chksum(pcal) = "f0f35180" /\ chksum(tla) = "116354c4") (chksum(pcal) = "ceaffbd8" /\ chksum(tla) = "31d4ed2f") (chksum(pcal) = "ceaffbd8" /\ chksum(tla) = "31d4ed2f") (chksum(pcal) = "ceaffbd8" /\ chksum(tla) = "31d4ed2f") (chksum(pcal) = "c978416d" /\ chksum(tla) = "9fdb807d") (chksum(pcal) = "9a483c9a" /\ chksum(tla) = "7a45fb4c") (chksum(pcal) = "9a483c9a" /\ chksum(tla) = "4e286c19") (chksum(pcal) = "6f77d7a0" /\ chksum(tla) = "1f75f444") (chksum(pcal) = "aa8b125c" /\ chksum(tla) = "8d865ca9") (chksum(pcal) = "cf3d0a41" /\ chksum(tla) = "5d555c32") (chksum(pcal) = "bcd87d9" /\ chksum(tla) = "21926a6d") (chksum(pcal) = "d086e217" /\ chksum(tla) = "65fe51b") (chksum(pcal) = "2d7f3fa9" /\ chksum(tla) = "291a932") (chksum(pcal) = "37e95dd2" /\ chksum(tla) = "407e6ef2") (chksum(pcal) = "f3837e52" /\ chksum(tla) = "e6a7b81b") (chksum(pcal) = "f135207f" /\ chksum(tla) = "c21368b0") (chksum(pcal) = "f0eefb51" /\ chksum(tla) = "b3a92d60") (chksum(pcal) = "b00ad258" /\ chksum(tla) = "443ee621") (chksum(pcal) = "b00ad258" /\ chksum(tla) = "7764057c") (chksum(pcal) = "f18a760" /\ chksum(tla) = "f7920ead") (chksum(pcal) = "ce92cfd2" /\ chksum(tla) = "b1c1b140") (chksum(pcal) = "d6d06718" /\ chksum(tla) = "9282732b") (chksum(pcal) = "42ee3c5e" /\ chksum(tla) = "80518238") (chksum(pcal) = "8cb13c72" /\ chksum(tla) = "bb41fb81") (chksum(pcal) = "8cb13c72" /\ chksum(tla) = "bb41fb81") (chksum(pcal) = "8cb13c72" /\ chksum(tla) = "bb41fb81") (chksum(pcal) = "c22c784a" /\ chksum(tla) = "81d3ea87") (chksum(pcal) = "3dd25d26" /\ chksum(tla) = "2b6204c8") (chksum(pcal) = "8c4c98f" /\ chksum(tla) = "9d2a12f4") (chksum(pcal) = "8c4c98f" /\ chksum(tla) = "40286c29") (chksum(pcal) = "8c4c98f" /\ chksum(tla) = "b4d767c4") (chksum(pcal) = "be68fae5" /\ chksum(tla) = "bbd15d38") (chksum(pcal) = "db916232" /\ chksum(tla) = "af315036") (chksum(pcal) = "66bee27d" /\ chksum(tla) = "12fe2e40") (chksum(pcal) = "2e97a457" /\ chksum(tla) = "9a07bcc2") (chksum(pcal) = "2e97a457" /\ chksum(tla) = "240a047e") (chksum(pcal) = "364a9b04" /\ chksum(tla) = "19f17100") (chksum(pcal) = "6b20d6a" /\ chksum(tla) = "67251219") (chksum(pcal) = "829c0e2c" /\ chksum(tla) = "8c827318") (chksum(pcal) = "a1dfa3e2" /\ chksum(tla) = "63c2fb6a") (chksum(pcal) = "6ac668f0" /\ chksum(tla) = "eca70484") (chksum(pcal) = "a4642e9b" /\ chksum(tla) = "5262f401") (chksum(pcal) = "a4642e9b" /\ chksum(tla) = "5262f401") (chksum(pcal) = "bdf6aef3" /\ chksum(tla) = "374343fd") (chksum(pcal) = "275cfd35" /\ chksum(tla) = "ad4ac30d") (chksum(pcal) = "a84db520" /\ chksum(tla) = "e0fd6452") (chksum(pcal) = "a84db520" /\ chksum(tla) = "e0fd6452") (chksum(pcal) = "a84db520" /\ chksum(tla) = "e0fd6452") (chksum(pcal) = "9e9e8407" /\ chksum(tla) = "9cac35f2") (chksum(pcal) = "9aa4e816" /\ chksum(tla) = "9a332feb") (chksum(pcal) = "a30b13d4" /\ chksum(tla) = "5f074879") (chksum(pcal) = "e4caf3de" /\ chksum(tla) = "36a5f04e") (chksum(pcal) = "1406ea28" /\ chksum(tla) = "b81c8f91") (chksum(pcal) = "1406ea28" /\ chksum(tla) = "b81c8f91") (chksum(pcal) = "980c642" /\ chksum(tla) = "54e27b3c") (chksum(pcal) = "69ded205" /\ chksum(tla) = "1b9425d6") (chksum(pcal) = "59c8a39c" /\ chksum(tla) = "4b65833e") (chksum(pcal) = "6b0daafa" /\ chksum(tla) = "71f1dff3") (chksum(pcal) = "4e7272db" /\ chksum(tla) = "ac6892dc") (chksum(pcal) = "4e7272db" /\ chksum(tla) = "ac6892dc") (chksum(pcal) = "4e7272db" /\ chksum(tla) = "ac6892dc") (chksum(pcal) = "4e7272db" /\ chksum(tla) = "ac6892dc") (chksum(pcal) = "e40d1db7" /\ chksum(tla) = "ba8c95ce") (chksum(pcal) = "2440cf55" /\ chksum(tla) = "838b0fe5") (chksum(pcal) = "2440cf55" /\ chksum(tla) = "e96975d0") (chksum(pcal) = "474b51ce" /\ chksum(tla) = "fd608e0b") (chksum(pcal) = "1f8ede3" /\ chksum(tla) = "5bf69df8") (chksum(pcal) = "ed782cd9" /\ chksum(tla) = "e8b1581a") (chksum(pcal) = "ed782cd9" /\ chksum(tla) = "ca5ce0b7") (chksum(pcal) = "244ca6f5" /\ chksum(tla) = "c80c3056") (chksum(pcal) = "d1bd6239" /\ chksum(tla) = "d9bd9fd2") (chksum(pcal) = "7b2adfce" /\ chksum(tla) = "2ff49137") (chksum(pcal) = "de87d7fd" /\ chksum(tla) = "2561dcea") (chksum(pcal) = "80f12db0" /\ chksum(tla) = "9a564ce4") (chksum(pcal) = "4a0408ef" /\ chksum(tla) = "ab8d3415") (chksum(pcal) = "a45cc940" /\ chksum(tla) = "ac3761c4") (chksum(pcal) = "22345170" /\ chksum(tla) = "3e0273ab") (chksum(pcal) = "3c03da40" /\ chksum(tla) = "7040bb36") (chksum(pcal) = "99808a7" /\ chksum(tla) = "52c19f1e") (chksum(pcal) = "60167b8e" /\ chksum(tla) = "bececfa2") (chksum(pcal) = "4ca36c0c" /\ chksum(tla) = "49327ab2") (chksum(pcal) = "4ca36c0c" /\ chksum(tla) = "ebcd75f3") (chksum(pcal) = "19fd05c9" /\ chksum(tla) = "af15f847") (chksum(pcal) = "2868cdcf" /\ chksum(tla) = "786a58c8") (chksum(pcal) = "e01f006b" /\ chksum(tla) = "b5363286") (chksum(pcal) = "d298ea7" /\ chksum(tla) = "c1b2e9f5") (chksum(pcal) = "97716171" /\ chksum(tla) = "8aa22682") (chksum(pcal) = "97716171" /\ chksum(tla) = "6f607da2") (chksum(pcal) = "97716171" /\ chksum(tla) = "40d66d23") (chksum(pcal) = "97716171" /\ chksum(tla) = "fa0ced5f") (chksum(pcal) = "68cb5400" /\ chksum(tla) = "4389971") (chksum(pcal) = "189301ee" /\ chksum(tla) = "87965dc2") (chksum(pcal) = "189301ee" /\ chksum(tla) = "febe02f0") (chksum(pcal) = "e8e52930" /\ chksum(tla) = "a8f8f570") (chksum(pcal) = "bff84086" /\ chksum(tla) = "68672c10") (chksum(pcal) = "a0d93bf5" /\ chksum(tla) = "cdae7ae6") (chksum(pcal) = "a0d93bf5" /\ chksum(tla) = "cdae7ae6") (chksum(pcal) = "e060dedc" /\ chksum(tla) = "10ed932b") (chksum(pcal) = "e33979c9" /\ chksum(tla) = "f0768d82") (chksum(pcal) = "b7a43deb" /\ chksum(tla) = "bdf31ad9") (chksum(pcal) = "b7a43deb" /\ chksum(tla) = "40c9c903") (chksum(pcal) = "d6befb16" /\ chksum(tla) = "61dc9130") (chksum(pcal) = "82145b0" /\ chksum(tla) = "51afc352") (chksum(pcal) = "c91de568" /\ chksum(tla) = "e8100f74") (chksum(pcal) = "72b6419d" /\ chksum(tla) = "d5dc2574") (chksum(pcal) = "6275dd78" /\ chksum(tla) = "3f4fa189") (chksum(pcal) = "b2243fe0" /\ chksum(tla) = "8de448b2") (chksum(pcal) = "100c6f11" /\ chksum(tla) = "b21640af") (chksum(pcal) = "100c6f11" /\ chksum(tla) = "b21640af") (chksum(pcal) = "9be41bc1" /\ chksum(tla) = "4469ad76") (chksum(pcal) = "c7bc5169" /\ chksum(tla) = "4f58abb9") (chksum(pcal) = "5a3b7f01" /\ chksum(tla) = "9b66017") (chksum(pcal) = "c74acdd" /\ chksum(tla) = "42e1222b") (chksum(pcal) = "9366ae03" /\ chksum(tla) = "d710787") (chksum(pcal) = "55154e32" /\ chksum(tla) = "835e6700") (chksum(pcal) = "d5e66292" /\ chksum(tla) = "e467eba0") (chksum(pcal) = "8de4876" /\ chksum(tla) = "b243971a") (chksum(pcal) = "8de4876" /\ chksum(tla) = "b243971a") (chksum(pcal) = "39ca7ccb" /\ chksum(tla) = "aa8efb43") (chksum(pcal) = "44f5e5d0" /\ chksum(tla) = "c656118b") (chksum(pcal) = "3959cdd" /\ chksum(tla) = "9f70054f")
\* Process variable currIR of process controllerTrafficEngineering at line 1512 col 54 changed to currIR_
\* Process variable stepOfFailure of process controllerSequencer at line 1636 col 50 changed to stepOfFailure_
\* Process variable stepOfFailure of process controllerWorkerThreads at line 1803 col 33 changed to stepOfFailure_c
VARIABLES switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
          ContProcSet, SwProcSet, irTypeMapping, ir2sw, swSeqChangedStatus, 
          controller2Switch, switch2Controller, switchStatus, installedIRs, 
          NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
          Ofa2InstallerBuff, TCAM, controlMsgCounter, RecoveryStatus, 
          controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
          switchOrdering, TEEventQueue, DAGEventQueue, DAGQueue, DAGID, 
          MaxDAGID, DAGState, RCNIBEventQueue, RCIRStatus, 
          RCSwSuspensionStatus, nxtRCIRID, idWorkerWorkingOnDAG, 
          RCSeqWorkerStatus, IRDoneSet, irCounter, MAX_IR_COUNTER, 
          idThreadWorkingOnIR, workerThreadRanking, flowStatReqStatus, 
          masterState, controllerStateNIB, NIBIRStatus, SwSuspensionStatus, 
          IRQueueNIB, SetScheduledIRs, pc

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




whichSwitchModel(swID) == WHICH_SWITCH_MODEL[swID]

swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed


swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed

existMatchingEntryTCAM(swID, flowID) == \E x \in rangeSeq(TCAM[swID]): x = flowID

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
                                                        /\ x \notin SetScheduledIRs[ir2sw[x]]
                                                        /\ ~\E p \in Paths(Cardinality(DAG.v), DAG.e): /\ p[Len(p)] = x
                                                                                                       /\ RCSwSuspensionStatus[CID][ir2sw[p[1]]] # SW_RUN}
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



setFreeThreads(CID) == {y \in CONTROLLER_THREAD_POOL: /\ NoEntryTaggedWith(IRQueueNIB, <<CID, y>>)
                                                      /\ controllerSubmoduleFailStat[<<CID, y>>] = NotFailed}
canWorkerThreadContinue(CID, threadID) == \/ \E x \in rangeSeq(IRQueueNIB): x.tag = threadID
                                          \/ /\ \E x \in rangeSeq(IRQueueNIB): x.tag = NO_TAG
                                             /\ NoEntryTaggedWith(IRQueueNIB, threadID)
                                             /\ workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]: z \in setFreeThreads(CID)})
setThreadsAttemptingForLock(CID, item, IRQueue) == {x \in CONTROLLER_THREAD_POOL: /\ \E y \in rangeSeq(IRQueue): /\ isIdenticalElement(y.item, item)
                                                                                                                 /\ y.tag = <<CID, x>>
                                                                                  /\ pc[<<CID, x>>] = "ControllerThread"}
threadWithLowerIDGetsTheLock(CID, threadID, item, IRQueue) == workerThreadRanking[threadID[2]] = min({workerThreadRanking[z]:
                                                                                                         z \in setThreadsAttemptingForLock(CID, item, IRQueue)})

workerCanSendTheIR(CID, nextToSent) == /\ ~isSwitchSuspended(nextToSent.to)
                                       /\ \/ /\ nextToSent.type \in {DELETE_FLOW, INSTALL_FLOW}
                                             /\ NIBIRStatus[nextToSent.IR] = IR_NONE
                                          \/ /\ nextToSent.type = FLOW_STAT_REQ
                                             /\ flowStatReqStatus[CID][nextToSent.to] = IR_NONE

existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                /\ swSeqChangedStatus[x].num > monEvent.num
shouldSuspendSw(monEvent) == \/ monEvent.type = OFA_DOWN
                             \/ monEvent.type = NIC_ASIC_DOWN
                             \/ /\ monEvent.type = KEEP_ALIVE
                                /\ monEvent.status.installerStatus = INSTALLER_DOWN
canfreeSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                   /\ monEvent.status.installerStatus = INSTALLER_UP




getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                             /\ NIBIRStatus[x] \notin {IR_DONE, IR_NONE}}



getIRIDForFlow(flowID, irType) == CHOOSE x \in DOMAIN irTypeMapping: /\ \/ /\ irType = INSTALLED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = INSTALL_FLOW
                                                                        \/ /\ irType = DELETED_SUCCESSFULLY
                                                                           /\ irTypeMapping[x].type = DELETE_FLOW
                                                                     /\ irTypeMapping[x].flow = flowID
getInstallationIRIDForFlow(flowID) == CHOOSE x \in 1..MaxNumIRs: IR2FLOW[x] = flowID

getRemovedIRID(flowID) == CHOOSE x \in DOMAIN irTypeMapping: /\ irTypeMapping[x].type = INSTALL_FLOW
                                                             /\ irTypeMapping[x].flow = flowID

returnControllerFailedModules(cont) == {x \in ContProcSet: /\ x[1] = cont
                                                           /\ controllerSubmoduleFailStat[x] = Failed}


isFinished == \A x \in 1..MaxNumIRs: NIBIRStatus[x] = IR_DONE

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, obj, failedSet, 
          statusResolveMsg, recoveredElem, event, topoChangeEvent, 
          currSetDownSw, prev_dag_id, init, nxtDAG, setRemovableIRs, currIR_, 
          currIRInDAG, nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, 
          worker, toBeScheduledIRs, nextIR, stepOfFailure_, currDAG, IRSet, 
          currIRMon, nextIRToSent, entryIndex, rowIndex, rowRemove, 
          stepOfFailure_c, monitoringEvent, setIRsToReset, resetIR, 
          stepOfFailure, msg, irID, setIRs, currIR, removedIR, 
          controllerFailedModules

vars == << switchLock, controllerLock, FirstInstall, sw_fail_ordering_var, 
           ContProcSet, SwProcSet, irTypeMapping, ir2sw, swSeqChangedStatus, 
           controller2Switch, switch2Controller, switchStatus, installedIRs, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
           Ofa2InstallerBuff, TCAM, controlMsgCounter, RecoveryStatus, 
           controllerSubmoduleFailNum, controllerSubmoduleFailStat, 
           switchOrdering, TEEventQueue, DAGEventQueue, DAGQueue, DAGID, 
           MaxDAGID, DAGState, RCNIBEventQueue, RCIRStatus, 
           RCSwSuspensionStatus, nxtRCIRID, idWorkerWorkingOnDAG, 
           RCSeqWorkerStatus, IRDoneSet, irCounter, MAX_IR_COUNTER, 
           idThreadWorkingOnIR, workerThreadRanking, flowStatReqStatus, 
           masterState, controllerStateNIB, NIBIRStatus, SwSuspensionStatus, 
           IRQueueNIB, SetScheduledIRs, pc, ingressPkt, ingressIR, egressMsg, 
           ofaInMsg, ofaOutConfirmation, installerInIR, statusMsg, 
           notFailedSet, failedElem, obj, failedSet, statusResolveMsg, 
           recoveredElem, event, topoChangeEvent, currSetDownSw, prev_dag_id, 
           init, nxtDAG, setRemovableIRs, currIR_, currIRInDAG, 
           nxtDAGVertices, setIRsInDAG, prev_dag, seqEvent, worker, 
           toBeScheduledIRs, nextIR, stepOfFailure_, currDAG, IRSet, 
           currIRMon, nextIRToSent, entryIndex, rowIndex, rowRemove, 
           stepOfFailure_c, monitoringEvent, setIRsToReset, resetIR, 
           stepOfFailure, msg, irID, setIRs, currIR, removedIR, 
           controllerFailedModules >>

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
        /\ switchStatus = [x\in SW |-> [cpu |-> NotFailed, nicAsic |-> NotFailed,
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
        /\ irCounter = 0
        /\ MAX_IR_COUNTER = 15
        /\ idThreadWorkingOnIR = [x \in 1..MAX_IR_COUNTER |-> IR_UNLOCK]
        /\ workerThreadRanking = (CHOOSE x \in [CONTROLLER_THREAD_POOL -> 1..Cardinality(CONTROLLER_THREAD_POOL)]: ~\E y, z \in DOMAIN x: y # z /\ x[y] = x[z])
        /\ flowStatReqStatus = [x \in {ofc0} |-> [y \in SW |-> IR_NONE]]
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
        /\ ofaOutConfirmation = [self \in ({OFA_OUT} \X SW) |-> 0]
        (* Process installerModuleProc *)
        /\ installerInIR = [self \in ({INSTALLER} \X SW) |-> 0]
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
        /\ currIR_ = [self \in ({rc0} \X {CONT_TE}) |-> 0]
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
        /\ nextIRToSent = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> [type |-> 0]]
        /\ entryIndex = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
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
        /\ setIRs = [self \in ({ofc0} \X {CONT_MONITOR}) |-> {}]
        /\ currIR = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
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
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ}, 
                                       "Failure of assertion at line 1118, column 9.")
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ IF ingressPkt'[self].type = INSTALL_FLOW
                                   THEN /\ installedIRs' = Append(installedIRs, (ingressPkt'[self].flow))
                                        /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], (ingressPkt'[self].flow))]
                                        /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                              THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> INSTALLED_SUCCESSFULLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                           flow |-> (ingressPkt'[self].flow)]))
                                                   /\ UNCHANGED Ofa2NicAsicBuff
                                              ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> INSTALLED_SUCCESSFULLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                                     flow |-> (ingressPkt'[self].flow)]))]
                                                   /\ UNCHANGED switch2Controller
                                   ELSE /\ IF ingressPkt'[self].type = DELETE_FLOW
                                              THEN /\ IF (ingressPkt'[self].flow) \in rangeSeq(TCAM[self[2]])
                                                         THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], (ingressPkt'[self].flow)))]
                                                         ELSE /\ TRUE
                                                              /\ TCAM' = TCAM
                                                   /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                         THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> DELETED_SUCCESSFULLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                      flow |-> (ingressPkt'[self].flow)]))
                                                              /\ UNCHANGED Ofa2NicAsicBuff
                                                         ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> DELETED_SUCCESSFULLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                                                flow |-> (ingressPkt'[self].flow)]))]
                                                              /\ UNCHANGED switch2Controller
                                              ELSE /\ IF ingressPkt'[self].type = FLOW_STAT_REQ
                                                         THEN /\ IF ingressPkt'[self].flow = ALL_FLOW
                                                                    THEN /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                               THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                            status |-> ALL_FLOW, flow |-> rangeSeq(TCAM[self[2]])]))
                                                                                    /\ UNCHANGED Ofa2NicAsicBuff
                                                                               ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                                                                      status |-> ALL_FLOW, flow |-> rangeSeq(TCAM[self[2]])]))]
                                                                                    /\ UNCHANGED switch2Controller
                                                                    ELSE /\ IF existMatchingEntryTCAM(self[2], ingressPkt'[self].flow)
                                                                               THEN /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                                          THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                                       status |-> ENTRY_FOUND, flow |-> (ingressPkt'[self].flow)]))
                                                                                               /\ UNCHANGED Ofa2NicAsicBuff
                                                                                          ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                                                                                 status |-> ENTRY_FOUND, flow |-> (ingressPkt'[self].flow)]))]
                                                                                               /\ UNCHANGED switch2Controller
                                                                               ELSE /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                                          THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                                       status |-> NO_ENTRY, flow |-> (ingressPkt'[self].flow)]))
                                                                                               /\ UNCHANGED Ofa2NicAsicBuff
                                                                                          ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ingressPkt'[self].from),
                                                                                                                                                                                                 status |-> NO_ENTRY, flow |-> (ingressPkt'[self].flow)]))]
                                                                                               /\ UNCHANGED switch2Controller
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << switch2Controller, 
                                                                              Ofa2NicAsicBuff >>
                                                   /\ TCAM' = TCAM
                                        /\ UNCHANGED installedIRs
                             /\ Assert(\/ switchLock[2] = self[2]
                                       \/ switchLock[2] = NO_LOCK, 
                                       "Failure of assertion at line 926, column 9 of macro called at line 1136, column 9.")
                             /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, switchStatus, 
                                             NicAsic2OfaBuff, 
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
                                             irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             flowStatReqStatus, masterState, 
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
                                             nxtDAG, setRemovableIRs, currIR_, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, setIRs, 
                                             currIR, removedIR, 
                                             controllerFailedModules >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(ingressIR'[self].type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ}, 
                                   "Failure of assertion at line 1161, column 9.")
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << controllerLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, irTypeMapping, ir2sw, 
                                         swSeqChangedStatus, switch2Controller, 
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
                                         irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         flowStatReqStatus, masterState, 
                                         controllerStateNIB, NIBIRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, event, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR_, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, seqEvent, 
                                         worker, toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, currDAG, IRSet, 
                                         currIRMon, nextIRToSent, entryIndex, 
                                         rowIndex, rowRemove, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, irID, 
                                         setIRs, currIR, removedIR, 
                                         controllerFailedModules >>

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
                                                      IRDoneSet, irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      flowStatReqStatus, 
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
                                                      currIR_, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      setIRs, currIR, 
                                                      removedIR, 
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
                             /\ Assert(egressMsg'[self].type \in {INSTALLED_SUCCESSFULLY,
                                                                  DELETED_SUCCESSFULLY,
                                                                  FLOW_STAT_REPLY}, 
                                       "Failure of assertion at line 1188, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
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
                                             irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             flowStatReqStatus, masterState, 
                                             controllerStateNIB, NIBIRStatus, 
                                             SwSuspensionStatus, IRQueueNIB, 
                                             SetScheduledIRs, ingressPkt, 
                                             ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             nxtDAG, setRemovableIRs, currIR_, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, setIRs, 
                                             currIR, removedIR, 
                                             controllerFailedModules >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 926, column 9 of macro called at line 1197, column 17.")
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
                                                 irCounter, MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 flowStatReqStatus, 
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
                                                 currIR_, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, entryIndex, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 setIRs, currIR, removedIR, 
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
                                   "Failure of assertion at line 1225, column 9.")
                         /\ Assert(\/ /\ ofaInMsg'[self].type \in {INSTALL_FLOW, DELETE_FLOW}
                                      /\ ofaInMsg'[self].flow  \in 1..MaxNumFlows
                                   \/ /\ ofaInMsg'[self].type = FLOW_STAT_REQ
                                      /\ \/ ofaInMsg'[self].flow = ALL_FLOW
                                         \/ ofaInMsg'[self].flow \in 1..MaxNumFlows, 
                                   "Failure of assertion at line 1226, column 9.")
                         /\ Assert(ofaInMsg'[self].from \in {ofc0}, 
                                   "Failure of assertion at line 1231, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << controllerLock, FirstInstall, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, irTypeMapping, ir2sw, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, Ofa2NicAsicBuff, 
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
                                         irCounter, MAX_IR_COUNTER, 
                                         idThreadWorkingOnIR, 
                                         workerThreadRanking, 
                                         flowStatReqStatus, masterState, 
                                         controllerStateNIB, NIBIRStatus, 
                                         SwSuspensionStatus, IRQueueNIB, 
                                         SetScheduledIRs, ingressPkt, 
                                         ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, event, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR_, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, seqEvent, 
                                         worker, toBeScheduledIRs, nextIR, 
                                         stepOfFailure_, currDAG, IRSet, 
                                         currIRMon, nextIRToSent, entryIndex, 
                                         rowIndex, rowRemove, stepOfFailure_c, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, msg, irID, 
                                         setIRs, currIR, removedIR, 
                                         controllerFailedModules >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                           /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           /\ switchLock' = <<INSTALLER, self[2]>>
                                           /\ IF ofaInMsg[self].type \in {INSTALL_FLOW, DELETE_FLOW}
                                                 THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], [type |-> ofaInMsg[self].type,
                                                                                                                                                         flow |-> ofaInMsg[self].flow])]
                                                      /\ UNCHANGED << switch2Controller, 
                                                                      Ofa2NicAsicBuff >>
                                                 ELSE /\ IF ofaInMsg[self].type = FLOW_STAT_REQ
                                                            THEN /\ Assert(\/ ofaInMsg[self].flow = ALL_FLOW
                                                                           \/ ofaInMsg[self].flow \in 1..MaxNumFlows, 
                                                                           "Failure of assertion at line 1247, column 21.")
                                                                 /\ IF ofaInMsg[self].flow = ALL_FLOW
                                                                       THEN /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                                  THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ofaInMsg[self].from),
                                                                                                                                               status |-> ALL_FLOW, flow |-> rangeSeq(TCAM[self[2]])]))
                                                                                       /\ UNCHANGED Ofa2NicAsicBuff
                                                                                  ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ofaInMsg[self].from),
                                                                                                                                                                                         status |-> ALL_FLOW, flow |-> rangeSeq(TCAM[self[2]])]))]
                                                                                       /\ UNCHANGED switch2Controller
                                                                       ELSE /\ IF existMatchingEntryTCAM(self[2], ofaInMsg[self].flow)
                                                                                  THEN /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                                             THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ofaInMsg[self].from),
                                                                                                                                                          status |-> ENTRY_FOUND, flow |-> (ofaInMsg[self].flow)]))
                                                                                                  /\ UNCHANGED Ofa2NicAsicBuff
                                                                                             ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ofaInMsg[self].from),
                                                                                                                                                                                                    status |-> ENTRY_FOUND, flow |-> (ofaInMsg[self].flow)]))]
                                                                                                  /\ UNCHANGED switch2Controller
                                                                                  ELSE /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                                             THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ofaInMsg[self].from),
                                                                                                                                                          status |-> NO_ENTRY, flow |-> (ofaInMsg[self].flow)]))
                                                                                                  /\ UNCHANGED Ofa2NicAsicBuff
                                                                                             ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> FLOW_STAT_REPLY, from |-> self[2], to |-> (ofaInMsg[self].from),
                                                                                                                                                                                                    status |-> NO_ENTRY, flow |-> (ofaInMsg[self].flow)]))]
                                                                                                  /\ UNCHANGED switch2Controller
                                                            ELSE /\ TRUE
                                                                 /\ UNCHANGED << switch2Controller, 
                                                                                 Ofa2NicAsicBuff >>
                                                      /\ UNCHANGED Ofa2InstallerBuff
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED ofaInMsg
                                      ELSE /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = [type |-> 0]]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED << switchLock, 
                                                           switch2Controller, 
                                                           Ofa2NicAsicBuff, 
                                                           Ofa2InstallerBuff >>
                                /\ UNCHANGED << controllerLock, FirstInstall, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, ir2sw, 
                                                swSeqChangedStatus, 
                                                controller2Switch, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Installer2OfaBuff, TCAM, 
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
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                flowStatReqStatus, masterState, 
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
                                                setRemovableIRs, currIR_, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, setIRs, currIR, 
                                                removedIR, 
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
                          /\ Assert(ofaOutConfirmation'[self].flow \in 1..MaxNumFlows, 
                                    "Failure of assertion at line 1276, column 9.")
                          /\ Assert(ofaOutConfirmation'[self].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                    "Failure of assertion at line 1277, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << controllerLock, FirstInstall, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, irTypeMapping, ir2sw, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
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
                                          irCounter, MAX_IR_COUNTER, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          flowStatReqStatus, masterState, 
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
                                          setRemovableIRs, currIR_, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          worker, toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, entryIndex, 
                                          rowIndex, rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          setIRs, currIR, removedIR, 
                                          controllerFailedModules >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                 /\ switchLock' = <<NIC_ASIC_OUT, self[2]>>
                                                 /\ IF ofaOutConfirmation[self].type = INSTALL_FLOW
                                                       THEN /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                  THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> INSTALLED_SUCCESSFULLY, from |-> self[2], to |-> (ofaOutConfirmation[self].from),
                                                                                                                               flow |-> (ofaOutConfirmation[self].flow)]))
                                                                       /\ UNCHANGED Ofa2NicAsicBuff
                                                                  ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> INSTALLED_SUCCESSFULLY, from |-> self[2], to |-> (ofaOutConfirmation[self].from),
                                                                                                                                                                         flow |-> (ofaOutConfirmation[self].flow)]))]
                                                                       /\ UNCHANGED switch2Controller
                                                       ELSE /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                  THEN /\ switch2Controller' = Append(switch2Controller, ([type |-> DELETED_SUCCESSFULLY, from |-> self[2], to |-> (ofaOutConfirmation[self].from),
                                                                                                                               flow |-> (ofaOutConfirmation[self].flow)]))
                                                                       /\ UNCHANGED Ofa2NicAsicBuff
                                                                  ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], ([type |-> DELETED_SUCCESSFULLY, from |-> self[2], to |-> (ofaOutConfirmation[self].from),
                                                                                                                                                                         flow |-> (ofaOutConfirmation[self].flow)]))]
                                                                       /\ UNCHANGED switch2Controller
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                 /\ UNCHANGED ofaOutConfirmation
                                            ELSE /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = 0]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                 /\ UNCHANGED << switchLock, 
                                                                 switch2Controller, 
                                                                 Ofa2NicAsicBuff >>
                                      /\ UNCHANGED << controllerLock, 
                                                      FirstInstall, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      irTypeMapping, ir2sw, 
                                                      swSeqChangedStatus, 
                                                      controller2Switch, 
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
                                                      IRDoneSet, irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      flowStatReqStatus, 
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
                                                      currIR_, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      setIRs, currIR, 
                                                      removedIR, 
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
                             /\ Assert(installerInIR'[self].flow \in 1..MaxNumFlows, 
                                       "Failure of assertion at line 1311, column 8.")
                             /\ Assert(installerInIR'[self].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                       "Failure of assertion at line 1312, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << controllerLock, FirstInstall, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, ir2sw, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
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
                                             irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             flowStatReqStatus, masterState, 
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
                                             setRemovableIRs, currIR_, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, setIRs, 
                                             currIR, removedIR, 
                                             controllerFailedModules >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                               /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                               /\ switchLock' = self
                                               /\ IF installerInIR[self].type = INSTALL_FLOW
                                                     THEN /\ installedIRs' = Append(installedIRs, (installerInIR[self].flow))
                                                          /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], (installerInIR[self].flow))]
                                                     ELSE /\ IF (installerInIR[self].flow) \in rangeSeq(TCAM[self[2]])
                                                                THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], (installerInIR[self].flow)))]
                                                                ELSE /\ TRUE
                                                                     /\ TCAM' = TCAM
                                                          /\ UNCHANGED installedIRs
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
                                                    IRDoneSet, irCounter, 
                                                    MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    flowStatReqStatus, 
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
                                                    setRemovableIRs, currIR_, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    nextIRToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    stepOfFailure_c, 
                                                    monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    setIRs, currIR, removedIR, 
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
                                                         IRDoneSet, irCounter, 
                                                         MAX_IR_COUNTER, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         flowStatReqStatus, 
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
                                                         currIR_, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         entryIndex, rowIndex, 
                                                         rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, setIRs, currIR, 
                                                         removedIR, 
                                                         controllerFailedModules >>

installerModuleProc(self) == SwitchInstallerProc(self)
                                \/ SwitchInstallerInsert2TCAM(self)
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
                                 "Failure of assertion at line 564, column 9 of macro called at line 1366, column 9.")
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
                                                       "Failure of assertion at line 694, column 9 of macro called at line 1386, column 17.")
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
                                                                  "Failure of assertion at line 746, column 9 of macro called at line 1388, column 17.")
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
                                                                             "Failure of assertion at line 790, column 9 of macro called at line 1390, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                                   /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                         THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                                        "Failure of assertion at line 793, column 13 of macro called at line 1390, column 17.")
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
                                                                                        "Failure of assertion at line 640, column 9 of macro called at line 1392, column 17.")
                                                                              /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                              /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                              /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                           swID |-> self[2],
                                                                                                                           num |-> controlMsgCounter'[self[2]]]]
                                                                              /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                                                         ELSE /\ Assert(FALSE, 
                                                                                        "Failure of assertion at line 1393, column 18.")
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
                                       RCSeqWorkerStatus, IRDoneSet, irCounter, 
                                       MAX_IR_COUNTER, idThreadWorkingOnIR, 
                                       workerThreadRanking, flowStatReqStatus, 
                                       masterState, controllerStateNIB, 
                                       NIBIRStatus, SwSuspensionStatus, 
                                       IRQueueNIB, SetScheduledIRs, ingressPkt, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       failedSet, statusResolveMsg, 
                                       recoveredElem, event, topoChangeEvent, 
                                       currSetDownSw, prev_dag_id, init, 
                                       nxtDAG, setRemovableIRs, currIR_, 
                                       currIRInDAG, nxtDAGVertices, 
                                       setIRsInDAG, prev_dag, seqEvent, worker, 
                                       toBeScheduledIRs, nextIR, 
                                       stepOfFailure_, currDAG, IRSet, 
                                       currIRMon, nextIRToSent, entryIndex, 
                                       rowIndex, rowRemove, stepOfFailure_c, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, msg, irID, setIRs, 
                                       currIR, removedIR, 
                                       controllerFailedModules >>

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ RecoveryStatus[self[2]].transient = 1
                              /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF RecoveryStatus[self[2]].partial = 0
                                    THEN /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                   "Failure of assertion at line 606, column 9 of macro called at line 1415, column 13.")
                                         /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                   "Failure of assertion at line 607, column 9 of macro called at line 1415, column 13.")
                                         /\ Assert(switchStatus[self[2]].ofa = Failed, 
                                                   "Failure of assertion at line 608, column 9 of macro called at line 1415, column 13.")
                                         /\ Assert(switchStatus[self[2]].installer = Failed, 
                                                   "Failure of assertion at line 609, column 9 of macro called at line 1415, column 13.")
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
                                                              "Failure of assertion at line 721, column 9 of macro called at line 1423, column 43.")
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
                                                                         "Failure of assertion at line 666, column 9 of macro called at line 1424, column 50.")
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
                                                                                    "Failure of assertion at line 768, column 9 of macro called at line 1425, column 46.")
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
                                                                                               "Failure of assertion at line 812, column 9 of macro called at line 1426, column 52.")
                                                                                     /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                                     /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                           THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                                          "Failure of assertion at line 815, column 13 of macro called at line 1426, column 52.")
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
                                                                                               "Failure of assertion at line 1427, column 18.")
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
                                              irCounter, MAX_IR_COUNTER, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              flowStatReqStatus, masterState, 
                                              controllerStateNIB, NIBIRStatus, 
                                              SwSuspensionStatus, IRQueueNIB, 
                                              SetScheduledIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              event, topoChangeEvent, 
                                              currSetDownSw, prev_dag_id, init, 
                                              nxtDAG, setRemovableIRs, currIR_, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              entryIndex, rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, setIRs, 
                                              currIR, removedIR, 
                                              controllerFailedModules >>

swResolveFailure(self) == SwitchResolveFailure(self)

ghostProc(self) == /\ pc[self] = "ghostProc"
                   /\ /\ switchLock # <<NO_LOCK, NO_LOCK>>
                      /\ switchLock[2] = self[2]
                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                   /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                         THEN /\ switchStatus[switchLock[2]].nicAsic = Failed
                         ELSE /\ IF switchStatus[switchLock[2]].cpu = Failed /\ switchLock[1] = NIC_ASIC_OUT
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
                             "Failure of assertion at line 926, column 9 of macro called at line 1468, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << controllerLock, FirstInstall, 
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
                                   IRDoneSet, irCounter, MAX_IR_COUNTER, 
                                   idThreadWorkingOnIR, workerThreadRanking, 
                                   flowStatReqStatus, masterState, 
                                   controllerStateNIB, NIBIRStatus, 
                                   SwSuspensionStatus, IRQueueNIB, 
                                   SetScheduledIRs, ingressPkt, ingressIR, 
                                   egressMsg, ofaInMsg, ofaOutConfirmation, 
                                   installerInIR, statusMsg, notFailedSet, 
                                   failedElem, obj, failedSet, 
                                   statusResolveMsg, recoveredElem, event, 
                                   topoChangeEvent, currSetDownSw, prev_dag_id, 
                                   init, nxtDAG, setRemovableIRs, currIR_, 
                                   currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                   prev_dag, seqEvent, worker, 
                                   toBeScheduledIRs, nextIR, stepOfFailure_, 
                                   currDAG, IRSet, currIRMon, nextIRToSent, 
                                   entryIndex, rowIndex, rowRemove, 
                                   stepOfFailure_c, monitoringEvent, 
                                   setIRsToReset, resetIR, stepOfFailure, msg, 
                                   irID, setIRs, currIR, removedIR, 
                                   controllerFailedModules >>

ghostUnlockProcess(self) == ghostProc(self)

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ controllerIsMaster(self[1])
                               /\ moduleIsUp(self)
                               /\ RCNIBEventQueue[self[1]] # <<>>
                               /\ event' = [event EXCEPT ![self] = Head(RCNIBEventQueue[self[1]])]
                               /\ Assert(event'[self].type \in {TOPO_MOD, IR_MOD}, 
                                         "Failure of assertion at line 1486, column 9.")
                               /\ IF (event'[self].type = TOPO_MOD)
                                     THEN /\ IF RCSwSuspensionStatus[self[1]][event'[self].sw] # event'[self].state
                                                THEN /\ RCSwSuspensionStatus' = [RCSwSuspensionStatus EXCEPT ![self[1]][event'[self].sw] = event'[self].state]
                                                     /\ TEEventQueue' = [TEEventQueue EXCEPT ![self[1]] = Append(TEEventQueue[self[1]], event'[self])]
                                                     /\ IF event'[self].state = SW_RUN
                                                           THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![event'[self].sw] = SetScheduledIRs[event'[self].sw] \ getSetIRsForSwitch(event'[self].sw)]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED SetScheduledIRs
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << TEEventQueue, 
                                                                     RCSwSuspensionStatus, 
                                                                     SetScheduledIRs >>
                                          /\ UNCHANGED RCIRStatus
                                     ELSE /\ IF (event'[self].type = IR_MOD)
                                                THEN /\ IF RCIRStatus[self[1]][event'[self].IR] # event'[self].state
                                                           THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![self[1]][event'[self].IR] = event'[self].state]
                                                                /\ IF event'[self].state \in {IR_SENT, IR_DONE}
                                                                      THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[event'[self].IR]] = SetScheduledIRs[ir2sw[event'[self].IR]]\{event'[self].IR}]
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED SetScheduledIRs
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << RCIRStatus, 
                                                                                SetScheduledIRs >>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << RCIRStatus, 
                                                                     SetScheduledIRs >>
                                          /\ UNCHANGED << TEEventQueue, 
                                                          RCSwSuspensionStatus >>
                               /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![self[1]] = Tail(RCNIBEventQueue[self[1]])]
                               /\ pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]
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
                                               switchOrdering, DAGEventQueue, 
                                               DAGQueue, DAGID, MaxDAGID, 
                                               DAGState, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
                                               RCSeqWorkerStatus, IRDoneSet, 
                                               irCounter, MAX_IR_COUNTER, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               flowStatReqStatus, masterState, 
                                               controllerStateNIB, NIBIRStatus, 
                                               SwSuspensionStatus, IRQueueNIB, 
                                               ingressPkt, ingressIR, 
                                               egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, topoChangeEvent, 
                                               currSetDownSw, prev_dag_id, 
                                               init, nxtDAG, setRemovableIRs, 
                                               currIR_, currIRInDAG, 
                                               nxtDAGVertices, setIRsInDAG, 
                                               prev_dag, seqEvent, worker, 
                                               toBeScheduledIRs, nextIR, 
                                               stepOfFailure_, currDAG, IRSet, 
                                               currIRMon, nextIRToSent, 
                                               entryIndex, rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, setIRs, currIR, removedIR, 
                                               controllerFailedModules >>

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ controllerIsMaster(self[1])
                          /\ moduleIsUp(self)
                          /\ init[self] = 1 \/ TEEventQueue[self[1]] # <<>>
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ controllerLock' = self
                          /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << switchLock, FirstInstall, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, irTypeMapping, ir2sw, 
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
                                          irCounter, MAX_IR_COUNTER, 
                                          idThreadWorkingOnIR, 
                                          workerThreadRanking, 
                                          flowStatReqStatus, masterState, 
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
                                          setRemovableIRs, currIR_, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          worker, toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, nextIRToSent, entryIndex, 
                                          rowIndex, rowRemove, stepOfFailure_c, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          setIRs, currIR, removedIR, 
                                          controllerFailedModules >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF TEEventQueue[self[1]] # <<>>
                                           THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue[self[1]])]
                                                /\ Assert(topoChangeEvent'[self].type \in {TOPO_MOD}, 
                                                          "Failure of assertion at line 1526, column 17.")
                                                /\ IF topoChangeEvent'[self].state = SW_SUSPEND
                                                      THEN /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \cup {topoChangeEvent'[self].sw}]
                                                      ELSE /\ currSetDownSw' = [currSetDownSw EXCEPT ![self] = currSetDownSw[self] \ {topoChangeEvent'[self].sw}]
                                                /\ TEEventQueue' = [TEEventQueue EXCEPT ![self[1]] = Tail(TEEventQueue[self[1]])]
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                                /\ UNCHANGED controllerLock
                                           ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                /\ UNCHANGED << TEEventQueue, 
                                                                topoChangeEvent, 
                                                                currSetDownSw >>
                                     /\ UNCHANGED << switchLock, FirstInstall, 
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
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     RCNIBEventQueue, 
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, irCounter, 
                                                     MAX_IR_COUNTER, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     flowStatReqStatus, 
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
                                                     prev_dag_id, init, nxtDAG, 
                                                     setRemovableIRs, currIR_, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, entryIndex, 
                                                     rowIndex, rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     setIRs, currIR, removedIR, 
                                                     controllerFailedModules >>

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ DAGID' = (DAGID % MaxDAGID) + 1
                                           /\ nxtDAG' = [nxtDAG EXCEPT ![self] = [id |-> DAGID', dag |-> TOPO_DAG_MAPPING[currSetDownSw[self]]]]
                                           /\ IF prev_dag[self] = nxtDAG'[self].dag
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                                      /\ UNCHANGED << DAGState, 
                                                                      prev_dag_id, 
                                                                      init, 
                                                                      nxtDAGVertices, 
                                                                      prev_dag >>
                                                 ELSE /\ nxtDAGVertices' = [nxtDAGVertices EXCEPT ![self] = nxtDAG'[self].dag.v]
                                                      /\ IF init[self] = 0
                                                            THEN /\ DAGState' = [DAGState EXCEPT ![prev_dag_id[self]] = DAG_STALE]
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTESendDagStaleNotif"]
                                                                 /\ UNCHANGED << prev_dag_id, 
                                                                                 init, 
                                                                                 prev_dag >>
                                                            ELSE /\ init' = [init EXCEPT ![self] = 0]
                                                                 /\ prev_dag_id' = [prev_dag_id EXCEPT ![self] = DAGID']
                                                                 /\ prev_dag' = [prev_dag EXCEPT ![self] = nxtDAG'[self].dag]
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                                                 /\ UNCHANGED DAGState
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
                                                           RCNIBEventQueue, 
                                                           RCIRStatus, 
                                                           RCSwSuspensionStatus, 
                                                           nxtRCIRID, 
                                                           idWorkerWorkingOnDAG, 
                                                           RCSeqWorkerStatus, 
                                                           IRDoneSet, 
                                                           irCounter, 
                                                           MAX_IR_COUNTER, 
                                                           idThreadWorkingOnIR, 
                                                           workerThreadRanking, 
                                                           flowStatReqStatus, 
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
                                                           currIR_, 
                                                           currIRInDAG, 
                                                           setIRsInDAG, 
                                                           seqEvent, worker, 
                                                           toBeScheduledIRs, 
                                                           nextIR, 
                                                           stepOfFailure_, 
                                                           currDAG, IRSet, 
                                                           currIRMon, 
                                                           nextIRToSent, 
                                                           entryIndex, 
                                                           rowIndex, rowRemove, 
                                                           stepOfFailure_c, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, 
                                                           stepOfFailure, msg, 
                                                           irID, setIRs, 
                                                           currIR, removedIR, 
                                                           controllerFailedModules >>

ControllerTESendDagStaleNotif(self) == /\ pc[self] = "ControllerTESendDagStaleNotif"
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                       IRDoneSet, irCounter, 
                                                       MAX_IR_COUNTER, 
                                                       idThreadWorkingOnIR, 
                                                       workerThreadRanking, 
                                                       flowStatReqStatus, 
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
                                                       currIR_, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       entryIndex, rowIndex, 
                                                       rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, msg, 
                                                       irID, setIRs, currIR, 
                                                       removedIR, 
                                                       controllerFailedModules >>

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                                irCounter, 
                                                                MAX_IR_COUNTER, 
                                                                idThreadWorkingOnIR, 
                                                                workerThreadRanking, 
                                                                flowStatReqStatus, 
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
                                                                currIR_, 
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
                                                                entryIndex, 
                                                                rowIndex, 
                                                                rowRemove, 
                                                                stepOfFailure_c, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, 
                                                                stepOfFailure, 
                                                                msg, irID, 
                                                                setIRs, currIR, 
                                                                removedIR, 
                                                                controllerFailedModules >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF setRemovableIRs[self] # {}
                                                THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = self
                                                     /\ currIR_' = [currIR_ EXCEPT ![self] = CHOOSE x \in setRemovableIRs[self]: TRUE]
                                                     /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = setRemovableIRs[self] \ {currIR_'[self]}]
                                                     /\ RCIRStatus' = [RCIRStatus EXCEPT ![self[1]] = RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE)]
                                                     /\ NIBIRStatus' = NIBIRStatus @@ (nxtRCIRID :> IR_NONE)
                                                     /\ FirstInstall' = FirstInstall @@ (nxtRCIRID :> 0)
                                                     /\ irTypeMapping' = irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIR_'[self]]])
                                                     /\ ir2sw' = ir2sw @@ (nxtRCIRID :> ir2sw[currIR_'[self]])
                                                     /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {nxtRCIRID}]
                                                     /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(ir2sw'[currIR_'[self]], nxtDAGVertices[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                                ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                                     /\ UNCHANGED << FirstInstall, 
                                                                     irTypeMapping, 
                                                                     ir2sw, 
                                                                     RCIRStatus, 
                                                                     NIBIRStatus, 
                                                                     nxtDAG, 
                                                                     setRemovableIRs, 
                                                                     currIR_, 
                                                                     setIRsInDAG >>
                                          /\ UNCHANGED << switchLock, 
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
                                                          RecoveryStatus, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGID, 
                                                          MaxDAGID, DAGState, 
                                                          RCNIBEventQueue, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          RCSeqWorkerStatus, 
                                                          IRDoneSet, irCounter, 
                                                          MAX_IR_COUNTER, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          flowStatReqStatus, 
                                                          masterState, 
                                                          controllerStateNIB, 
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
                                                          currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          prev_dag, seqEvent, 
                                                          worker, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          stepOfFailure_, 
                                                          currDAG, IRSet, 
                                                          currIRMon, 
                                                          nextIRToSent, 
                                                          entryIndex, rowIndex, 
                                                          rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, setIRs, currIR, 
                                                          removedIR, 
                                                          controllerFailedModules >>

ControllerTEAddEdge(self) == /\ pc[self] = "ControllerTEAddEdge"
                             /\ IF setIRsInDAG[self] # {}
                                   THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ controllerLock' = self
                                        /\ currIRInDAG' = [currIRInDAG EXCEPT ![self] = CHOOSE x \in setIRsInDAG[self]: TRUE]
                                        /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = setIRsInDAG[self] \ {currIRInDAG'[self]}]
                                        /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.e = nxtDAG[self].dag.e \cup {<<nxtRCIRID, currIRInDAG'[self]>>}]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                        /\ UNCHANGED nxtRCIRID
                                   ELSE /\ nxtRCIRID' = nxtRCIRID + 1
                                        /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ controllerLock' = self
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]
                                        /\ UNCHANGED << nxtDAG, currIRInDAG, 
                                                        setIRsInDAG >>
                             /\ UNCHANGED << switchLock, FirstInstall, 
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
                                             irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             flowStatReqStatus, masterState, 
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
                                             setRemovableIRs, currIR_, 
                                             nxtDAGVertices, prev_dag, 
                                             seqEvent, worker, 
                                             toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, setIRs, 
                                             currIR, removedIR, 
                                             controllerFailedModules >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' = [DAGEventQueue EXCEPT ![self[1]] = Append(DAGEventQueue[self[1]], [type |-> DAG_NEW, dag_obj |-> nxtDAG[self]])]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
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
                                                  controllerSubmoduleFailStat, 
                                                  switchOrdering, TEEventQueue, 
                                                  DAGQueue, DAGID, MaxDAGID, 
                                                  RCNIBEventQueue, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  RCSeqWorkerStatus, IRDoneSet, 
                                                  irCounter, MAX_IR_COUNTER, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  flowStatReqStatus, 
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
                                                  setRemovableIRs, currIR_, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, entryIndex, 
                                                  rowIndex, rowRemove, 
                                                  stepOfFailure_c, 
                                                  monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  setIRs, currIR, removedIR, 
                                                  controllerFailedModules >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTESendDagStaleNotif(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTEAddEdge(self)
                                         \/ ControllerTESubmitNewDAG(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ controllerIsMaster(self[1])
                               /\ moduleIsUp(self)
                               /\ DAGEventQueue[self[1]] # <<>>
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ seqEvent' = [seqEvent EXCEPT ![self] = Head(DAGEventQueue[self[1]])]
                               /\ DAGEventQueue' = [DAGEventQueue EXCEPT ![self[1]] = Tail(DAGEventQueue[self[1]])]
                               /\ Assert(seqEvent'[self].type \in {DAG_NEW, DAG_STALE}, 
                                         "Failure of assertion at line 1613, column 9.")
                               /\ IF seqEvent'[self].type = DAG_NEW
                                     THEN /\ DAGQueue' = [DAGQueue EXCEPT ![self[1]] = Append(DAGQueue[self[1]], seqEvent'[self].dag_obj)]
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                          /\ UNCHANGED << DAGState, 
                                                          RCSeqWorkerStatus, 
                                                          worker >>
                                     ELSE /\ worker' = [worker EXCEPT ![self] = idWorkerWorkingOnDAG[seqEvent'[self].id]]
                                          /\ IF worker'[self] # DAG_UNLOCK
                                                THEN /\ RCSeqWorkerStatus' = [RCSeqWorkerStatus EXCEPT ![CONT_WORKER_SEQ] = SEQ_WORKER_STALE_SIGNAL]
                                                     /\ pc' = [pc EXCEPT ![self] = "WaitForRCSeqWorkerTerminate"]
                                                     /\ UNCHANGED DAGState
                                                ELSE /\ DAGState' = [DAGState EXCEPT ![seqEvent'[self].id] = DAG_NONE]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                                     /\ UNCHANGED RCSeqWorkerStatus
                                          /\ UNCHANGED DAGQueue
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
                                               DAGID, MaxDAGID, 
                                               RCNIBEventQueue, RCIRStatus, 
                                               RCSwSuspensionStatus, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, IRDoneSet, 
                                               irCounter, MAX_IR_COUNTER, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               flowStatReqStatus, masterState, 
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
                                               setRemovableIRs, currIR_, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, 
                                               toBeScheduledIRs, nextIR, 
                                               stepOfFailure_, currDAG, IRSet, 
                                               currIRMon, nextIRToSent, 
                                               entryIndex, rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, setIRs, currIR, removedIR, 
                                               controllerFailedModules >>

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ idWorkerWorkingOnDAG[seqEvent[self].id] = DAG_UNLOCK
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
                                                     IRDoneSet, irCounter, 
                                                     MAX_IR_COUNTER, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     flowStatReqStatus, 
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
                                                     setRemovableIRs, currIR_, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, entryIndex, 
                                                     rowIndex, rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     setIRs, currIR, removedIR, 
                                                     controllerFailedModules >>

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ controllerIsMaster(self[1])
                                 /\ moduleIsUp(self)
                                 /\ DAGQueue[self[1]] # <<>>
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue[self[1]])]
                                 /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG'[self].id] = self[2]]
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
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
                                                 nxtRCIRID, RCSeqWorkerStatus, 
                                                 IRDoneSet, irCounter, 
                                                 MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 flowStatReqStatus, 
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
                                                 currIR_, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, IRSet, 
                                                 currIRMon, nextIRToSent, 
                                                 entryIndex, rowIndex, 
                                                 rowRemove, stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 setIRs, currIR, removedIR, 
                                                 controllerFailedModules >>

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF ~allIRsInDAGInstalled(self[1], currDAG[self].dag) /\ ~isDAGStale(currDAG[self].id)
                                              THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNext(self[1], currDAG[self].dag)]
                                                   /\ toBeScheduledIRs'[self] # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                   /\ UNCHANGED << idWorkerWorkingOnDAG, 
                                                                   RCSeqWorkerStatus, 
                                                                   IRSet >>
                                              ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG[self].id] = DAG_UNLOCK]
                                                   /\ RCSeqWorkerStatus' = [RCSeqWorkerStatus EXCEPT ![self[2]] = SEQ_WORKER_RUN]
                                                   /\ IRSet' = [IRSet EXCEPT ![self] = currDAG[self].dag.v]
                                                   /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                                   /\ UNCHANGED toBeScheduledIRs
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
                                                        irCounter, 
                                                        MAX_IR_COUNTER, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        flowStatReqStatus, 
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
                                                        currIR_, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, worker, 
                                                        nextIR, stepOfFailure_, 
                                                        currDAG, currIRMon, 
                                                        nextIRToSent, 
                                                        entryIndex, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        irID, setIRs, currIR, 
                                                        removedIR, 
                                                        controllerFailedModules >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                            irCounter, MAX_IR_COUNTER, 
                                            idThreadWorkingOnIR, 
                                            workerThreadRanking, 
                                            flowStatReqStatus, masterState, 
                                            NIBIRStatus, SwSuspensionStatus, 
                                            IRQueueNIB, ingressPkt, ingressIR, 
                                            egressMsg, ofaInMsg, 
                                            ofaOutConfirmation, installerInIR, 
                                            statusMsg, notFailedSet, 
                                            failedElem, obj, failedSet, 
                                            statusResolveMsg, recoveredElem, 
                                            event, topoChangeEvent, 
                                            currSetDownSw, prev_dag_id, init, 
                                            nxtDAG, setRemovableIRs, currIR_, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, seqEvent, 
                                            worker, toBeScheduledIRs, currDAG, 
                                            IRSet, currIRMon, nextIRToSent, 
                                            entryIndex, rowIndex, rowRemove, 
                                            stepOfFailure_c, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, msg, irID, setIRs, 
                                            currIR, removedIR, 
                                            controllerFailedModules >>

AddDeleteIRIRDoneSet(self) == /\ pc[self] = "AddDeleteIRIRDoneSet"
                              /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                              /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                              RCSeqWorkerStatus, irCounter, 
                                              MAX_IR_COUNTER, 
                                              idThreadWorkingOnIR, 
                                              workerThreadRanking, 
                                              flowStatReqStatus, masterState, 
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
                                              setRemovableIRs, currIR_, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, seqEvent, 
                                              worker, toBeScheduledIRs, nextIR, 
                                              stepOfFailure_, currDAG, IRSet, 
                                              currIRMon, nextIRToSent, 
                                              entryIndex, rowIndex, rowRemove, 
                                              stepOfFailure_c, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, msg, irID, setIRs, 
                                              currIR, removedIR, 
                                              controllerFailedModules >>

ScheduleTheIR(self) == /\ pc[self] = "ScheduleTheIR"
                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                             THEN /\ \E num \in 0..2:
                                       stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = num]
                             ELSE /\ stepOfFailure_' = [stepOfFailure_ EXCEPT ![self] = 0]
                       /\ IF (stepOfFailure_'[self] # 1)
                             THEN /\ IRQueueNIB' = Append(IRQueueNIB, [item |-> ([type |-> INSTALL_FLOW, to |-> ir2sw[nextIR[self]], IR |-> nextIR[self]]), id |-> -1, tag |-> NO_TAG])
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
                                       RCSeqWorkerStatus, IRDoneSet, irCounter, 
                                       MAX_IR_COUNTER, idThreadWorkingOnIR, 
                                       workerThreadRanking, flowStatReqStatus, 
                                       masterState, NIBIRStatus, 
                                       SwSuspensionStatus, SetScheduledIRs, 
                                       ingressPkt, ingressIR, egressMsg, 
                                       ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, statusMsg, notFailedSet, 
                                       failedElem, obj, failedSet, 
                                       statusResolveMsg, recoveredElem, event, 
                                       topoChangeEvent, currSetDownSw, 
                                       prev_dag_id, init, nxtDAG, 
                                       setRemovableIRs, currIR_, currIRInDAG, 
                                       nxtDAGVertices, setIRsInDAG, prev_dag, 
                                       seqEvent, worker, nextIR, currDAG, 
                                       IRSet, currIRMon, nextIRToSent, 
                                       entryIndex, rowIndex, rowRemove, 
                                       stepOfFailure_c, monitoringEvent, 
                                       setIRsToReset, resetIR, stepOfFailure, 
                                       msg, irID, setIRs, currIR, removedIR, 
                                       controllerFailedModules >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {} /\ allIRsInDAGInstalled(self[1], currDAG[self].dag)
                                     THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF irTypeMapping[nextIR'[self]].type = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \cup {nextIR'[self]}]
                                                ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR'[self]].flow, INSTALLED_SUCCESSFULLY)}]
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                          /\ UNCHANGED controllerLock
                                     ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF allIRsInDAGInstalled(self[1], currDAG[self].dag) \/ isDAGStale(currDAG[self].id)
                                                THEN /\ pc' = [pc EXCEPT ![self] = "RemoveDAGfromDAGQueue"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << IRDoneSet, nextIR, 
                                                          IRSet >>
                               /\ UNCHANGED << switchLock, FirstInstall, 
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
                                               RCSeqWorkerStatus, irCounter, 
                                               MAX_IR_COUNTER, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               flowStatReqStatus, masterState, 
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
                                               setRemovableIRs, currIR_, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               stepOfFailure_, currDAG, 
                                               currIRMon, nextIRToSent, 
                                               entryIndex, rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, setIRs, currIR, removedIR, 
                                               controllerFailedModules >>

RemoveDAGfromDAGQueue(self) == /\ pc[self] = "RemoveDAGfromDAGQueue"
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ DAGQueue' = [DAGQueue EXCEPT ![self[1]] = Tail(DAGQueue[self[1]])]
                               /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
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
                                               irCounter, MAX_IR_COUNTER, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               flowStatReqStatus, masterState, 
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
                                               setRemovableIRs, currIR_, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, seqEvent, 
                                               worker, toBeScheduledIRs, 
                                               nextIR, stepOfFailure_, currDAG, 
                                               IRSet, currIRMon, nextIRToSent, 
                                               entryIndex, rowIndex, rowRemove, 
                                               stepOfFailure_c, 
                                               monitoringEvent, setIRsToReset, 
                                               resetIR, stepOfFailure, msg, 
                                               irID, setIRs, currIR, removedIR, 
                                               controllerFailedModules >>

ControllerSeqStateReconciliation(self) == /\ pc[self] = "ControllerSeqStateReconciliation"
                                          /\ controllerIsMaster(self[1])
                                          /\ moduleIsUp(self)
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ IF (controllerStateNIB[self].type = STATUS_START_SCHEDULING)
                                                THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[controllerStateNIB[self].next]] = SetScheduledIRs[ir2sw[controllerStateNIB[self].next]]\{controllerStateNIB[self].next}]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED SetScheduledIRs
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]
                                          /\ UNCHANGED << switchLock, 
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
                                                          IRDoneSet, irCounter, 
                                                          MAX_IR_COUNTER, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          flowStatReqStatus, 
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
                                                          currIR_, currIRInDAG, 
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
                                                          entryIndex, rowIndex, 
                                                          rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, setIRs, currIR, 
                                                          removedIR, 
                                                          controllerFailedModules >>

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteIRIRDoneSet(self)
                                \/ ScheduleTheIR(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ RemoveDAGfromDAGQueue(self)
                                \/ ControllerSeqStateReconciliation(self)

controllerIRMonitor(self) == /\ pc[self] = "controllerIRMonitor"
                             /\ controllerIsMaster(self[1])
                             /\ moduleIsUp(self)
                             /\ setIRMonitorShouldSchedule(self[1]) # {}
                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ currIRMon' = [currIRMon EXCEPT ![self] = CHOOSE x \in setIRMonitorShouldSchedule(self[1]): TRUE]
                             /\ IF currIRMon'[self] \in IRDoneSet[self[1]]
                                   THEN /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw[currIRMon'[self]]] = SetScheduledIRs[ir2sw[currIRMon'[self]]] \cup {currIRMon'[self]}]
                                        /\ IRQueueNIB' = Append(IRQueueNIB, [item |-> ([type |-> INSTALL_FLOW, to |-> ir2sw[currIRMon'[self]], IR |-> currIRMon'[self]]), id |-> -1, tag |-> NO_TAG])
                                        /\ UNCHANGED << FirstInstall, 
                                                        irTypeMapping, ir2sw, 
                                                        RCIRStatus, nxtRCIRID, 
                                                        NIBIRStatus >>
                                   ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![self[1]] = RCIRStatus[self[1]] @@ (nxtRCIRID :> IR_NONE)]
                                        /\ NIBIRStatus' = NIBIRStatus @@ (nxtRCIRID :> IR_NONE)
                                        /\ FirstInstall' = FirstInstall @@ (nxtRCIRID :> 0)
                                        /\ irTypeMapping' = irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIRMon'[self]]])
                                        /\ ir2sw' = ir2sw @@ (nxtRCIRID :> ir2sw[currIRMon'[self]])
                                        /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![ir2sw'[nxtRCIRID]] = SetScheduledIRs[ir2sw'[nxtRCIRID]] \cup {nxtRCIRID}]
                                        /\ IRQueueNIB' = Append(IRQueueNIB, [item |-> ([type |-> INSTALL_FLOW, to |-> ir2sw'[nxtRCIRID], IR |-> nxtRCIRID]), id |-> -1, tag |-> NO_TAG])
                                        /\ nxtRCIRID' = nxtRCIRID + 1
                             /\ pc' = [pc EXCEPT ![self] = "controllerIRMonitor"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, swSeqChangedStatus, 
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
                                             RCNIBEventQueue, 
                                             RCSwSuspensionStatus, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             flowStatReqStatus, masterState, 
                                             controllerStateNIB, 
                                             SwSuspensionStatus, ingressPkt, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             event, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             nxtDAG, setRemovableIRs, currIR_, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             nextIRToSent, entryIndex, 
                                             rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, setIRs, 
                                             currIR, removedIR, 
                                             controllerFailedModules >>

rcIRMonitor(self) == controllerIRMonitor(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ controllerIsMaster(self[1])
                          /\ moduleIsUp(self)
                          /\ IRQueueNIB # <<>>
                          /\ canWorkerThreadContinue(self[1], self)
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ rowIndex' = [rowIndex EXCEPT ![self] = getFirstIRIndexToRead(IRQueueNIB, self)]
                          /\ nextIRToSent' = [nextIRToSent EXCEPT ![self] = IRQueueNIB[rowIndex'[self]].item]
                          /\ IF existEquivalentItemWithID(IRQueueNIB, nextIRToSent'[self])
                                THEN /\ entryIndex' = [entryIndex EXCEPT ![self] = getIdOfEquivalentItem(IRQueueNIB, nextIRToSent'[self])]
                                     /\ UNCHANGED irCounter
                                ELSE /\ irCounter' = (irCounter % MAX_IR_COUNTER) + 1
                                     /\ entryIndex' = [entryIndex EXCEPT ![self] = irCounter']
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![rowIndex'[self]].tag = self,
                                                              ![rowIndex'[self]].id = entryIndex'[self]]
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
                                           ELSE /\ IF idThreadWorkingOnIR[entryIndex'[self]] = IR_UNLOCK
                                                      THEN /\ threadWithLowerIDGetsTheLock(self[1], self, nextIRToSent'[self], IRQueueNIB')
                                                           /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![entryIndex'[self]] = self[2]]
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveQueue1"]
                                                           /\ UNCHANGED idThreadWorkingOnIR
                                                /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                                controllerSubmoduleFailStat >>
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
                                          RecoveryStatus, switchOrdering, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, DAGID, MaxDAGID, DAGState, 
                                          RCNIBEventQueue, RCIRStatus, 
                                          RCSwSuspensionStatus, nxtRCIRID, 
                                          idWorkerWorkingOnDAG, 
                                          RCSeqWorkerStatus, IRDoneSet, 
                                          MAX_IR_COUNTER, workerThreadRanking, 
                                          flowStatReqStatus, masterState, 
                                          NIBIRStatus, SwSuspensionStatus, 
                                          SetScheduledIRs, ingressPkt, 
                                          ingressIR, egressMsg, ofaInMsg, 
                                          ofaOutConfirmation, installerInIR, 
                                          statusMsg, notFailedSet, failedElem, 
                                          obj, failedSet, statusResolveMsg, 
                                          recoveredElem, event, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR_, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, seqEvent, 
                                          worker, toBeScheduledIRs, nextIR, 
                                          stepOfFailure_, currDAG, IRSet, 
                                          currIRMon, rowRemove, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, msg, irID, 
                                          setIRs, currIR, removedIR, 
                                          controllerFailedModules >>

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                      THEN /\ IF (workerCanSendTheIR(self[1], nextIRToSent[self]))
                                                 THEN /\ Assert(nextIRToSent[self].type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ}, 
                                                                "Failure of assertion at line 1862, column 21.")
                                                      /\ IF nextIRToSent[self].type \in {INSTALL_FLOW, DELETE_FLOW}
                                                            THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![nextIRToSent[self].IR] = IR_SENT]
                                                                 /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> nextIRToSent[self].IR, state |-> IR_SENT])]
                                                                 /\ UNCHANGED flowStatReqStatus
                                                            ELSE /\ IF nextIRToSent[self].type = FLOW_STAT_REQ
                                                                       THEN /\ flowStatReqStatus' = [flowStatReqStatus EXCEPT ![self[1]][nextIRToSent[self].to] = IR_SENT]
                                                                       ELSE /\ TRUE
                                                                            /\ UNCHANGED flowStatReqStatus
                                                                 /\ UNCHANGED << RCNIBEventQueue, 
                                                                                 NIBIRStatus >>
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                                      /\ UNCHANGED << RCNIBEventQueue, 
                                                                      flowStatReqStatus, 
                                                                      NIBIRStatus >>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadStateReconciliation"]
                                           /\ UNCHANGED << RCNIBEventQueue, 
                                                           flowStatReqStatus, 
                                                           NIBIRStatus >>
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
                                                DAGState, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                RCSeqWorkerStatus, IRDoneSet, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                masterState, 
                                                controllerStateNIB, 
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
                                                setRemovableIRs, currIR_, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, setIRs, currIR, 
                                                removedIR, 
                                                controllerFailedModules >>

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                         THEN /\ \E num \in 0..2:
                                                   stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                         ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                   /\ IF (stepOfFailure_c'[self] # 1)
                                         THEN /\ IF nextIRToSent[self].type = INSTALL_FLOW
                                                    THEN /\ Assert(irTypeMapping[nextIRToSent[self].IR].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                                                   "Failure of assertion at line 1066, column 13 of macro called at line 1878, column 29.")
                                                         /\ Assert(irTypeMapping[nextIRToSent[self].IR].flow \in 1..MaxNumFlows, 
                                                                   "Failure of assertion at line 1067, column 13 of macro called at line 1878, column 29.")
                                                         /\ controller2Switch' = [controller2Switch EXCEPT ![ir2sw[nextIRToSent[self].IR]] = Append(controller2Switch[ir2sw[nextIRToSent[self].IR]], [type |-> irTypeMapping[nextIRToSent[self].IR].type,
                                                                                                                                                                                                      from |-> self[1],
                                                                                                                                                                                                      to |-> nextIRToSent[self].to,
                                                                                                                                                                                                      flow |-> irTypeMapping[nextIRToSent[self].IR].flow])]
                                                    ELSE /\ IF nextIRToSent[self].type = FLOW_STAT_REQ
                                                               THEN /\ controller2Switch' = [controller2Switch EXCEPT ![nextIRToSent[self].to] = Append(controller2Switch[nextIRToSent[self].to], [type |-> FLOW_STAT_REQ,
                                                                                                                                                                                                   from |-> self[1],
                                                                                                                                                                                                   to |-> nextIRToSent[self].to,
                                                                                                                                                                                                   flow |-> nextIRToSent[self].flow])]
                                                               ELSE /\ TRUE
                                                                    /\ UNCHANGED controller2Switch
                                              /\ IF whichSwitchModel(nextIRToSent[self].to) = SW_COMPLEX_MODEL
                                                    THEN /\ switchLock' = <<NIC_ASIC_IN, nextIRToSent[self].to>>
                                                    ELSE /\ switchLock' = <<SW_SIMPLE_ID, nextIRToSent[self].to>>
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
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadUnlockSemaphore"]
                                              /\ UNCHANGED << controllerSubmoduleFailNum, 
                                                              controllerSubmoduleFailStat >>
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
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCNIBEventQueue, 
                                                   RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, irCounter, 
                                                   MAX_IR_COUNTER, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   flowStatReqStatus, 
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
                                                   setRemovableIRs, currIR_, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, entryIndex, 
                                                   rowIndex, rowRemove, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   setIRs, currIR, removedIR, 
                                                   controllerFailedModules >>

ControllerThreadUnlockSemaphore(self) == /\ pc[self] = "ControllerThreadUnlockSemaphore"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                               THEN /\ IF idThreadWorkingOnIR[entryIndex[self]] = self[2]
                                                          THEN /\ idThreadWorkingOnIR' = [idThreadWorkingOnIR EXCEPT ![entryIndex[self]] = IR_UNLOCK]
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
                                                         IRDoneSet, irCounter, 
                                                         MAX_IR_COUNTER, 
                                                         workerThreadRanking, 
                                                         flowStatReqStatus, 
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
                                                         currIR_, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         entryIndex, rowIndex, 
                                                         rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, setIRs, currIR, 
                                                         removedIR, 
                                                         controllerFailedModules >>

RemoveFromScheduledIRSet(self) == /\ pc[self] = "RemoveFromScheduledIRSet"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF (controllerSubmoduleFailNum[self[1]] < getMaxNumSubModuleFailure(self[1]))
                                        THEN /\ \E num \in 0..2:
                                                  stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = num]
                                        ELSE /\ stepOfFailure_c' = [stepOfFailure_c EXCEPT ![self] = 0]
                                  /\ IF (stepOfFailure_c'[self] # 1)
                                        THEN /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![self] = [type |-> NO_STATUS]]
                                             /\ IF (stepOfFailure_c'[self] # 2)
                                                   THEN /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(IRQueueNIB, nextIRToSent[self], self)]
                                                        /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << IRQueueNIB, 
                                                                        rowRemove >>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << controllerStateNIB, 
                                                             IRQueueNIB, 
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
                                                  switchOrdering, TEEventQueue, 
                                                  DAGEventQueue, DAGQueue, 
                                                  DAGID, MaxDAGID, DAGState, 
                                                  RCNIBEventQueue, RCIRStatus, 
                                                  RCSwSuspensionStatus, 
                                                  nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  RCSeqWorkerStatus, IRDoneSet, 
                                                  irCounter, MAX_IR_COUNTER, 
                                                  idThreadWorkingOnIR, 
                                                  workerThreadRanking, 
                                                  flowStatReqStatus, 
                                                  masterState, NIBIRStatus, 
                                                  SwSuspensionStatus, 
                                                  SetScheduledIRs, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
                                                  statusResolveMsg, 
                                                  recoveredElem, event, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR_, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  seqEvent, worker, 
                                                  toBeScheduledIRs, nextIR, 
                                                  stepOfFailure_, currDAG, 
                                                  IRSet, currIRMon, 
                                                  nextIRToSent, entryIndex, 
                                                  rowIndex, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, msg, irID, 
                                                  setIRs, currIR, removedIR, 
                                                  controllerFailedModules >>

ControllerThreadRemoveQueue1(self) == /\ pc[self] = "ControllerThreadRemoveQueue1"
                                      /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ rowRemove' = [rowRemove EXCEPT ![self] = getFirstIndexWith(IRQueueNIB, nextIRToSent[self], self)]
                                      /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove'[self])
                                      /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
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
                                                      IRDoneSet, irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      flowStatReqStatus, 
                                                      masterState, 
                                                      controllerStateNIB, 
                                                      NIBIRStatus, 
                                                      SwSuspensionStatus, 
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
                                                      currIR_, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, entryIndex, 
                                                      rowIndex, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      setIRs, currIR, 
                                                      removedIR, 
                                                      controllerFailedModules >>

ControllerThreadStateReconciliation(self) == /\ pc[self] = "ControllerThreadStateReconciliation"
                                             /\ controllerIsMaster(self[1])
                                             /\ moduleIsUp(self)
                                             /\ IRQueueNIB # <<>>
                                             /\ canWorkerThreadContinue(self[1], self)
                                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                             /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                             /\ IF (controllerStateNIB[self].type = STATUS_LOCKING)
                                                   THEN /\ IF (controllerStateNIB[self].next.type \in {INSTALL_FLOW, DELETE_FLOW})
                                                              THEN /\ IF (NIBIRStatus[controllerStateNIB[self].next] = IR_SENT)
                                                                         THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![controllerStateNIB[self].next] = IR_NONE]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED NIBIRStatus
                                                                   /\ UNCHANGED flowStatReqStatus
                                                              ELSE /\ IF (controllerStateNIB[self].next.type = FLOW_STAT_REQ)
                                                                         THEN /\ IF (flowStatReqStatus[self[1]][controllerStateNIB[self].next] = IR_SENT)
                                                                                    THEN /\ flowStatReqStatus' = [flowStatReqStatus EXCEPT ![self[1]][controllerStateNIB[self].next] = IR_NONE]
                                                                                    ELSE /\ TRUE
                                                                                         /\ UNCHANGED flowStatReqStatus
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED flowStatReqStatus
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
                                                        /\ UNCHANGED << flowStatReqStatus, 
                                                                        NIBIRStatus >>
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]
                                             /\ UNCHANGED << switchLock, 
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
                                                             irCounter, 
                                                             MAX_IR_COUNTER, 
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
                                                             currIR_, 
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
                                                             entryIndex, 
                                                             rowIndex, 
                                                             rowRemove, 
                                                             stepOfFailure_c, 
                                                             monitoringEvent, 
                                                             setIRsToReset, 
                                                             resetIR, 
                                                             stepOfFailure, 
                                                             msg, irID, setIRs, 
                                                             currIR, removedIR, 
                                                             controllerFailedModules >>

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadUnlockSemaphore(self)
                                    \/ RemoveFromScheduledIRSet(self)
                                    \/ ControllerThreadRemoveQueue1(self)
                                    \/ ControllerThreadStateReconciliation(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerIsMaster(self[1])
                                    /\ moduleIsUp(self)
                                    /\ swSeqChangedStatus # <<>>
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ controllerLock' = self
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF canfreeSuspendedSw(monitoringEvent'[self]) /\ SwSuspensionStatus[monitoringEvent'[self].swID] = SW_SUSPEND
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
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
                                                    IRDoneSet, irCounter, 
                                                    MAX_IR_COUNTER, 
                                                    idThreadWorkingOnIR, 
                                                    workerThreadRanking, 
                                                    flowStatReqStatus, 
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
                                                    setRemovableIRs, currIR_, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    seqEvent, worker, 
                                                    toBeScheduledIRs, nextIR, 
                                                    stepOfFailure_, currDAG, 
                                                    IRSet, currIRMon, 
                                                    nextIRToSent, entryIndex, 
                                                    rowIndex, rowRemove, 
                                                    stepOfFailure_c, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, msg, irID, 
                                                    setIRs, currIR, removedIR, 
                                                    controllerFailedModules >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
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
                                                                   irCounter, 
                                                                   MAX_IR_COUNTER, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   flowStatReqStatus, 
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
                                                                   currIR_, 
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
                                                                   entryIndex, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   msg, irID, 
                                                                   setIRs, 
                                                                   currIR, 
                                                                   removedIR, 
                                                                   controllerFailedModules >>

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                        /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                                                               sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND])]
                                        /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED << RCNIBEventQueue, 
                                                        SwSuspensionStatus >>
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
                                             MaxDAGID, DAGState, RCIRStatus, 
                                             RCSwSuspensionStatus, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, 
                                             RCSeqWorkerStatus, IRDoneSet, 
                                             irCounter, MAX_IR_COUNTER, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             flowStatReqStatus, masterState, 
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
                                             setRemovableIRs, currIR_, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, seqEvent, 
                                             worker, toBeScheduledIRs, nextIR, 
                                             stepOfFailure_, currDAG, IRSet, 
                                             currIRMon, nextIRToSent, 
                                             entryIndex, rowIndex, rowRemove, 
                                             stepOfFailure_c, monitoringEvent, 
                                             setIRsToReset, resetIR, 
                                             stepOfFailure, msg, irID, setIRs, 
                                             currIR, removedIR, 
                                             controllerFailedModules >>

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                                           THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![(monitoringEvent[self].swID)] = SW_RECONCILE]
                                                                /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                                                                                     sw |-> monitoringEvent[self].swID,
                                                                                                                                                     state |-> SW_RECONCILE])]
                                                                /\ IRQueueNIB' = Append(IRQueueNIB, [item |-> ([type |-> FLOW_STAT_REQ,
                                                                                                                to |-> (monitoringEvent[self].swID),
                                                                                                                flow |-> ALL_FLOW]), id |-> -1, tag |-> NO_TAG])
                                                           ELSE /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent[self].swID] = SW_RUN]
                                                                /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                                                                                       sw |-> monitoringEvent[self].swID, state |-> SW_RUN])]
                                                                /\ UNCHANGED IRQueueNIB
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                                     /\ UNCHANGED << RCNIBEventQueue, 
                                                                     SwSuspensionStatus, 
                                                                     IRQueueNIB >>
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
                                                          RCIRStatus, 
                                                          RCSwSuspensionStatus, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          RCSeqWorkerStatus, 
                                                          IRDoneSet, irCounter, 
                                                          MAX_IR_COUNTER, 
                                                          idThreadWorkingOnIR, 
                                                          workerThreadRanking, 
                                                          flowStatReqStatus, 
                                                          masterState, 
                                                          controllerStateNIB, 
                                                          NIBIRStatus, 
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
                                                          currIR_, currIRInDAG, 
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
                                                          entryIndex, rowIndex, 
                                                          rowRemove, 
                                                          stepOfFailure_c, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, msg, 
                                                          irID, setIRs, currIR, 
                                                          removedIR, 
                                                          controllerFailedModules >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ controllerIsMaster(self[1])
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus # <<>>
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (controllerStateNIB[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![controllerStateNIB[self].sw] = SW_SUSPEND]
                                                              /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                                                                                     sw |-> monitoringEvent[self].swID, state |-> SW_SUSPEND])]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << RCNIBEventQueue, 
                                                                              SwSuspensionStatus >>
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << switchLock, 
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
                                                                   irCounter, 
                                                                   MAX_IR_COUNTER, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   flowStatReqStatus, 
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
                                                                   currIR_, 
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
                                                                   entryIndex, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_c, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
                                                                   msg, irID, 
                                                                   setIRs, 
                                                                   currIR, 
                                                                   removedIR, 
                                                                   controllerFailedModules >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ controllerIsMaster(self[1])
                                       /\ moduleIsUp(self)
                                       /\ switch2Controller # <<>>
                                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                       /\ controllerLock' = self
                                       /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                       /\ Assert(msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, FLOW_STAT_REPLY}, 
                                                 "Failure of assertion at line 2180, column 9.")
                                       /\ IF msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                             THEN /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg'[self].flow, msg'[self].type)]
                                                  /\ Assert(msg'[self].from = ir2sw[irID'[self]], 
                                                            "Failure of assertion at line 2186, column 13.")
                                                  /\ pc' = [pc EXCEPT ![self] = "ControllerUpdateIRDone"]
                                                  /\ UNCHANGED flowStatReqStatus
                                             ELSE /\ IF msg'[self].type = FLOW_STAT_REPLY
                                                        THEN /\ Assert(msg'[self].status \in {ALL_FLOW, NO_ENTRY, ENTRY_FOUND}, 
                                                                       "Failure of assertion at line 2214, column 21.")
                                                             /\ Assert(SwSuspensionStatus[msg'[self].from] \in {SW_RECONCILE}, 
                                                                       "Failure of assertion at line 2215, column 21.")
                                                             /\ flowStatReqStatus' = [flowStatReqStatus EXCEPT ![self[1]][msg'[self].from] = IR_DONE]
                                                             /\ pc' = [pc EXCEPT ![self] = "changeStatusOfSwToSwRun"]
                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                                             /\ UNCHANGED flowStatReqStatus
                                                  /\ irID' = irID
                                       /\ UNCHANGED << switchLock, 
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
                                                       IRDoneSet, irCounter, 
                                                       MAX_IR_COUNTER, 
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
                                                       currIR_, currIRInDAG, 
                                                       nxtDAGVertices, 
                                                       setIRsInDAG, prev_dag, 
                                                       seqEvent, worker, 
                                                       toBeScheduledIRs, 
                                                       nextIR, stepOfFailure_, 
                                                       currDAG, IRSet, 
                                                       currIRMon, nextIRToSent, 
                                                       entryIndex, rowIndex, 
                                                       rowRemove, 
                                                       stepOfFailure_c, 
                                                       monitoringEvent, 
                                                       setIRsToReset, resetIR, 
                                                       stepOfFailure, setIRs, 
                                                       currIR, removedIR, 
                                                       controllerFailedModules >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                         /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
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
                                                         IRDoneSet, irCounter, 
                                                         MAX_IR_COUNTER, 
                                                         idThreadWorkingOnIR, 
                                                         workerThreadRanking, 
                                                         flowStatReqStatus, 
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
                                                         currIR_, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         seqEvent, worker, 
                                                         toBeScheduledIRs, 
                                                         nextIR, 
                                                         stepOfFailure_, 
                                                         currDAG, IRSet, 
                                                         currIRMon, 
                                                         nextIRToSent, 
                                                         entryIndex, rowIndex, 
                                                         rowRemove, 
                                                         stepOfFailure_c, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, msg, 
                                                         irID, setIRs, currIR, 
                                                         removedIR, 
                                                         controllerFailedModules >>

ControllerUpdateIRDone(self) == /\ pc[self] = "ControllerUpdateIRDone"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
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
                                           /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID[self]] = IR_DONE]
                                           /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD, IR |-> irID[self], state |-> IR_DONE])]
                                           /\ IF msg[self].type = DELETED_SUCCESSFULLY
                                                 THEN /\ removedIR' = [removedIR EXCEPT ![self] = getRemovedIRID(msg[self].flow)]
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerMonUpdateIRNone"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                                      /\ UNCHANGED removedIR
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]
                                           /\ UNCHANGED << FirstInstall, 
                                                           RCNIBEventQueue, 
                                                           NIBIRStatus, 
                                                           removedIR >>
                                /\ UNCHANGED << switchLock, 
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
                                                DAGState, RCIRStatus, 
                                                RCSwSuspensionStatus, 
                                                nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                RCSeqWorkerStatus, IRDoneSet, 
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                flowStatReqStatus, masterState, 
                                                controllerStateNIB, 
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
                                                setRemovableIRs, currIR_, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, setIRs, currIR, 
                                                controllerFailedModules >>

ControllerMonUpdateIRNone(self) == /\ pc[self] = "ControllerMonUpdateIRNone"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerLock' = self
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
                                                   switchOrdering, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, RCIRStatus, 
                                                   RCSwSuspensionStatus, 
                                                   nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   RCSeqWorkerStatus, 
                                                   IRDoneSet, irCounter, 
                                                   MAX_IR_COUNTER, 
                                                   idThreadWorkingOnIR, 
                                                   workerThreadRanking, 
                                                   flowStatReqStatus, 
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
                                                   setRemovableIRs, currIR_, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   seqEvent, worker, 
                                                   toBeScheduledIRs, nextIR, 
                                                   stepOfFailure_, currDAG, 
                                                   IRSet, currIRMon, 
                                                   nextIRToSent, entryIndex, 
                                                   rowIndex, rowRemove, 
                                                   stepOfFailure_c, 
                                                   monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, msg, irID, 
                                                   setIRs, currIR, removedIR, 
                                                   controllerFailedModules >>

changeStatusOfSwToSwRun(self) == /\ pc[self] = "changeStatusOfSwToSwRun"
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                 /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![msg[self].from] = SW_RUN]
                                 /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> TOPO_MOD,
                                                                                                                      sw |-> msg[self].from,
                                                                                                                      state |-> SW_RUN])]
                                 /\ IF msg[self].status = ALL_FLOW
                                       THEN /\ setIRs' = [setIRs EXCEPT ![self] = getSetIRsForSwitch(msg[self].from)]
                                            /\ pc' = [pc EXCEPT ![self] = "changeStatusOfIRsUponAllFlow"]
                                       ELSE /\ IF msg[self].status = ENTRY_FOUND /\ NIBIRStatus[getInstallationIRIDForFlow(msg[self].flow)] # IR_DONE
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "changeStatusOfIRUponEntryFound"]
                                                  ELSE /\ IF msg[self].status = NO_ENTRY /\ NIBIRStatus[getInstallationIRIDForFlow(msg[self].flow)] # IR_NONE
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "changeStatusOfIRUponNoEntry"]
                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                            /\ UNCHANGED setIRs
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
                                                 controllerSubmoduleFailStat, 
                                                 switchOrdering, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 RCIRStatus, 
                                                 RCSwSuspensionStatus, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 RCSeqWorkerStatus, IRDoneSet, 
                                                 irCounter, MAX_IR_COUNTER, 
                                                 idThreadWorkingOnIR, 
                                                 workerThreadRanking, 
                                                 flowStatReqStatus, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 NIBIRStatus, IRQueueNIB, 
                                                 SetScheduledIRs, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, event, 
                                                 topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR_, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, seqEvent, worker, 
                                                 toBeScheduledIRs, nextIR, 
                                                 stepOfFailure_, currDAG, 
                                                 IRSet, currIRMon, 
                                                 nextIRToSent, entryIndex, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_c, 
                                                 monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, msg, irID, 
                                                 currIR, removedIR, 
                                                 controllerFailedModules >>

changeStatusOfIRsUponAllFlow(self) == /\ pc[self] = "changeStatusOfIRsUponAllFlow"
                                      /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ currIR' = [currIR EXCEPT ![self] = CHOOSE x \in setIRs[self]: TRUE]
                                      /\ setIRs' = [setIRs EXCEPT ![self] = setIRs[self] \ {currIR'[self]}]
                                      /\ IF IR2FLOW[currIR'[self]] \in msg[self].flow /\ NIBIRStatus[currIR'[self]] # IR_DONE
                                            THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currIR'[self]] = IR_DONE]
                                                 /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD,
                                                                                                                                      IR |-> currIR'[self],
                                                                                                                                      state |-> IR_DONE])]
                                            ELSE /\ IF IR2FLOW[currIR'[self]] \notin msg[self].flow /\ NIBIRStatus[currIR'[self]] # IR_NONE
                                                       THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currIR'[self]] = IR_NONE]
                                                            /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD,
                                                                                                                                                 IR |-> currIR'[self],
                                                                                                                                                 state |-> IR_NONE])]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED << RCNIBEventQueue, 
                                                                            NIBIRStatus >>
                                      /\ IF setIRs'[self] = {}
                                            THEN /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "changeStatusOfIRsUponAllFlow"]
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
                                                      DAGState, RCIRStatus, 
                                                      RCSwSuspensionStatus, 
                                                      nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      RCSeqWorkerStatus, 
                                                      IRDoneSet, irCounter, 
                                                      MAX_IR_COUNTER, 
                                                      idThreadWorkingOnIR, 
                                                      workerThreadRanking, 
                                                      flowStatReqStatus, 
                                                      masterState, 
                                                      controllerStateNIB, 
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
                                                      currIR_, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      seqEvent, worker, 
                                                      toBeScheduledIRs, nextIR, 
                                                      stepOfFailure_, currDAG, 
                                                      IRSet, currIRMon, 
                                                      nextIRToSent, entryIndex, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_c, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, msg, irID, 
                                                      removedIR, 
                                                      controllerFailedModules >>

changeStatusOfIRUponEntryFound(self) == /\ pc[self] = "changeStatusOfIRUponEntryFound"
                                        /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![IR2FLOW[msg[self].flow]] = IR_DONE]
                                        /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD,
                                                                                                                             IR |-> getInstallationIRIDForFlow(msg[self].flow),
                                                                                                                             state |-> IR_DONE])]
                                        /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
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
                                                        RCIRStatus, 
                                                        RCSwSuspensionStatus, 
                                                        nxtRCIRID, 
                                                        idWorkerWorkingOnDAG, 
                                                        RCSeqWorkerStatus, 
                                                        IRDoneSet, irCounter, 
                                                        MAX_IR_COUNTER, 
                                                        idThreadWorkingOnIR, 
                                                        workerThreadRanking, 
                                                        flowStatReqStatus, 
                                                        masterState, 
                                                        controllerStateNIB, 
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
                                                        currIR_, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        seqEvent, worker, 
                                                        toBeScheduledIRs, 
                                                        nextIR, stepOfFailure_, 
                                                        currDAG, IRSet, 
                                                        currIRMon, 
                                                        nextIRToSent, 
                                                        entryIndex, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_c, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, msg, 
                                                        irID, setIRs, currIR, 
                                                        removedIR, 
                                                        controllerFailedModules >>

changeStatusOfIRUponNoEntry(self) == /\ pc[self] = "changeStatusOfIRUponNoEntry"
                                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                     /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![IR2FLOW[msg[self].flow]] = IR_NONE]
                                     /\ RCNIBEventQueue' = [RCNIBEventQueue EXCEPT ![rc0] = Append(RCNIBEventQueue[rc0], [type |-> IR_MOD,
                                                                                                                          IR |-> getInstallationIRIDForFlow(msg[self].flow),
                                                                                                                          state |-> IR_NONE])]
                                     /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
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
                                                     RCIRStatus, 
                                                     RCSwSuspensionStatus, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     RCSeqWorkerStatus, 
                                                     IRDoneSet, irCounter, 
                                                     MAX_IR_COUNTER, 
                                                     idThreadWorkingOnIR, 
                                                     workerThreadRanking, 
                                                     flowStatReqStatus, 
                                                     masterState, 
                                                     controllerStateNIB, 
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
                                                     setRemovableIRs, currIR_, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     seqEvent, worker, 
                                                     toBeScheduledIRs, nextIR, 
                                                     stepOfFailure_, currDAG, 
                                                     IRSet, currIRMon, 
                                                     nextIRToSent, entryIndex, 
                                                     rowIndex, rowRemove, 
                                                     stepOfFailure_c, 
                                                     monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, msg, irID, 
                                                     setIRs, currIR, removedIR, 
                                                     controllerFailedModules >>

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerUpdateIRDone(self)
                                       \/ ControllerMonUpdateIRNone(self)
                                       \/ changeStatusOfSwToSwRun(self)
                                       \/ changeStatusOfIRsUponAllFlow(self)
                                       \/ changeStatusOfIRUponEntryFound(self)
                                       \/ changeStatusOfIRUponNoEntry(self)

ControllerWatchDogProc(self) == /\ pc[self] = "ControllerWatchDogProc"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerFailedModules' = [controllerFailedModules EXCEPT ![self] = returnControllerFailedModules(self[1])]
                                /\ Cardinality(controllerFailedModules'[self]) > 0
                                /\ \E module \in controllerFailedModules'[self]:
                                     /\ Assert(controllerSubmoduleFailStat[module] = Failed, 
                                               "Failure of assertion at line 2299, column 13.")
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
                                                irCounter, MAX_IR_COUNTER, 
                                                idThreadWorkingOnIR, 
                                                workerThreadRanking, 
                                                flowStatReqStatus, masterState, 
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
                                                setRemovableIRs, currIR_, 
                                                currIRInDAG, nxtDAGVertices, 
                                                setIRsInDAG, prev_dag, 
                                                seqEvent, worker, 
                                                toBeScheduledIRs, nextIR, 
                                                stepOfFailure_, currDAG, IRSet, 
                                                currIRMon, nextIRToSent, 
                                                entryIndex, rowIndex, 
                                                rowRemove, stepOfFailure_c, 
                                                monitoringEvent, setIRsToReset, 
                                                resetIR, stepOfFailure, msg, 
                                                irID, setIRs, currIR, 
                                                removedIR >>

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-da7eb049f12c500b240cce8ac9f718f1
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
CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in FINAL_DAG.v
                                                  /\ \E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x]
                                               \/ /\ x \notin FINAL_DAG.v
                                                  /\ ~\E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x])
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ NIBIRStatus[x] = IR_DONE
                                                       \/ x \notin FINAL_DAG.v)
                                                       
InstallationLivenessProp == <>[] (/\ CorrectDAGInstalled 
                                  /\ CorrectDoneStatusController)

InstallationInvProp == \/ ENABLED Next
                       \/ /\ CorrectDAGInstalled
                          /\ CorrectDoneStatusController

InstallationLivenessProp2 == <>(/\ ~ ENABLED Next
                                /\ CorrectDAGInstalled 
                                /\ CorrectDoneStatusController)
                                  
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
\* Last modified Sun Apr 11 20:47:07 PDT 2021 by root
\* Created Sun Mar 28 03:06:08 PDT 2021 by root

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
CONSTANTS CONT_RC_NIB_EVENT,
          \* id for NIB event handler in RC (type: model value) 
          CONT_TE
          \* id for TE in RC (type: model value) 
          
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
          CONT_OFC_NIB_EVENT,
          \* id for event handler for NIB in OFC (type: model value)  
          CONT_WORKER_SEQ, CONT_BOSS_SEQ 
          \* id for sequencer (type: model value)

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
          NIBT_FIRST_INSTALL,
          NIBT_SW_STATUS
      
      
(***************************************************************************)
(*********************** NIB notification semantics ************************)
(***************************************************************************)
CONSTANTS TOPO_MOD,
          IR_MOD

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
          DELETE_FLOW,
          RECEIVED_SUCCESSFULLY, 
          INSTALLED_SUCCESSFULLY, 
          DELETED_SUCCESSFULLY,
          KEEP_ALIVE,
          FLOW_STAT_REPLY,
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
          IR2FLOW,
          SW_FAIL_ORDERING,
          TOPO_DAG_MAPPING,
          IR2SW,
          MaxNumFlows,
          FINAL_DAG


CONSTANTS SW_UP, SW_DOWN        
CONSTANTS NULL  

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
              FirstInstallOFC = [x \in 1..MaxNumIRs |-> 0],
              FirstInstallNIB = [x \in 1..MaxNumIRs |-> 0],
              sw_fail_ordering_var = SW_FAIL_ORDERING,
              ContProcSet = (({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_RC_NIB_EVENT, CONT_TE}))
                            \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) 
                            \cup (({ofc0} \X {CONT_OFC_NIB_EVENT}))
                            \cup (({ofc0} \X {CONT_EVENT})) 
                            \cup (({ofc0} \X {CONT_MONITOR}))
                            \cup (({nib0} \X {CONT_NIB_RC_EVENT}))
                            \cup (({nib0} \X {CONT_NIB_OFC_EVENT})),
              SwProcSet = (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) 
                            \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) 
                            \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) 
                            \cup (({SW_RESOLVE_PROC} \X SW)),
              \* irTypeMapping is a mapping from irIR to {INSTALL_FLOW, DELETE_FLOW}
              \* it should be encoded into the IR msg from RC to NIB to OFC. However, to 
              \* simplify the abstraction, we keep it in this static mapping.
              irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]],
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
\*              IR2SW = CHOOSE x \in [1..MaxNumIRs -> SW]: ~\E y, z \in DOMAIN x: /\ y > z 
\*                                                                                /\ switchOrdering[x[y]] =< switchOrdering[x[z]],
              ir2sw = IR2SW;
              \* used by the NIB event handler to notify sequencer to recompute tobescheduled-IRs
              NIBUpdateForRC = FALSE,
              \* Copy of NIB states at RC
              controllerStateRC = [x \in ContProcSet |-> [type |-> NO_STATUS]], 
              IRStatusRC = [x \in 1..MaxNumIRs |-> IR_NONE],
              SwSuspensionStatusRC = [x \in SW |-> SW_RUN],
              IRQueueRC = <<>>,
              SetScheduledIRsRC = [y \in SW |-> {}],
              FlagRCNIBEventHandlerFailover = FALSE,
              FlagRCSequencerFailover = FALSE,
              RC_READY = FALSE,
              IRChangeForRC = FALSE,
              TopoChangeForRC = FALSE,
              (*********************** TE Vars ****************************)
              TEEventQueue = [x \in {rc0} |-> <<>>],
              DAGEventQueue = [x \in {rc0} |-> <<>>],
              DAGQueue = [x \in {rc0} |-> <<>>],
              DAGID = 0,
              MaxDAGID = 15,
              DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
              nxtRCIRID = MaxNumIRs + 10,
              idWorkerWorkingOnDAG = [x \in 1..MaxDAGID |-> DAG_UNLOCK],
\*              RCSeqWorkerStatus = (CONT_WORKER_SEQ :> SEQ_WORKER_RUN),
              IRDoneSet = [x \in {rc0} |-> {}],
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
              IRStatusNIB = [x \in 1..MaxNumIRs |-> IR_NONE], 
              SwSuspensionStatusNIB = [x \in SW |-> SW_RUN],
              IRQueueNIB = <<>>,
              \* notificationNIB = [y \in {c0, c1} |-> [RCS |-> [IRQueueNIB |-> <<>>]]], 
              SetScheduledIRs = [y \in SW |-> {}],
              \* @Pooria, consider moving this variable to RC
              (*************** Debug Vars ***********************)
              X2NIB_len = 0,
              \********************** Control plane threads *************************************
              NIBThreadID = <<nib0, CONT_NIB_RC_EVENT>>,
              RCThreadID = <<rc0, CONT_WORKER_SEQ>>,
\*              OFCThreadID = <<ofc0, CONTROLLER_THREAD_POOL[0]>>
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
        \**************************** Installer *****************************
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
                               
        \*************************** switch failure process *****************
        returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}
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
        \****************************** TE ***********************************
        getSetRemovableIRs(CID, swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ IRStatusRC[x] # IR_NONE
                                                                           \/ x \in SetScheduledIRsRC[ir2sw[x]]
                                                                        /\ x \notin nxtDAGV
                                                                        /\ ir2sw[x] \in swSet}
        getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: ir2sw[x] = swID}
        \*************************** Sequencer *******************************
\*        isDependencySatisfiedRC(ir) == ~\E y \in 1..MaxNumIRs: /\ <<y, ir>> \in dependencyGraph
\*                                                             /\ IRStatusRC[y] # IR_DONE 
        isDependencySatisfiedRC(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                        /\ IRStatusRC[y] # IR_DONE                                                    
        
        getSetIRsCanBeScheduledNextRC(DAG)  == {x \in DAG.v: /\ IRStatusRC[x] = IR_NONE
                                                                  /\ isDependencySatisfiedRC(DAG, x)
                                                                  /\ SwSuspensionStatusRC[ir2sw[x]] = SW_RUN
                                                                  /\ x \notin SetScheduledIRsRC[ir2sw[x]]}                                                          
        removeInstalledIR(IRSet) == IF IRSet = {} 
                                    THEN IRSet
                                    ELSE {ir \in IRSet: IRStatusRC[ir] # IR_DONE}
        isRCFailed(id) == controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = Failed
                    /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed
        isRCUp(id) == controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = NotFailed
                    /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
        isRCReconciliation(id) == controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = InReconciliation
                    /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = InReconciliation
        isDAGStale(id) == DAGState[id] # DAG_SUBMIT
        isDAGReady(id) == DAGState[id] = DAG_SUBMIT
        allIRsInDAGInstalled(CID, DAG) == ~\E y \in DAG.v: IRStatusRC[y] # IR_DONE
        
        (****************** OFC (openflow controller) ************************)
        \*************************** Workers *********************************
        isSwitchSuspended(sw, SwSuspensionStatus) == SwSuspensionStatus[sw] = SW_SUSPEND
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
        
        getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                                     /\ IRStatusNIB[x] \notin {IR_DONE, IR_NONE}}
                                                                             
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
        isFinished == \A x \in 1..MaxNumIRs: IRStatusNIB[x] = IR_DONE
                                                                                                                
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
        assert irTypeMapping[s].type \in {INSTALL_FLOW, DELETE_FLOW};
        assert irTypeMapping[s].flow \in 1..MaxNumFlows;
        
\*        controller2Switch[ir2sw[s]] := Append(controller2Switch[ir2sw[s]], [type |-> INSTALL_FLOW,
\*                                                                            to |-> IR2SW[s],
\*                                                                            IR |-> s]);
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
        value := [IRStatusNIB |-> IRStatusNIB, 
                        IRQueueNIB |->IRQueueNIB,
                        SetScheduledIRsNIB |-> SetScheduledIRs, 
                        SwSuspensionStatusNIB |-> SwSuspensionStatusNIB];
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
        if ~\E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans.ops[1].value.IR then
            IRQueueNIB := Append(IRQueueNIB, nextTrans.ops[1].value);
        end if;
        assert nextTrans.ops[2].table = NIBT_CONTROLLER_STATE;
        assert Len(nextTrans.ops[2].key) = 2;
        controllerStateNIB[nextTrans.ops[2].key] := nextTrans.ops[2].value;
    end macro;
    
    macro ScheduleIRInOneStepTransaction()
    begin
        assert nextTrans.ops[1].table = NIBT_IR_QUEUE;
        if ~\E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans.ops[1].value.IR then
            IRQueueNIB := Append(IRQueueNIB, nextTrans.ops[1].value);
        end if;
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
            IRStatusNIB := nextTrans.ops[1];
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
                IRStatusNIB[nextTrans.ops[1].key] := nextTrans.ops[1].value;
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
                IRStatusNIB[nextTrans.ops[1].key] := nextTrans.ops[1].value;
                assert nextTrans.ops[2].table = NIBT_FIRST_INSTALL;
                FirstInstallNIB[nextTrans.ops[2].key] := nextTrans.ops[2].value;
                NIBStateCopy();
                send_NIB_back := "NIB2RC";
        elsif (nextTrans.name = "ChangeIRDoneToNone") then 
            assert Len(nextTrans.ops) = 1;
            assert nextTrans.ops[1].table = NIBT_IR_STATUS;
            IRStatusNIB[nextTrans.ops[1].key] := nextTrans.ops[1].value;
            NIBStateCopy();
            send_NIB_back := "NIB2RC";
        elsif (nextTrans.name = "SwitchDown") then
            assert Len(nextTrans.ops) = 1;
            assert nextTrans.ops[1].table = NIBT_SW_STATUS;
            SwSuspensionStatusNIB[nextTrans.ops[1].key] := nextTrans.ops[1].value;
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
        await isOFCUp(OFCThreadID);
        await swCanReceivePackets(self[2]); 
        await Len(controller2Switch[self[2]]) > 0;
        switchWaitForLock();
        ingressPkt := Head(controller2Switch[self[2]]);
\*        assert ingressPkt.type = INSTALL_FLOW;
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        if ingressPkt.type = INSTALL_FLOW then
            installedIRs := Append(installedIRs, ingressPkt.flow);
            TCAM[self[2]] := Append(TCAM[self[2]], ingressPkt.flow);
            switch2Controller := Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                        from |-> self[2],
                                                        flow |-> ingressPkt.flow]);
        else
            TCAM[self[2]] := removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], ingressPkt.flow));
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
    (********************** Network Information Base *******************)
    (*******************************************************************)
    \* ============ NIB event handler for RC and OFC ==========
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
            IRStatusNIB := IRStatusOFC;
            SwSuspensionStatusNIB := SwSuspensionStatusOFC;
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
    NIBDequeueRCTransaction:
    while TRUE do
        controllerWaitForLockFree();
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
        controllerWaitForLockFree();
        if moduleIsUp(self) then
            NIBProcessTransaction();
            debug := 0;
        else
            FlagNIBRCEventhandlerFailover := TRUE;
            goto NIBForRCReconciliation;
        end if; 
            
        NIBUpdateRCIfAny:   
        controllerWaitForLockFree();
        if moduleIsUp(self) then
            if send_NIB_back = "NIB2RC" then
                await isRCUp(RCThreadID);
                NIB2RC := Append(NIB2RC, [value |-> value]);
            elsif send_NIB_back = "NIB2OFC" then
                await isOFCUp(RCThreadID);
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
        goto NIBDequeueRCTransaction;      
    end process
    
    \* ============ NIB event handler for OFC ==========
    fair process NIBOFCEventHandler \in ({nib0} \X {CONT_NIB_OFC_EVENT})
    variables nextTrans = [name |-> ""], value = NULL, rowRemove=0,
              IR2Remove = 0, send_NIB_back = "", stepOfFailure = 0,
              IRIndex = -1, debug = -1;
    begin
    NIBDequeueOFCTransaction:
    while TRUE do
        controllerWaitForLockFree();
        send_NIB_back := "";
        if moduleIsUp(self) then
            await OFC2NIB # <<>>;
            nextTrans := Head(OFC2NIB);
            OFC2NIB := Tail(OFC2NIB);
        else
            FlagNIBOFCEventhandlerFailover := TRUE;
            goto NIBForOFCReconciliation;
        end if; 
        
        NIBOFCProcessTransaction:
        controllerWaitForLockFree();   
        if moduleIsUp(self) then
            NIBProcessTransaction();
            debug := 0;
        else
            FlagNIBOFCEventhandlerFailover := TRUE;
            goto NIBForOFCReconciliation;
        end if; 
            
        NIBOFCSendBackIfAny:
        controllerWaitForLockFree();   
        if moduleIsUp(self) then
            if send_NIB_back = "NIB2RC" then
                await isRCUp(RCThreadID);
                NIB2RC := Append(NIB2RC, [value |-> value]);
            elsif send_NIB_back = "NIB2OFC" then
                await isOFCUp(RCThreadID);
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
        goto NIBDequeueOFCTransaction;            
    end process
    
    
    \* ======== RC failover =====
    \*
    fair process RCFailoverProc \in ({"proc"} \X {RC_FAILOVER})
    begin 
        RCFailoverResetStates:
            controllerWaitForLockFree();
            \* LSF (Logic for simulating failures)
            \* step 1
            await controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = Failed /\
                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed;
            controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] := InReconciliation ||
            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] := InReconciliation;
            \* step 2: make sure modules in RC fail together
            await FlagRCNIBEventHandlerFailover /\ FlagRCSequencerFailover;
            \* step 3: Clear old messages sent to the old RC
            NIB2RC := <<>>;
            RC2NIB := <<>>;
            \* step 4: empty local tables
            SetScheduledIRsRC := [y \in SW |-> {}];
            IRQueueRC := <<>>;
            \* step 5: make RC unready
            RC_READY := FALSE;
            
            RCReadNIB:
                \* RC reads from NIB assuming that NIB has a dedicated thread for RC failover
                \* such that RC can get NIB tables immediately
                controllerWaitForLockFree();
                await NIB_READY_FOR_RC \/ isNIBUp(NIBThreadID);
                IRStatusRC := IRStatusNIB;
                SwSuspensionStatusRC := SwSuspensionStatusNIB;
                RC_READY := TRUE;
                
\*            RCRecomputeIRQueue
\*                \* Since NIB knows that RC fails, at current moment, OFC is the authority for IRQueue
\*\*                IRQueueRC := IRQueueNIB;
\*                RC_READY := TRUE;
                
            
            \* Change RC status to up
            RCBack2Normal:
            controllerWaitForLockFree();
            controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] := NotFailed ||
            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] := NotFailed;
            NIBUpdateForRC := TRUE;
    end process    
    \* ==========================
    
    \* ============ RC NIB Event Handler ==========
    fair process RCNIBEventHandler \in ({rc0} \X {CONT_RC_NIB_EVENT})
    variables NIBMsg = [value |-> [x |-> <<>>]], isBootStrap = TRUE, 
              sw_id = 0, transaction = <<>>;
    begin
    \* Read states from NIB
    RCSendReadTransaction:
            \* RC needs NIB to 1) notify OFC and 2) get IRStatus
            \* Therefore, if NIB is Failed, RC will stop scheduling new IRs
        assert RC_READY = FALSE;
        controllerWaitForLockFree();
        if isRCFailed(self) then
           FlagRCNIBEventHandlerFailover := TRUE;
           goto RCNIBEventHandlerFailover;
        else
            await isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID);
            transaction := [name |-> "SeqReadNIBStates"];
            RC2NIB := RC2NIB \o <<transaction>>;
        end if;
        
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
                    \*************************Topology Change************************
                    if SwSuspensionStatusRC # NIBMsg.value.SwSuspensionStatusNIB then 
                        sw_id := CHOOSE x \in DOMAIN SwSuspensionStatusRC: SwSuspensionStatusRC[x] # NIBMsg.value.SwSuspensionStatusNIB[x];
                        SwSuspensionStatusRC := NIBMsg.value.SwSuspensionStatusNIB;
                        
                        TEEventQueue[self[1]] := Append(TEEventQueue[self[1]], [type |-> TOPO_MOD, 
                                                              sw |-> sw_id, 
                                                              state |-> SW_SUSPEND]);
                    end if;
                    NIBUpdateForRC := TRUE;
                    isBootStrap := FALSE;
                    \************************TE and Sequencer are waiting for RC_READY to be TRUE to start***********
                    \************************Without failover, this is the single place that changes RC_READY to be TRUE 
                    assert RC_READY = FALSE;
                    RC_READY := TRUE;
                \* If local and remote tables are different
                elsif IRStatusRC # NIBMsg.value.IRStatusNIB 
                    \/ SwSuspensionStatusRC # NIBMsg.value.SwSuspensionStatusNIB then
                    \*************************IR Status Change************************
                    if IRStatusRC # NIBMsg.value.IRStatusNIB then 
                        \* Only modify IRs with status change
                        IRStatusRC := [ir \in DOMAIN IRStatusRC |-> IF ir \in DOMAIN NIBMsg.value.IRStatusNIB 
                                                                       /\ IRStatusRC[ir]# NIBMsg.value.IRStatusNIB[ir]
                                                                    THEN NIBMsg.value.IRStatusNIB[ir]
                                                                    ELSE IRStatusRC[ir]];
                        \* remove DONE IR from SetScheduledIRsRC
                        SetScheduledIRsRC := [sw \in SW |-> IF SetScheduledIRsRC[sw] = {}
                                            THEN SetScheduledIRsRC[sw]
                                            ELSE {ir \in SetScheduledIRsRC[sw]: 
                                                    IRStatusRC[ir] # IR_DONE}];
                        \* remove DONE IR from IRQueueRC
                        IRQueueRC := SelectSeq(IRQueueRC, LAMBDA i: IRStatusRC[i.IR] # IR_DONE);
                        IRChangeForRC := TRUE;
                    end if;
                    \*************************Topology Change************************
                    if SwSuspensionStatusRC # NIBMsg.value.SwSuspensionStatusNIB then 
                        sw_id := CHOOSE x \in DOMAIN SwSuspensionStatusRC: SwSuspensionStatusRC[x] # NIBMsg.value.SwSuspensionStatusNIB[x];
                        SwSuspensionStatusRC := NIBMsg.value.SwSuspensionStatusNIB;
                        
                        TEEventQueue[self[1]] := Append(TEEventQueue[self[1]], [type |-> TOPO_MOD, 
                                                              sw |-> sw_id, 
                                                              state |-> SW_SUSPEND]);
                        TopoChangeForRC := TRUE;
                    end if;
                    NIBUpdateForRC := TRUE;
                end if;
            end if;
        end while;    
    RCNIBEventHandlerFailover:
        controllerWaitForLockFree();
        await controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = NotFailed /\
                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed;
        isBootStrap := FALSE;
        goto RCNIBEventHanderProc;
    end process
 
 
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
        await RC_READY = TRUE;
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
                    
                    \* boss sequencer replacement
                    TEWaitSequencerTerminate:
                    if idWorkerWorkingOnDAG[prev_dag_id] # DAG_UNLOCK then
                            await idWorkerWorkingOnDAG[prev_dag_id] = DAG_UNLOCK;
                            DAGState[prev_dag_id] := DAG_NONE;
                    else
                        DAGState[prev_dag_id] := DAG_NONE;
                    end if;
                    \*-------------------------
                
\*                    ControllerTESendDagStaleNotif:
\*                        controllerWaitForLockFree();
\*                        DAGEventQueue[self[1]] := Append(DAGEventQueue[self[1]], [type |-> DAG_STALE, id |-> prev_dag_id]);
                
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
                IRStatusRC := IRStatusRC @@ (nxtRCIRID :> IR_NONE);
                IRStatusNIB := IRStatusNIB @@ (nxtRCIRID :> IR_NONE);
\*                FirstInstall := FirstInstall @@ (nxtRCIRID :> 0);
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
            \* boss sequencer replacement
            DAGQueue[self[1]] := Append(DAGQueue[self[1]], nxtDAG);
    end while;
    end process
    \* =================================
    
\*    \* ========= Boss Sequencer ========
\*    fair process controllerBossSequencer \in ({rc0} \X {CONT_BOSS_SEQ})
\*    variables seqEvent = [type |-> 0], worker = 0;
\*    begin
\*    ControllerBossSeqProc:
\*    while TRUE do
\*        await controllerIsMaster(self[1]);
\*        await moduleIsUp(self);
\*        await DAGEventQueue[self[1]] # <<>>;
\*    
\*        controllerWaitForLockFree();
\*        seqEvent := Head(DAGEventQueue[self[1]]);
\*        DAGEventQueue[self[1]] := Tail(DAGEventQueue[self[1]]);
\*        assert seqEvent.type \in {DAG_NEW, DAG_STALE};
\*        if seqEvent.type = DAG_NEW then
\*            DAGQueue[self[1]] := Append(DAGQueue[self[1]], seqEvent.dag_obj);
\*        else
\*            worker := idWorkerWorkingOnDAG[seqEvent.id];
\*            if worker # DAG_UNLOCK then
\*\*                RCSeqWorkerStatus[CONT_WORKER_SEQ] := SEQ_WORKER_STALE_SIGNAL;
\*                WaitForRCSeqWorkerTerminate:
\*                    await idWorkerWorkingOnDAG[seqEvent.id] = DAG_UNLOCK;
\*                    DAGState[seqEvent.id] := DAG_NONE;
\*            else
\*                DAGState[seqEvent.id] := DAG_NONE;
\*            end if;
\*        end if;
\*    end while;
\*    end process
    \* =================================
    
    \* ======== Worker Sequencers =======
    \* Sequencer periodically gets all the valid IRs (those with satisfied
    \* dependencies), run its scheduling mechanism to decide the order of
    \* scheduling and then, schedule the IR
    fair process controllerSequencer \in ({rc0} \X {CONT_WORKER_SEQ})
    variables toBeScheduledIRs = {}, 
                nextIR = 0, 
                transaction = <<>>, 
                stepOfFailure = 0, 
                currDAG = [dag |-> 0], 
                IRSet = {},
                key = "", 
                op1 = [table |-> ""], 
                op2 = [table |-> ""],
                debug = FALSE;
    begin
    
    RCWorkerSeqProc:
    while TRUE do
        \* ControlSeqProc consists of one operation;
        \* 1) Retrieving the set of valid IRs
        await controllerIsMaster(self[1]);
        await moduleIsUp(self);
        await RC_READY = TRUE;
        await DAGQueue[self[1]] # <<>>;
        controllerWaitForLockFree();
        currDAG := Head(DAGQueue[self[1]]);
        idWorkerWorkingOnDAG[currDAG.id] := self[2];
        \* Every time a new DAG comes, the sequencer should try to compute next IRs
        NIBUpdateForRC := TRUE;
        
\*        ControllerWorkerSeqScheduleDAG:
        RCWorkerSeqScheduleDAG:
            while ~allIRsInDAGInstalled(self[1], currDAG.dag) /\ ~isDAGStale(currDAG.id)do
                controllerWaitForLockFree();
                    if isRCFailed(self) then
                        FlagRCSequencerFailover := TRUE;
                        goto RCSequencerFailover;
                    else
                        await NIBUpdateForRC;
                        toBeScheduledIRs := getSetIRsCanBeScheduledNextRC(currDAG.dag);
\*                        await toBeScheduledIRs # {};
                        if toBeScheduledIRs = {} then
                            if TopoChangeForRC then 
                                goto RemoveDAGFromQueue;
                            else
                                NIBUpdateForRC := FALSE;
                                goto RCWorkerSeqScheduleDAG;
                            end if;
                        end if;
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
                    if isRCFailed(self) then
                        FlagRCSequencerFailover := TRUE;
                        goto RCSequencerFailover;
                    else
                        nextIR := CHOOSE x \in toBeScheduledIRs: TRUE;
                        SetScheduledIRsRC[ir2sw[nextIR]] := SetScheduledIRsRC[ir2sw[nextIR]] \cup {nextIR};
                        toBeScheduledIRs := toBeScheduledIRs\{nextIR};
                        IRQueueRC := Append(IRQueueRC, [IR |-> nextIR, tag |-> NO_TAG]);
                    end if;     

                    AddDeleteIRDoneSet:      
                        controllerWaitForLockFree();
                        if irTypeMapping[nextIR].type = INSTALL_FLOW then
                            IRDoneSet[self[1]] := IRDoneSet[self[1]] \cup {nextIR};
                        else
                            IRDoneSet[self[1]] := IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
                        end if;
                                        
                    \* Send RCScheduleIRInOneStep transaction to NIB
                    RCSendIR2NIB:
                    controllerWaitForLockFree();
                    if isRCFailed(self) then
                        FlagRCSequencerFailover := TRUE;
                        goto RCSequencerFailover;
                    else
                        await isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID);
                        op1 := [table |-> NIBT_IR_QUEUE, key |-> NULL, value |-> [IR |-> nextIR, tag |-> NO_TAG]];
                        transaction := [name |-> "RCScheduleIRInOneStep", ops |-> <<op1>>];
                        RC2NIB := RC2NIB \o <<transaction>>;  
            
                        if toBeScheduledIRs = {} \/ isDAGStale(currDAG.id) then
                            goto RCWorkerSeqScheduleDAG;
                        end if;
                    end if;          
                end while;                                                
            end while;
            \* Remove DAG from the DAG Queue
            RemoveDAGFromQueue:
                controllerWaitForLockFree();
                if TopoChangeForRC then 
                    \* TE could be slower to update DAG to be STALE 
                    await isDAGStale(currDAG.id);
                    TopoChangeForRC := FALSE;    
                end if;
                idWorkerWorkingOnDAG[currDAG.id] := DAG_UNLOCK;
\*                RCSeqWorkerStatus[self[2]] := SEQ_WORKER_RUN;
                IRSet := currDAG.dag.v;
            
            AddDeleteDAGIRDoneSet:
                while IRSet # {} /\ allIRsInDAGInstalled(self[1], currDAG.dag) do
                    controllerAcquireLock();
                    nextIR := CHOOSE x \in IRSet: TRUE;
                    if irTypeMapping[nextIR].type = INSTALL_FLOW then
                        IRDoneSet[self[1]] := IRDoneSet[self[1]] \cup {nextIR};
                    else
                        IRDoneSet[self[1]] := IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR].flow, INSTALLED_SUCCESSFULLY)}
                    end if;
                    IRSet := IRSet \ {nextIR};
                end while; 
                if allIRsInDAGInstalled(self[1], currDAG.dag) \/ isDAGStale(currDAG.id) then
\*                    RemoveDAGfromDAGQueue: 
                        controllerWaitForLockFree();
                        DAGQueue[self[1]] := Tail(DAGQueue[self[1]]);
                end if;
                controllerReleaseLock();
                
    end while;
    RCSequencerFailover:
        controllerWaitForLockFree();
        toBeScheduledIRs := {};
        await controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = NotFailed /\
                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed;
        goto RCWorkerSeqScheduleDAG;
    
    end process
    \* ========================== 
    
    
    
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
\*    fair process OFCFailureProc \in ( {"proc"} \X {OFC_FAILURE})
\*    begin 
\*        OFCFailure:
\*            controllerWaitForLockFree();
\*            controllerSubmoduleFailStat[OFCThreadID] := Failed ||
\*            controllerSubmoduleFailStat[<<ofc0,CONT_MONITOR>>] := Failed ||
\*            controllerSubmoduleFailStat[<<ofc0,CONT_OFC_NIB_EVENT>>] := Failed;        
\*    end process    
    \* ==========================
    
    \* ======== NIB failure =====
    fair process NIBFailureProc \in ( {"proc"} \X {NIB_FAILURE})
    begin 
        NIBFailure:
            controllerWaitForLockFree();
            controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] := Failed ||
            controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] := Failed;        
    end process    
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
                        
            \* We are assuming a dedicated connection between switch and OFC for failover
            OFCReadSwitches:
                controllerWaitForLockFree();
                IRStatusOFC := [x \in 1..MaxNumIRs |-> IF x \in rangeSeq(installedIRs) 
                                                       THEN IR_DONE
                                                       ELSE IRStatusOFC[x]];
                FirstInstallOFC := [x \in 1..MaxNumIRs |-> IF IRStatusOFC[x] = IR_DONE
                                                           THEN FirstInstallOFC[x] + 1
                                                           ELSE FirstInstallOFC[x]];                                       
                OFC_READY := TRUE;

            OFCReadNIB:
                controllerWaitForLockFree();
                \* If NIB is up, OFC can read it directly.
                \* If NIB is in reconciliation, NIB_READY_FOR_OFC could be false, therefore OFC should wait.
                await NIB_READY_FOR_OFC \/ isNIBUp(NIBThreadID);
                \* bug-04-26-2021: IRQueueOFC := SelectSeq(IRQueueNIB, LAMBDA i: IRStatusOFC[i.IR] # IR_DONE);
                IRQueueOFC := SelectSeq(IRQueueRC, LAMBDA i: IRStatusOFC[i.IR] # IR_DONE);
              
                
                

            \* Change RC status to up
            OFCBack2Normal:
\*                IRStatus := IRStatusOFC;
                controllerWaitForLockFree();
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
    \* OFCNIBEventHandler only needs to handle IR-related messages from RC
    \* When it fails over, it reads switch status (up/down) from switches directly
    fair process OFCNIBEventHandler \in ({ofc0} \X {CONT_OFC_NIB_EVENT})
    variables NIBMsg = [value |-> [x |-> <<>>]], isBootStrap = TRUE,
              localIRSet = {}, NIBIRSet = {}, newIRSet = {}, newIR = -1;
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
                \* This condition signals the new IR addition, so we need to add the new IR to IRStatusOFC
                if Cardinality(DOMAIN NIBMsg.value.IRStatusNIB) > Cardinality(DOMAIN IRStatusOFC) then
                    newIRSet := DOMAIN NIBMsg.value.IRStatusNIB \ DOMAIN IRStatusOFC;
                    assert Cardinality(newIRSet)=1;
                    newIR := CHOOSE x \in newIRSet: TRUE;
                    IRStatusOFC := IRStatusOFC @@ (newIR :> IR_NONE);
                end if;
                localIRSet := {IRQueueOFC[i].IR: i \in DOMAIN IRQueueOFC};
                NIBIRSet := {NIBMsg.value.IRQueueNIB[i].IR: i \in DOMAIN NIBMsg.value.IRQueueNIB};
                if localIRSet # NIBIRSet then
                    \* enqueue new IRs to be scheduled
                    \* "i.IR not \in DOMAIN IRStatusOFC" could happen if a new DAG is scheduled
                    IRQueueOFC := SelectSeq(NIBMsg.value.IRQueueNIB, LAMBDA i: i.IR \notin DOMAIN IRStatusOFC \/ IRStatusOFC[i.IR] = IR_NONE);
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
    OFCThreadGetNextIR:
    while TRUE do
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
                await isNIBUp(NIBThreadID);
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
                            await isNIBUp(NIBThreadID);
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
        goto OFCThreadGetNextIR;
    end process
    \* ==========================


    
    \* ===== OFC Switch Event Handler ======
    \* The role of EH is to detect switch up/down
    fair process controllerEventHandler \in ({ofc0} \X {CONT_EVENT})
    variables monitoringEvent = [type |-> 0], setIRsToReset = {}, 
              resetIR = 0, stepOfFailure = 0, transaction = <<>>,
              topo_change = [table |-> ""];
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
          
         if shouldSuspendSw(monitoringEvent) /\ SwSuspensionStatusOFC[monitoringEvent.swID] = SW_RUN then
         
            \* ControllerSuspendSW only suspends the SW (so the rest of the system does not work on
            \* the tasks related to this switch anymore).
            \* Here, Due to performance reasons, we defer the task of resetting status of IRs to 
            \* the time that the switch is recovered (Lazy evaluation) because; First, it might not
            \* be necessary (for example, the switch may have installed the IR). Second, the switch
            \* may have faced a permanent failure in which these IRs are not valid anymore.                 
            OFCSuspendSWLocally: 
                controllerWaitForLockFree();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    SwSuspensionStatusOFC[monitoringEvent.swID] := SW_SUSPEND;        
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;  
                
            OFCSuspendSWRemotely:
                controllerWaitForLockFree();
                controllerModuleFailOrNot();
                if (controllerSubmoduleFailStat[self] = NotFailed) then
                    await isNIBUp(NIBThreadID);
                    topo_change := [table |-> NIBT_SW_STATUS, key |-> monitoringEvent.swID, value |-> SW_SUSPEND];
                    transaction := [name |-> "SwitchDown", ops |-> <<topo_change>>];
                    OFC2NIB := OFC2NIB \o <<transaction>>;        
                else
                    goto ControllerEventHandlerStateReconciliation;
                end if;  
                
         else
            assert FALSE;
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
         controllerReleaseLock();
         if (controllerStateNIB[self].type = START_RESET_IR) then
            SwSuspensionStatusOFC[controllerStateNIB[self].sw] := SW_SUSPEND;
         end if;
        goto ControllerEventHandlerProc;
    end process
    \* ==========================
    
    \* == Monitoring Server ===== 
    \* The role of MS is to communicate with switches on IR installation status
    fair process controllerMonitoringServer \in ({ofc0} \X {CONT_MONITOR})
    variable irID = 0, removedIR = 0, msg = [type |-> 0], 
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
        await switch2Controller # <<>>;
        controllerAcquireLock();
        msg := Head(switch2Controller);
        assert msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, FLOW_STAT_REPLY};

        if msg.type \in {INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY} then
                \* If msg type is INSTALLED_SUCCESSFULLY, we have to change the IR status
                \* to IR_DONE. 
                irID := getIRIDForFlow(msg.flow, msg.type);
                assert msg.from = ir2sw[irID];
                
                OFCUpdateIRDone:
                    controllerWaitForLockFree(); 
                    if isOFCFailed(self) then
                        FlagOFCMonitorFailover := TRUE;
                        goto OFCMonitorFailover;
                    else
                        IRStatusOFC[irID] := IR_DONE; 
                        FirstInstallOFC[irID] := 1;
                    end if;
                \* update NIB
                OFCUpdateNIBIRDONE:
                    controllerWaitForLockFree(); 
                    if isOFCFailed(self) then
                        FlagOFCMonitorFailover := TRUE;
                        goto OFCMonitorFailover;
                    else
                        await isNIBUp(NIBThreadID);
                        op_ir_status_change := [table |-> NIBT_IR_STATUS, key |-> irID, value |-> IR_DONE];
                        op_first_install  := [table |-> NIBT_FIRST_INSTALL, key |-> irID, value |-> 1];
                        transaction := [name |-> "FirstInstallIR", 
                                        ops |-> <<op_ir_status_change, op_first_install>>];
                        OFC2NIB := OFC2NIB \o <<transaction>>;
                    end if;
                OFCUpdateIRNone:
                if msg.type = DELETED_SUCCESSFULLY then
                    removedIR := getRemovedIRID(msg.flow);
                    
                        controllerWaitForLockFree(); 
                        if isOFCFailed(self) then
                            FlagOFCMonitorFailover := TRUE;
                            goto OFCMonitorFailover;
                        else
                            IRStatusOFC[removedIR] := IR_NONE; 
                            FirstInstallOFC[removedIR] := 0;
                        end if;
                        
                    OFCUpdateNIBIRNone:
                        controllerWaitForLockFree(); 
                        if isOFCFailed(self) then
                            FlagOFCMonitorFailover := TRUE;
                            goto OFCMonitorFailover;
                        else
                            await isNIBUp(NIBThreadID);
                            op_ir_status_change := [table |-> NIBT_IR_STATUS, key |-> removedIR, value |-> IR_NONE];
                            op_first_install  := [table |-> NIBT_FIRST_INSTALL, key |-> removedIR, value |-> 0];
                            transaction := [name |-> "FirstInstallIR", 
                                        ops |-> <<op_ir_status_change, op_first_install>>];
                            OFC2NIB := OFC2NIB \o <<transaction>>;
                        end if;    
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
\* Process variable value of process NIBFailoverProc at line 1673 col 15 changed to value_
\* Process variable nextTrans of process NIBRCEventHandler at line 1715 col 15 changed to nextTrans_
\* Process variable value of process NIBRCEventHandler at line 1715 col 42 changed to value_N
\* Process variable rowRemove of process NIBRCEventHandler at line 1715 col 56 changed to rowRemove_
\* Process variable IR2Remove of process NIBRCEventHandler at line 1716 col 15 changed to IR2Remove_
\* Process variable send_NIB_back of process NIBRCEventHandler at line 1716 col 30 changed to send_NIB_back_
\* Process variable stepOfFailure of process NIBRCEventHandler at line 1716 col 50 changed to stepOfFailure_
\* Process variable IRIndex of process NIBRCEventHandler at line 1717 col 15 changed to IRIndex_
\* Process variable debug of process NIBRCEventHandler at line 1717 col 29 changed to debug_
\* Process variable rowRemove of process NIBOFCEventHandler at line 1769 col 56 changed to rowRemove_N
\* Process variable stepOfFailure of process NIBOFCEventHandler at line 1770 col 50 changed to stepOfFailure_N
\* Process variable debug of process NIBOFCEventHandler at line 1771 col 29 changed to debug_N
\* Process variable NIBMsg of process RCNIBEventHandler at line 1871 col 15 changed to NIBMsg_
\* Process variable isBootStrap of process RCNIBEventHandler at line 1871 col 50 changed to isBootStrap_
\* Process variable transaction of process RCNIBEventHandler at line 1872 col 26 changed to transaction_
\* Process variable transaction of process controllerSequencer at line 2108 col 17 changed to transaction_c
\* Process variable stepOfFailure of process controllerSequencer at line 2109 col 17 changed to stepOfFailure_c
\* Process variable op1 of process controllerSequencer at line 2113 col 17 changed to op1_
\* Process variable transaction of process OFCFailoverProc at line 2298 col 15 changed to transaction_O
\* Process variable NIBMsg of process OFCNIBEventHandler at line 2365 col 15 changed to NIBMsg_O
\* Process variable stepOfFailure of process controllerWorkerThreads at line 2404 col 64 changed to stepOfFailure_co
\* Process variable transaction of process controllerWorkerThreads at line 2405 col 15 changed to transaction_co
\* Process variable op_ir_status_change of process controllerWorkerThreads at line 2407 col 15 changed to op_ir_status_change_
\* Process variable transaction of process controllerEventHandler at line 2506 col 47 changed to transaction_con
VARIABLES switchLock, controllerLock, FirstInstallOFC, FirstInstallNIB, 
          sw_fail_ordering_var, ContProcSet, SwProcSet, irTypeMapping, 
          swSeqChangedStatus, controller2Switch, switch2Controller, 
          switchStatus, installedIRs, NicAsic2OfaBuff, Ofa2NicAsicBuff, 
          Installer2OfaBuff, Ofa2InstallerBuff, TCAM, controlMsgCounter, 
          RecoveryStatus, controllerSubmoduleFailNum, 
          controllerSubmoduleFailStat, switchOrdering, dependencyGraph, ir2sw, 
          NIBUpdateForRC, controllerStateRC, IRStatusRC, SwSuspensionStatusRC, 
          IRQueueRC, SetScheduledIRsRC, FlagRCNIBEventHandlerFailover, 
          FlagRCSequencerFailover, RC_READY, IRChangeForRC, TopoChangeForRC, 
          TEEventQueue, DAGEventQueue, DAGQueue, DAGID, MaxDAGID, DAGState, 
          nxtRCIRID, idWorkerWorkingOnDAG, IRDoneSet, idThreadWorkingOnIR, 
          workerThreadRanking, controllerStateOFC, IRStatusOFC, IRQueueOFC, 
          SwSuspensionStatusOFC, SetScheduledIRsOFC, FlagOFCWorkerFailover, 
          FlagOFCMonitorFailover, FlagOFCNIBEventHandlerFailover, OFCThreadID, 
          OFC_READY, NIB2OFC, NIB2RC, X2NIB, OFC2NIB, RC2NIB, FlagNIBFailover, 
          FlagNIBRCEventhandlerFailover, FlagNIBOFCEventhandlerFailover, 
          NIB_READY_FOR_RC, NIB_READY_FOR_OFC, masterState, 
          controllerStateNIB, IRStatusNIB, SwSuspensionStatusNIB, IRQueueNIB, 
          SetScheduledIRs, X2NIB_len, NIBThreadID, RCThreadID, pc

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

swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed


returnSwitchElementsNotFailed(sw) == {x \in DOMAIN switchStatus[sw]: switchStatus[sw][x] = NotFailed}

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


getSetRemovableIRs(CID, swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ IRStatusRC[x] # IR_NONE
                                                                   \/ x \in SetScheduledIRsRC[ir2sw[x]]
                                                                /\ x \notin nxtDAGV
                                                                /\ ir2sw[x] \in swSet}
getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: ir2sw[x] = swID}



isDependencySatisfiedRC(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                /\ IRStatusRC[y] # IR_DONE

getSetIRsCanBeScheduledNextRC(DAG)  == {x \in DAG.v: /\ IRStatusRC[x] = IR_NONE
                                                          /\ isDependencySatisfiedRC(DAG, x)
                                                          /\ SwSuspensionStatusRC[ir2sw[x]] = SW_RUN
                                                          /\ x \notin SetScheduledIRsRC[ir2sw[x]]}
removeInstalledIR(IRSet) == IF IRSet = {}
                            THEN IRSet
                            ELSE {ir \in IRSet: IRStatusRC[ir] # IR_DONE}
isRCFailed(id) == controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = Failed
            /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed
isRCUp(id) == controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = NotFailed
            /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
isRCReconciliation(id) == controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = InReconciliation
            /\ controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = InReconciliation
isDAGStale(id) == DAGState[id] # DAG_SUBMIT
isDAGReady(id) == DAGState[id] = DAG_SUBMIT
allIRsInDAGInstalled(CID, DAG) == ~\E y \in DAG.v: IRStatusRC[y] # IR_DONE



isSwitchSuspended(sw, SwSuspensionStatus) == SwSuspensionStatus[sw] = SW_SUSPEND



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

getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ ir2sw[x] = SID
                                             /\ IRStatusNIB[x] \notin {IR_DONE, IR_NONE}}


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


isFinished == \A x \in 1..MaxNumIRs: IRStatusNIB[x] = IR_DONE

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, obj, failedSet, 
          statusResolveMsg, recoveredElem, value_, nextTrans_, value_N, 
          rowRemove_, IR2Remove_, send_NIB_back_, stepOfFailure_, IRIndex_, 
          debug_, nextTrans, value, rowRemove_N, IR2Remove, send_NIB_back, 
          stepOfFailure_N, IRIndex, debug_N, NIBMsg_, isBootStrap_, sw_id, 
          transaction_, topoChangeEvent, currSetDownSw, prev_dag_id, init, 
          nxtDAG, setRemovableIRs, currIR, currIRInDAG, nxtDAGVertices, 
          setIRsInDAG, prev_dag, toBeScheduledIRs, nextIR, transaction_c, 
          stepOfFailure_c, currDAG, IRSet, key, op1_, op2, debug, 
          transaction_O, IRQueueTmp, NIBMsg_O, isBootStrap, localIRSet, 
          NIBIRSet, newIRSet, newIR, nextIRToSent, rowIndex, rowRemove, 
          stepOfFailure_co, transaction_co, NIBMsg, op1, IRQueue, 
          op_ir_status_change_, removeIR, monitoringEvent, setIRsToReset, 
          resetIR, stepOfFailure, transaction_con, topo_change, irID, 
          removedIR, msg, op_ir_status_change, op_first_install, transaction

vars == << switchLock, controllerLock, FirstInstallOFC, FirstInstallNIB, 
           sw_fail_ordering_var, ContProcSet, SwProcSet, irTypeMapping, 
           swSeqChangedStatus, controller2Switch, switch2Controller, 
           switchStatus, installedIRs, NicAsic2OfaBuff, Ofa2NicAsicBuff, 
           Installer2OfaBuff, Ofa2InstallerBuff, TCAM, controlMsgCounter, 
           RecoveryStatus, controllerSubmoduleFailNum, 
           controllerSubmoduleFailStat, switchOrdering, dependencyGraph, 
           ir2sw, NIBUpdateForRC, controllerStateRC, IRStatusRC, 
           SwSuspensionStatusRC, IRQueueRC, SetScheduledIRsRC, 
           FlagRCNIBEventHandlerFailover, FlagRCSequencerFailover, RC_READY, 
           IRChangeForRC, TopoChangeForRC, TEEventQueue, DAGEventQueue, 
           DAGQueue, DAGID, MaxDAGID, DAGState, nxtRCIRID, 
           idWorkerWorkingOnDAG, IRDoneSet, idThreadWorkingOnIR, 
           workerThreadRanking, controllerStateOFC, IRStatusOFC, IRQueueOFC, 
           SwSuspensionStatusOFC, SetScheduledIRsOFC, FlagOFCWorkerFailover, 
           FlagOFCMonitorFailover, FlagOFCNIBEventHandlerFailover, 
           OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
           FlagNIBFailover, FlagNIBRCEventhandlerFailover, 
           FlagNIBOFCEventhandlerFailover, NIB_READY_FOR_RC, 
           NIB_READY_FOR_OFC, masterState, controllerStateNIB, IRStatusNIB, 
           SwSuspensionStatusNIB, IRQueueNIB, SetScheduledIRs, X2NIB_len, 
           NIBThreadID, RCThreadID, pc, ingressPkt, ingressIR, egressMsg, 
           ofaInMsg, ofaOutConfirmation, installerInIR, statusMsg, 
           notFailedSet, failedElem, obj, failedSet, statusResolveMsg, 
           recoveredElem, value_, nextTrans_, value_N, rowRemove_, IR2Remove_, 
           send_NIB_back_, stepOfFailure_, IRIndex_, debug_, nextTrans, value, 
           rowRemove_N, IR2Remove, send_NIB_back, stepOfFailure_N, IRIndex, 
           debug_N, NIBMsg_, isBootStrap_, sw_id, transaction_, 
           topoChangeEvent, currSetDownSw, prev_dag_id, init, nxtDAG, 
           setRemovableIRs, currIR, currIRInDAG, nxtDAGVertices, setIRsInDAG, 
           prev_dag, toBeScheduledIRs, nextIR, transaction_c, stepOfFailure_c, 
           currDAG, IRSet, key, op1_, op2, debug, transaction_O, IRQueueTmp, 
           NIBMsg_O, isBootStrap, localIRSet, NIBIRSet, newIRSet, newIR, 
           nextIRToSent, rowIndex, rowRemove, stepOfFailure_co, 
           transaction_co, NIBMsg, op1, IRQueue, op_ir_status_change_, 
           removeIR, monitoringEvent, setIRsToReset, resetIR, stepOfFailure, 
           transaction_con, topo_change, irID, removedIR, msg, 
           op_ir_status_change, op_first_install, transaction >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW)) \cup (({"proc"} \X {CONT_NIB_FAILOVER})) \cup (({nib0} \X {CONT_NIB_RC_EVENT})) \cup (({nib0} \X {CONT_NIB_OFC_EVENT})) \cup (({"proc"} \X {RC_FAILOVER})) \cup (({rc0} \X {CONT_RC_NIB_EVENT})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (( {"proc"} \X {NIB_FAILURE})) \cup (({"proc"} \X {OFC_FAILOVER})) \cup (({ofc0} \X {CONT_OFC_NIB_EVENT})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstallOFC = [x \in 1..MaxNumIRs |-> 0]
        /\ FirstInstallNIB = [x \in 1..MaxNumIRs |-> 0]
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ ContProcSet = (({rc0} \X {CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_RC_NIB_EVENT, CONT_TE}))
                         \cup (({ofc0} \X CONTROLLER_THREAD_POOL))
                         \cup (({ofc0} \X {CONT_OFC_NIB_EVENT}))
                         \cup (({ofc0} \X {CONT_EVENT}))
                         \cup (({ofc0} \X {CONT_MONITOR}))
                         \cup (({nib0} \X {CONT_NIB_RC_EVENT}))
                         \cup (({nib0} \X {CONT_NIB_OFC_EVENT}))
        /\ SwProcSet = ((({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW))
                          \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW))
                          \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW))
                          \cup (({SW_RESOLVE_PROC} \X SW)))
        /\ irTypeMapping = [x \in 1.. MaxNumIRs |-> [type |-> INSTALL_FLOW, flow |-> IR2FLOW[x]]]
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
        /\ controllerSubmoduleFailNum = [x \in {ofc0, rc0, nib0} |-> 0]
        /\ controllerSubmoduleFailStat = [x \in ContProcSet |-> NotFailed]
        /\ switchOrdering = (CHOOSE x \in [SW -> 1..Cardinality(SW)]: ~\E y, z \in SW: y # z /\ x[y] = x[z])
        /\ dependencyGraph \in generateConnectedDAG(1..MaxNumIRs)
        /\ ir2sw = IR2SW
        /\ NIBUpdateForRC = FALSE
        /\ controllerStateRC = [x \in ContProcSet |-> [type |-> NO_STATUS]]
        /\ IRStatusRC = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatusRC = [x \in SW |-> SW_RUN]
        /\ IRQueueRC = <<>>
        /\ SetScheduledIRsRC = [y \in SW |-> {}]
        /\ FlagRCNIBEventHandlerFailover = FALSE
        /\ FlagRCSequencerFailover = FALSE
        /\ RC_READY = FALSE
        /\ IRChangeForRC = FALSE
        /\ TopoChangeForRC = FALSE
        /\ TEEventQueue = [x \in {rc0} |-> <<>>]
        /\ DAGEventQueue = [x \in {rc0} |-> <<>>]
        /\ DAGQueue = [x \in {rc0} |-> <<>>]
        /\ DAGID = 0
        /\ MaxDAGID = 15
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ nxtRCIRID = MaxNumIRs + 10
        /\ idWorkerWorkingOnDAG = [x \in 1..MaxDAGID |-> DAG_UNLOCK]
        /\ IRDoneSet = [x \in {rc0} |-> {}]
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
        /\ IRStatusNIB = [x \in 1..MaxNumIRs |-> IR_NONE]
        /\ SwSuspensionStatusNIB = [x \in SW |-> SW_RUN]
        /\ IRQueueNIB = <<>>
        /\ SetScheduledIRs = [y \in SW |-> {}]
        /\ X2NIB_len = 0
        /\ NIBThreadID = <<nib0, CONT_NIB_RC_EVENT>>
        /\ RCThreadID = <<rc0, CONT_WORKER_SEQ>>
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
        /\ debug_N = [self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) |-> -1]
        (* Process RCNIBEventHandler *)
        /\ NIBMsg_ = [self \in ({rc0} \X {CONT_RC_NIB_EVENT}) |-> [value |-> [x |-> <<>>]]]
        /\ isBootStrap_ = [self \in ({rc0} \X {CONT_RC_NIB_EVENT}) |-> TRUE]
        /\ sw_id = [self \in ({rc0} \X {CONT_RC_NIB_EVENT}) |-> 0]
        /\ transaction_ = [self \in ({rc0} \X {CONT_RC_NIB_EVENT}) |-> <<>>]
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
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ transaction_c = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> <<>>]
        /\ stepOfFailure_c = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> 0]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> [dag |-> 0]]
        /\ IRSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ key = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> ""]
        /\ op1_ = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> [table |-> ""]]
        /\ op2 = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> [table |-> ""]]
        /\ debug = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> FALSE]
        (* Process OFCFailoverProc *)
        /\ transaction_O = [self \in ({"proc"} \X {OFC_FAILOVER}) |-> <<>>]
        /\ IRQueueTmp = [self \in ({"proc"} \X {OFC_FAILOVER}) |-> <<>>]
        (* Process OFCNIBEventHandler *)
        /\ NIBMsg_O = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> [value |-> [x |-> <<>>]]]
        /\ isBootStrap = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> TRUE]
        /\ localIRSet = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> {}]
        /\ NIBIRSet = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> {}]
        /\ newIRSet = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> {}]
        /\ newIR = [self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) |-> -1]
        (* Process controllerWorkerThreads *)
        /\ nextIRToSent = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ rowIndex = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ rowRemove = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> -1]
        /\ stepOfFailure_co = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ transaction_co = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> <<>>]
        /\ NIBMsg = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> [value |-> [x |-> <<>>]]]
        /\ op1 = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> [table |-> ""]]
        /\ IRQueue = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> <<>>]
        /\ op_ir_status_change_ = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> [table |-> ""]]
        /\ removeIR = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> FALSE]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> [type |-> 0]]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ stepOfFailure = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        /\ transaction_con = [self \in ({ofc0} \X {CONT_EVENT}) |-> <<>>]
        /\ topo_change = [self \in ({ofc0} \X {CONT_EVENT}) |-> [table |-> ""]]
        (* Process controllerMonitoringServer *)
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
        /\ removedIR = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
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
                                        [] self \in ({nib0} \X {CONT_NIB_RC_EVENT}) -> "NIBDequeueRCTransaction"
                                        [] self \in ({nib0} \X {CONT_NIB_OFC_EVENT}) -> "NIBDequeueOFCTransaction"
                                        [] self \in ({"proc"} \X {RC_FAILOVER}) -> "RCFailoverResetStates"
                                        [] self \in ({rc0} \X {CONT_RC_NIB_EVENT}) -> "RCSendReadTransaction"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "RCWorkerSeqProc"
                                        [] self \in ( {"proc"} \X {NIB_FAILURE}) -> "NIBFailure"
                                        [] self \in ({"proc"} \X {OFC_FAILOVER}) -> "OFCFailoverResetStates"
                                        [] self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) -> "OFCNIBEventHanderProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "OFCThreadGetNextIR"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "OFCMonitorCheckIfMastr"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ isOFCUp(OFCThreadID)
                             /\ swCanReceivePackets(self[2])
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ IF ingressPkt'[self].type = INSTALL_FLOW
                                   THEN /\ installedIRs' = Append(installedIRs, ingressPkt'[self].flow)
                                        /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], ingressPkt'[self].flow)]
                                        /\ switch2Controller' = Append(switch2Controller, [type |-> INSTALLED_SUCCESSFULLY,
                                                                                       from |-> self[2],
                                                                                       flow |-> ingressPkt'[self].flow])
                                   ELSE /\ TCAM' = [TCAM EXCEPT ![self[2]] = removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], ingressPkt'[self].flow))]
                                        /\ switch2Controller' = Append(switch2Controller, [type |-> DELETED_SUCCESSFULLY,
                                                                                           from |-> self[2],
                                                                                           flow |-> ingressPkt'[self].flow])
                                        /\ UNCHANGED installedIRs
                             /\ Assert(\/ switchLock[2] = self[2]
                                       \/ switchLock[2] = NO_LOCK, 
                                       "Failure of assertion at line 966, column 9 of macro called at line 1278, column 9.")
                             /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                             FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, 
                                             swSeqChangedStatus, switchStatus, 
                                             NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             ir2sw, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             SwSuspensionStatusRC, IRQueueRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             IRChangeForRC, TopoChangeForRC, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, DAGID, MaxDAGID, 
                                             DAGState, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, IRDoneSet, 
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
                                             controllerStateNIB, IRStatusNIB, 
                                             SwSuspensionStatusNIB, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             value_, nextTrans_, value_N, 
                                             rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug_N, NIBMsg_, 
                                             isBootStrap_, sw_id, transaction_, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, 
                                             toBeScheduledIRs, nextIR, 
                                             transaction_c, stepOfFailure_c, 
                                             currDAG, IRSet, key, op1_, op2, 
                                             debug, transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, newIRSet, newIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_co, transaction_co, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, 
                                             transaction_con, topo_change, 
                                             irID, removedIR, msg, 
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
                                   "Failure of assertion at line 1303, column 9.")
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         swSeqChangedStatus, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         ir2sw, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         SwSuspensionStatusRC, IRQueueRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         IRChangeForRC, TopoChangeForRC, 
                                         TEEventQueue, DAGEventQueue, DAGQueue, 
                                         DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                         idWorkerWorkingOnDAG, IRDoneSet, 
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
                                         IRStatusNIB, SwSuspensionStatusNIB, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug_N, 
                                         NIBMsg_, isBootStrap_, sw_id, 
                                         transaction_, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, 
                                         toBeScheduledIRs, nextIR, 
                                         transaction_c, stepOfFailure_c, 
                                         currDAG, IRSet, key, op1_, op2, debug, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         newIRSet, newIR, nextIRToSent, 
                                         rowIndex, rowRemove, stepOfFailure_co, 
                                         transaction_co, NIBMsg, op1, IRQueue, 
                                         op_ir_status_change_, removeIR, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, 
                                         transaction_con, topo_change, irID, 
                                         removedIR, msg, op_ir_status_change, 
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
                                                      irTypeMapping, 
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
                                                      dependencyGraph, ir2sw, 
                                                      NIBUpdateForRC, 
                                                      controllerStateRC, 
                                                      IRStatusRC, 
                                                      SwSuspensionStatusRC, 
                                                      IRQueueRC, 
                                                      SetScheduledIRsRC, 
                                                      FlagRCNIBEventHandlerFailover, 
                                                      FlagRCSequencerFailover, 
                                                      RC_READY, IRChangeForRC, 
                                                      TopoChangeForRC, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      DAGID, MaxDAGID, 
                                                      DAGState, nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      IRDoneSet, 
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
                                                      IRStatusNIB, 
                                                      SwSuspensionStatusNIB, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      X2NIB_len, NIBThreadID, 
                                                      RCThreadID, ingressPkt, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
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
                                                      debug_N, NIBMsg_, 
                                                      isBootStrap_, sw_id, 
                                                      transaction_, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, 
                                                      nxtDAG, setRemovableIRs, 
                                                      currIR, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      toBeScheduledIRs, nextIR, 
                                                      transaction_c, 
                                                      stepOfFailure_c, currDAG, 
                                                      IRSet, key, op1_, op2, 
                                                      debug, transaction_O, 
                                                      IRQueueTmp, NIBMsg_O, 
                                                      isBootStrap, localIRSet, 
                                                      NIBIRSet, newIRSet, 
                                                      newIR, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_co, 
                                                      transaction_co, NIBMsg, 
                                                      op1, IRQueue, 
                                                      op_ir_status_change_, 
                                                      removeIR, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, 
                                                      transaction_con, 
                                                      topo_change, irID, 
                                                      removedIR, msg, 
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
                                       "Failure of assertion at line 1331, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                             FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             ir2sw, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             SwSuspensionStatusRC, IRQueueRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             IRChangeForRC, TopoChangeForRC, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, DAGID, MaxDAGID, 
                                             DAGState, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, IRDoneSet, 
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
                                             controllerStateNIB, IRStatusNIB, 
                                             SwSuspensionStatusNIB, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             value_, nextTrans_, value_N, 
                                             rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug_N, NIBMsg_, 
                                             isBootStrap_, sw_id, transaction_, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, 
                                             toBeScheduledIRs, nextIR, 
                                             transaction_c, stepOfFailure_c, 
                                             currDAG, IRSet, key, op1_, op2, 
                                             debug, transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, newIRSet, newIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_co, transaction_co, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, 
                                             transaction_con, topo_change, 
                                             irID, removedIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 966, column 9 of macro called at line 1340, column 17.")
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
                                                 irTypeMapping, 
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
                                                 switchOrdering, 
                                                 dependencyGraph, ir2sw, 
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 SwSuspensionStatusRC, 
                                                 IRQueueRC, SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, IRChangeForRC, 
                                                 TopoChangeForRC, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 IRDoneSet, 
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
                                                 IRStatusNIB, 
                                                 SwSuspensionStatusNIB, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
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
                                                 debug_N, NIBMsg_, 
                                                 isBootStrap_, sw_id, 
                                                 transaction_, topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, toBeScheduledIRs, 
                                                 nextIR, transaction_c, 
                                                 stepOfFailure_c, currDAG, 
                                                 IRSet, key, op1_, op2, debug, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 newIRSet, newIR, nextIRToSent, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_co, 
                                                 transaction_co, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, 
                                                 transaction_con, topo_change, 
                                                 irID, removedIR, msg, 
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
                                   "Failure of assertion at line 1368, column 9.")
                         /\ Assert(ofaInMsg'[self].IR  \in 1..MaxNumIRs, 
                                   "Failure of assertion at line 1369, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, Ofa2NicAsicBuff, 
                                         Installer2OfaBuff, Ofa2InstallerBuff, 
                                         TCAM, controlMsgCounter, 
                                         RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         ir2sw, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         SwSuspensionStatusRC, IRQueueRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         IRChangeForRC, TopoChangeForRC, 
                                         TEEventQueue, DAGEventQueue, DAGQueue, 
                                         DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                         idWorkerWorkingOnDAG, IRDoneSet, 
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
                                         IRStatusNIB, SwSuspensionStatusNIB, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug_N, 
                                         NIBMsg_, isBootStrap_, sw_id, 
                                         transaction_, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, 
                                         toBeScheduledIRs, nextIR, 
                                         transaction_c, stepOfFailure_c, 
                                         currDAG, IRSet, key, op1_, op2, debug, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         newIRSet, newIR, nextIRToSent, 
                                         rowIndex, rowRemove, stepOfFailure_co, 
                                         transaction_co, NIBMsg, op1, IRQueue, 
                                         op_ir_status_change_, removeIR, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, 
                                         transaction_con, topo_change, irID, 
                                         removedIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                           /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           /\ switchLock' = <<INSTALLER, self[2]>>
                                           /\ IF ofaInMsg[self].type = INSTALL_FLOW
                                                 THEN /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], ofaInMsg[self].IR)]
                                                 ELSE /\ Assert(FALSE, 
                                                                "Failure of assertion at line 1382, column 21.")
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
                                                irTypeMapping, 
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
                                                switchOrdering, 
                                                dependencyGraph, ir2sw, 
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                SwSuspensionStatusRC, 
                                                IRQueueRC, SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, IRChangeForRC, 
                                                TopoChangeForRC, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
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
                                                controllerStateNIB, 
                                                IRStatusNIB, 
                                                SwSuspensionStatusNIB, 
                                                IRQueueNIB, SetScheduledIRs, 
                                                X2NIB_len, NIBThreadID, 
                                                RCThreadID, ingressPkt, 
                                                ingressIR, egressMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug_N, NIBMsg_, 
                                                isBootStrap_, sw_id, 
                                                transaction_, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, nxtDAG, setRemovableIRs, 
                                                currIR, currIRInDAG, 
                                                nxtDAGVertices, setIRsInDAG, 
                                                prev_dag, toBeScheduledIRs, 
                                                nextIR, transaction_c, 
                                                stepOfFailure_c, currDAG, 
                                                IRSet, key, op1_, op2, debug, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, newIRSet, 
                                                newIR, nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_co, 
                                                transaction_co, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, transaction_con, 
                                                topo_change, irID, removedIR, 
                                                msg, op_ir_status_change, 
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
                                    "Failure of assertion at line 1403, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                          FirstInstallNIB, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, irTypeMapping, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          ir2sw, NIBUpdateForRC, 
                                          controllerStateRC, IRStatusRC, 
                                          SwSuspensionStatusRC, IRQueueRC, 
                                          SetScheduledIRsRC, 
                                          FlagRCNIBEventHandlerFailover, 
                                          FlagRCSequencerFailover, RC_READY, 
                                          IRChangeForRC, TopoChangeForRC, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, DAGID, MaxDAGID, DAGState, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          IRDoneSet, idThreadWorkingOnIR, 
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
                                          IRStatusNIB, SwSuspensionStatusNIB, 
                                          IRQueueNIB, SetScheduledIRs, 
                                          X2NIB_len, NIBThreadID, RCThreadID, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, installerInIR, statusMsg, 
                                          notFailedSet, failedElem, obj, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, value_, nextTrans_, 
                                          value_N, rowRemove_, IR2Remove_, 
                                          send_NIB_back_, stepOfFailure_, 
                                          IRIndex_, debug_, nextTrans, value, 
                                          rowRemove_N, IR2Remove, 
                                          send_NIB_back, stepOfFailure_N, 
                                          IRIndex, debug_N, NIBMsg_, 
                                          isBootStrap_, sw_id, transaction_, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, toBeScheduledIRs, nextIR, 
                                          transaction_c, stepOfFailure_c, 
                                          currDAG, IRSet, key, op1_, op2, 
                                          debug, transaction_O, IRQueueTmp, 
                                          NIBMsg_O, isBootStrap, localIRSet, 
                                          NIBIRSet, newIRSet, newIR, 
                                          nextIRToSent, rowIndex, rowRemove, 
                                          stepOfFailure_co, transaction_co, 
                                          NIBMsg, op1, IRQueue, 
                                          op_ir_status_change_, removeIR, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, 
                                          transaction_con, topo_change, irID, 
                                          removedIR, msg, op_ir_status_change, 
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
                                                      irTypeMapping, 
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
                                                      dependencyGraph, ir2sw, 
                                                      NIBUpdateForRC, 
                                                      controllerStateRC, 
                                                      IRStatusRC, 
                                                      SwSuspensionStatusRC, 
                                                      IRQueueRC, 
                                                      SetScheduledIRsRC, 
                                                      FlagRCNIBEventHandlerFailover, 
                                                      FlagRCSequencerFailover, 
                                                      RC_READY, IRChangeForRC, 
                                                      TopoChangeForRC, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      DAGID, MaxDAGID, 
                                                      DAGState, nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      IRDoneSet, 
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
                                                      IRStatusNIB, 
                                                      SwSuspensionStatusNIB, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      X2NIB_len, NIBThreadID, 
                                                      RCThreadID, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, installerInIR, 
                                                      statusMsg, notFailedSet, 
                                                      failedElem, obj, 
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
                                                      debug_N, NIBMsg_, 
                                                      isBootStrap_, sw_id, 
                                                      transaction_, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, 
                                                      nxtDAG, setRemovableIRs, 
                                                      currIR, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      toBeScheduledIRs, nextIR, 
                                                      transaction_c, 
                                                      stepOfFailure_c, currDAG, 
                                                      IRSet, key, op1_, op2, 
                                                      debug, transaction_O, 
                                                      IRQueueTmp, NIBMsg_O, 
                                                      isBootStrap, localIRSet, 
                                                      NIBIRSet, newIRSet, 
                                                      newIR, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_co, 
                                                      transaction_co, NIBMsg, 
                                                      op1, IRQueue, 
                                                      op_ir_status_change_, 
                                                      removeIR, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, 
                                                      transaction_con, 
                                                      topo_change, irID, 
                                                      removedIR, msg, 
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
                                       "Failure of assertion at line 1435, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                             FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             controllerSubmoduleFailNum, 
                                             controllerSubmoduleFailStat, 
                                             switchOrdering, dependencyGraph, 
                                             ir2sw, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             SwSuspensionStatusRC, IRQueueRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             IRChangeForRC, TopoChangeForRC, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, DAGID, MaxDAGID, 
                                             DAGState, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, IRDoneSet, 
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
                                             controllerStateNIB, IRStatusNIB, 
                                             SwSuspensionStatusNIB, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem, 
                                             value_, nextTrans_, value_N, 
                                             rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug_N, NIBMsg_, 
                                             isBootStrap_, sw_id, transaction_, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, 
                                             toBeScheduledIRs, nextIR, 
                                             transaction_c, stepOfFailure_c, 
                                             currDAG, IRSet, key, op1_, op2, 
                                             debug, transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, newIRSet, newIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_co, transaction_co, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, 
                                             transaction_con, topo_change, 
                                             irID, removedIR, msg, 
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
                                                    irTypeMapping, 
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
                                                    dependencyGraph, ir2sw, 
                                                    NIBUpdateForRC, 
                                                    controllerStateRC, 
                                                    IRStatusRC, 
                                                    SwSuspensionStatusRC, 
                                                    IRQueueRC, 
                                                    SetScheduledIRsRC, 
                                                    FlagRCNIBEventHandlerFailover, 
                                                    FlagRCSequencerFailover, 
                                                    RC_READY, IRChangeForRC, 
                                                    TopoChangeForRC, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    IRDoneSet, 
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
                                                    IRStatusNIB, 
                                                    SwSuspensionStatusNIB, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, X2NIB_len, 
                                                    NIBThreadID, RCThreadID, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    statusMsg, notFailedSet, 
                                                    failedElem, obj, failedSet, 
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
                                                    debug_N, NIBMsg_, 
                                                    isBootStrap_, sw_id, 
                                                    transaction_, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    toBeScheduledIRs, nextIR, 
                                                    transaction_c, 
                                                    stepOfFailure_c, currDAG, 
                                                    IRSet, key, op1_, op2, 
                                                    debug, transaction_O, 
                                                    IRQueueTmp, NIBMsg_O, 
                                                    isBootStrap, localIRSet, 
                                                    NIBIRSet, newIRSet, newIR, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, 
                                                    stepOfFailure_co, 
                                                    transaction_co, NIBMsg, 
                                                    op1, IRQueue, 
                                                    op_ir_status_change_, 
                                                    removeIR, monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, 
                                                    transaction_con, 
                                                    topo_change, irID, 
                                                    removedIR, msg, 
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
                                                         irTypeMapping, 
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
                                                         dependencyGraph, 
                                                         ir2sw, NIBUpdateForRC, 
                                                         controllerStateRC, 
                                                         IRStatusRC, 
                                                         SwSuspensionStatusRC, 
                                                         IRQueueRC, 
                                                         SetScheduledIRsRC, 
                                                         FlagRCNIBEventHandlerFailover, 
                                                         FlagRCSequencerFailover, 
                                                         RC_READY, 
                                                         IRChangeForRC, 
                                                         TopoChangeForRC, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, DAGID, 
                                                         MaxDAGID, DAGState, 
                                                         nxtRCIRID, 
                                                         idWorkerWorkingOnDAG, 
                                                         IRDoneSet, 
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
                                                         IRStatusNIB, 
                                                         SwSuspensionStatusNIB, 
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
                                                         failedElem, obj, 
                                                         failedSet, 
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
                                                         IRIndex, debug_N, 
                                                         NIBMsg_, isBootStrap_, 
                                                         sw_id, transaction_, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         toBeScheduledIRs, 
                                                         nextIR, transaction_c, 
                                                         stepOfFailure_c, 
                                                         currDAG, IRSet, key, 
                                                         op1_, op2, debug, 
                                                         transaction_O, 
                                                         IRQueueTmp, NIBMsg_O, 
                                                         isBootStrap, 
                                                         localIRSet, NIBIRSet, 
                                                         newIRSet, newIR, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_co, 
                                                         transaction_co, 
                                                         NIBMsg, op1, IRQueue, 
                                                         op_ir_status_change_, 
                                                         removeIR, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, 
                                                         transaction_con, 
                                                         topo_change, irID, 
                                                         removedIR, msg, 
                                                         op_ir_status_change, 
                                                         op_first_install, 
                                                         transaction >>

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
                                 "Failure of assertion at line 670, column 9 of macro called at line 1485, column 9.")
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
                                                       "Failure of assertion at line 793, column 9 of macro called at line 1505, column 17.")
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
                                                                  "Failure of assertion at line 845, column 9 of macro called at line 1507, column 17.")
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
                                                                             "Failure of assertion at line 889, column 9 of macro called at line 1509, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                                   /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                         THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                                        "Failure of assertion at line 892, column 13 of macro called at line 1509, column 17.")
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
                                                                                        "Failure of assertion at line 739, column 9 of macro called at line 1511, column 17.")
                                                                              /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                              /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                              /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                                                           swID |-> self[2],
                                                                                                                           num |-> controlMsgCounter'[self[2]]]]
                                                                              /\ swSeqChangedStatus' = Append(swSeqChangedStatus, statusMsg'[self])
                                                                         ELSE /\ Assert(FALSE, 
                                                                                        "Failure of assertion at line 1512, column 18.")
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
                                       FirstInstallOFC, FirstInstallNIB, 
                                       ContProcSet, SwProcSet, irTypeMapping, 
                                       switch2Controller, installedIRs, 
                                       controllerSubmoduleFailNum, 
                                       controllerSubmoduleFailStat, 
                                       switchOrdering, dependencyGraph, ir2sw, 
                                       NIBUpdateForRC, controllerStateRC, 
                                       IRStatusRC, SwSuspensionStatusRC, 
                                       IRQueueRC, SetScheduledIRsRC, 
                                       FlagRCNIBEventHandlerFailover, 
                                       FlagRCSequencerFailover, RC_READY, 
                                       IRChangeForRC, TopoChangeForRC, 
                                       TEEventQueue, DAGEventQueue, DAGQueue, 
                                       DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                       idWorkerWorkingOnDAG, IRDoneSet, 
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
                                       IRStatusNIB, SwSuspensionStatusNIB, 
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
                                       stepOfFailure_N, IRIndex, debug_N, 
                                       NIBMsg_, isBootStrap_, sw_id, 
                                       transaction_, topoChangeEvent, 
                                       currSetDownSw, prev_dag_id, init, 
                                       nxtDAG, setRemovableIRs, currIR, 
                                       currIRInDAG, nxtDAGVertices, 
                                       setIRsInDAG, prev_dag, toBeScheduledIRs, 
                                       nextIR, transaction_c, stepOfFailure_c, 
                                       currDAG, IRSet, key, op1_, op2, debug, 
                                       transaction_O, IRQueueTmp, NIBMsg_O, 
                                       isBootStrap, localIRSet, NIBIRSet, 
                                       newIRSet, newIR, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_co, 
                                       transaction_co, NIBMsg, op1, IRQueue, 
                                       op_ir_status_change_, removeIR, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, transaction_con, 
                                       topo_change, irID, removedIR, msg, 
                                       op_ir_status_change, op_first_install, 
                                       transaction >>

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ RecoveryStatus[self[2]].transient = 1
                              /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF RecoveryStatus[self[2]].partial = 0
                                    THEN /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                   "Failure of assertion at line 706, column 9 of macro called at line 1534, column 13.")
                                         /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                   "Failure of assertion at line 707, column 9 of macro called at line 1534, column 13.")
                                         /\ Assert(switchStatus[self[2]].ofa = Failed, 
                                                   "Failure of assertion at line 708, column 9 of macro called at line 1534, column 13.")
                                         /\ Assert(switchStatus[self[2]].installer = Failed, 
                                                   "Failure of assertion at line 709, column 9 of macro called at line 1534, column 13.")
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
                                                              "Failure of assertion at line 820, column 9 of macro called at line 1542, column 43.")
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
                                                                         "Failure of assertion at line 765, column 9 of macro called at line 1543, column 50.")
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
                                                                                    "Failure of assertion at line 867, column 9 of macro called at line 1544, column 46.")
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
                                                                                               "Failure of assertion at line 911, column 9 of macro called at line 1545, column 52.")
                                                                                     /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                                     /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                           THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                                          "Failure of assertion at line 914, column 13 of macro called at line 1545, column 52.")
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
                                                                                               "Failure of assertion at line 1546, column 18.")
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
                                              FirstInstallOFC, FirstInstallNIB, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, switch2Controller, 
                                              installedIRs, 
                                              controllerSubmoduleFailNum, 
                                              controllerSubmoduleFailStat, 
                                              switchOrdering, dependencyGraph, 
                                              ir2sw, NIBUpdateForRC, 
                                              controllerStateRC, IRStatusRC, 
                                              SwSuspensionStatusRC, IRQueueRC, 
                                              SetScheduledIRsRC, 
                                              FlagRCNIBEventHandlerFailover, 
                                              FlagRCSequencerFailover, 
                                              RC_READY, IRChangeForRC, 
                                              TopoChangeForRC, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, IRDoneSet, 
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
                                              NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                              FlagNIBFailover, 
                                              FlagNIBRCEventhandlerFailover, 
                                              FlagNIBOFCEventhandlerFailover, 
                                              NIB_READY_FOR_RC, 
                                              NIB_READY_FOR_OFC, masterState, 
                                              controllerStateNIB, IRStatusNIB, 
                                              SwSuspensionStatusNIB, 
                                              IRQueueNIB, SetScheduledIRs, 
                                              X2NIB_len, NIBThreadID, 
                                              RCThreadID, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              value_, nextTrans_, value_N, 
                                              rowRemove_, IR2Remove_, 
                                              send_NIB_back_, stepOfFailure_, 
                                              IRIndex_, debug_, nextTrans, 
                                              value, rowRemove_N, IR2Remove, 
                                              send_NIB_back, stepOfFailure_N, 
                                              IRIndex, debug_N, NIBMsg_, 
                                              isBootStrap_, sw_id, 
                                              transaction_, topoChangeEvent, 
                                              currSetDownSw, prev_dag_id, init, 
                                              nxtDAG, setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, 
                                              toBeScheduledIRs, nextIR, 
                                              transaction_c, stepOfFailure_c, 
                                              currDAG, IRSet, key, op1_, op2, 
                                              debug, transaction_O, IRQueueTmp, 
                                              NIBMsg_O, isBootStrap, 
                                              localIRSet, NIBIRSet, newIRSet, 
                                              newIR, nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure_co, 
                                              transaction_co, NIBMsg, op1, 
                                              IRQueue, op_ir_status_change_, 
                                              removeIR, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, transaction_con, 
                                              topo_change, irID, removedIR, 
                                              msg, op_ir_status_change, 
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
                             "Failure of assertion at line 966, column 9 of macro called at line 1583, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << controllerLock, FirstInstallOFC, 
                                   FirstInstallNIB, sw_fail_ordering_var, 
                                   ContProcSet, SwProcSet, irTypeMapping, 
                                   swSeqChangedStatus, controller2Switch, 
                                   switch2Controller, switchStatus, 
                                   installedIRs, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   RecoveryStatus, controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   dependencyGraph, ir2sw, NIBUpdateForRC, 
                                   controllerStateRC, IRStatusRC, 
                                   SwSuspensionStatusRC, IRQueueRC, 
                                   SetScheduledIRsRC, 
                                   FlagRCNIBEventHandlerFailover, 
                                   FlagRCSequencerFailover, RC_READY, 
                                   IRChangeForRC, TopoChangeForRC, 
                                   TEEventQueue, DAGEventQueue, DAGQueue, 
                                   DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                   idWorkerWorkingOnDAG, IRDoneSet, 
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
                                   masterState, controllerStateNIB, 
                                   IRStatusNIB, SwSuspensionStatusNIB, 
                                   IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                   NIBThreadID, RCThreadID, ingressPkt, 
                                   ingressIR, egressMsg, ofaInMsg, 
                                   ofaOutConfirmation, installerInIR, 
                                   statusMsg, notFailedSet, failedElem, obj, 
                                   failedSet, statusResolveMsg, recoveredElem, 
                                   value_, nextTrans_, value_N, rowRemove_, 
                                   IR2Remove_, send_NIB_back_, stepOfFailure_, 
                                   IRIndex_, debug_, nextTrans, value, 
                                   rowRemove_N, IR2Remove, send_NIB_back, 
                                   stepOfFailure_N, IRIndex, debug_N, NIBMsg_, 
                                   isBootStrap_, sw_id, transaction_, 
                                   topoChangeEvent, currSetDownSw, prev_dag_id, 
                                   init, nxtDAG, setRemovableIRs, currIR, 
                                   currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                   prev_dag, toBeScheduledIRs, nextIR, 
                                   transaction_c, stepOfFailure_c, currDAG, 
                                   IRSet, key, op1_, op2, debug, transaction_O, 
                                   IRQueueTmp, NIBMsg_O, isBootStrap, 
                                   localIRSet, NIBIRSet, newIRSet, newIR, 
                                   nextIRToSent, rowIndex, rowRemove, 
                                   stepOfFailure_co, transaction_co, NIBMsg, 
                                   op1, IRQueue, op_ir_status_change_, 
                                   removeIR, monitoringEvent, setIRsToReset, 
                                   resetIR, stepOfFailure, transaction_con, 
                                   topo_change, irID, removedIR, msg, 
                                   op_ir_status_change, op_first_install, 
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
                                                irTypeMapping, 
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
                                                switchOrdering, 
                                                dependencyGraph, ir2sw, 
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                SwSuspensionStatusRC, 
                                                IRQueueRC, SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, IRChangeForRC, 
                                                TopoChangeForRC, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
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
                                                controllerStateNIB, 
                                                IRStatusNIB, 
                                                SwSuspensionStatusNIB, 
                                                IRQueueNIB, SetScheduledIRs, 
                                                X2NIB_len, NIBThreadID, 
                                                RCThreadID, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug_N, NIBMsg_, 
                                                isBootStrap_, sw_id, 
                                                transaction_, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, nxtDAG, setRemovableIRs, 
                                                currIR, currIRInDAG, 
                                                nxtDAGVertices, setIRsInDAG, 
                                                prev_dag, toBeScheduledIRs, 
                                                nextIR, transaction_c, 
                                                stepOfFailure_c, currDAG, 
                                                IRSet, key, op1_, op2, debug, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, newIRSet, 
                                                newIR, nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_co, 
                                                transaction_co, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, transaction_con, 
                                                topo_change, irID, removedIR, 
                                                msg, op_ir_status_change, 
                                                op_first_install, transaction >>

NIBFailoverReadOFC(self) == /\ pc[self] = "NIBFailoverReadOFC"
                            /\ OFC_READY \/ isOFCUp(OFCThreadID)
                            /\ IRStatusNIB' = IRStatusOFC
                            /\ SwSuspensionStatusNIB' = SwSuspensionStatusOFC
                            /\ NIB_READY_FOR_RC' = TRUE
                            /\ pc' = [pc EXCEPT ![self] = "NIBFailoverReadRC"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, IRQueueRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            IRChangeForRC, TopoChangeForRC, 
                                            TEEventQueue, DAGEventQueue, 
                                            DAGQueue, DAGID, MaxDAGID, 
                                            DAGState, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, IRDoneSet, 
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
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            toBeScheduledIRs, nextIR, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, IRSet, key, op1_, op2, 
                                            debug, transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_co, transaction_co, 
                                            NIBMsg, op1, IRQueue, 
                                            op_ir_status_change_, removeIR, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, 
                                            transaction_con, topo_change, irID, 
                                            removedIR, msg, 
                                            op_ir_status_change, 
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
                                           SwProcSet, irTypeMapping, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, RecoveryStatus, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           ir2sw, NIBUpdateForRC, 
                                           controllerStateRC, IRStatusRC, 
                                           SwSuspensionStatusRC, IRQueueRC, 
                                           SetScheduledIRsRC, 
                                           FlagRCNIBEventHandlerFailover, 
                                           FlagRCSequencerFailover, RC_READY, 
                                           IRChangeForRC, TopoChangeForRC, 
                                           TEEventQueue, DAGEventQueue, 
                                           DAGQueue, DAGID, MaxDAGID, DAGState, 
                                           nxtRCIRID, idWorkerWorkingOnDAG, 
                                           IRDoneSet, idThreadWorkingOnIR, 
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
                                           controllerStateNIB, IRStatusNIB, 
                                           SwSuspensionStatusNIB, X2NIB_len, 
                                           NIBThreadID, RCThreadID, ingressPkt, 
                                           ingressIR, egressMsg, ofaInMsg, 
                                           ofaOutConfirmation, installerInIR, 
                                           statusMsg, notFailedSet, failedElem, 
                                           obj, failedSet, statusResolveMsg, 
                                           recoveredElem, value_, nextTrans_, 
                                           value_N, rowRemove_, IR2Remove_, 
                                           send_NIB_back_, stepOfFailure_, 
                                           IRIndex_, debug_, nextTrans, value, 
                                           rowRemove_N, IR2Remove, 
                                           send_NIB_back, stepOfFailure_N, 
                                           IRIndex, debug_N, NIBMsg_, 
                                           isBootStrap_, sw_id, transaction_, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, 
                                           toBeScheduledIRs, nextIR, 
                                           transaction_c, stepOfFailure_c, 
                                           currDAG, IRSet, key, op1_, op2, 
                                           debug, transaction_O, IRQueueTmp, 
                                           NIBMsg_O, isBootStrap, localIRSet, 
                                           NIBIRSet, newIRSet, newIR, 
                                           nextIRToSent, rowIndex, rowRemove, 
                                           stepOfFailure_co, transaction_co, 
                                           NIBMsg, op1, IRQueue, 
                                           op_ir_status_change_, removeIR, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure, 
                                           transaction_con, topo_change, irID, 
                                           removedIR, msg, op_ir_status_change, 
                                           op_first_install, transaction >>

ChangeNIBStatusToNormal(self) == /\ pc[self] = "ChangeNIBStatusToNormal"
                                 /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed,
                                                                                                       ![<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed]
                                 /\ value_' = [value_ EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                              IRQueueNIB |->IRQueueNIB,
                                                                              SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                              SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                 /\ NIB2RC' = Append(NIB2RC, [value |-> value_'[self]])
                                 /\ NIB2OFC' = Append(NIB2OFC, [value |-> value_'[self]])
                                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstallOFC, 
                                                 FirstInstallNIB, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, 
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
                                                 switchOrdering, 
                                                 dependencyGraph, ir2sw, 
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 SwSuspensionStatusRC, 
                                                 IRQueueRC, SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, IRChangeForRC, 
                                                 TopoChangeForRC, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 IRDoneSet, 
                                                 idThreadWorkingOnIR, 
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
                                                 controllerStateNIB, 
                                                 IRStatusNIB, 
                                                 SwSuspensionStatusNIB, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, nextTrans_, 
                                                 value_N, rowRemove_, 
                                                 IR2Remove_, send_NIB_back_, 
                                                 stepOfFailure_, IRIndex_, 
                                                 debug_, nextTrans, value, 
                                                 rowRemove_N, IR2Remove, 
                                                 send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug_N, NIBMsg_, 
                                                 isBootStrap_, sw_id, 
                                                 transaction_, topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, toBeScheduledIRs, 
                                                 nextIR, transaction_c, 
                                                 stepOfFailure_c, currDAG, 
                                                 IRSet, key, op1_, op2, debug, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 newIRSet, newIR, nextIRToSent, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_co, 
                                                 transaction_co, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, 
                                                 transaction_con, topo_change, 
                                                 irID, removedIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBFailoverProc(self) == NIBFailoverResetStates(self)
                            \/ NIBFailoverReadOFC(self)
                            \/ NIBFailoverReadRC(self)
                            \/ ChangeNIBStatusToNormal(self)

NIBDequeueRCTransaction(self) == /\ pc[self] = "NIBDequeueRCTransaction"
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                                 irTypeMapping, 
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
                                                 dependencyGraph, ir2sw, 
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 SwSuspensionStatusRC, 
                                                 IRQueueRC, SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, IRChangeForRC, 
                                                 TopoChangeForRC, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 IRDoneSet, 
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
                                                 OFC2NIB, FlagNIBFailover, 
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, 
                                                 controllerStateNIB, 
                                                 IRStatusNIB, 
                                                 SwSuspensionStatusNIB, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, value_, 
                                                 value_N, rowRemove_, 
                                                 IR2Remove_, stepOfFailure_, 
                                                 IRIndex_, debug_, nextTrans, 
                                                 value, rowRemove_N, IR2Remove, 
                                                 send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug_N, NIBMsg_, 
                                                 isBootStrap_, sw_id, 
                                                 transaction_, topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, toBeScheduledIRs, 
                                                 nextIR, transaction_c, 
                                                 stepOfFailure_c, currDAG, 
                                                 IRSet, key, op1_, op2, debug, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 newIRSet, newIR, nextIRToSent, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_co, 
                                                 transaction_co, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, 
                                                 transaction_con, topo_change, 
                                                 irID, removedIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBProcessRCTransaction(self) == /\ pc[self] = "NIBProcessRCTransaction"
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ IF moduleIsUp(self)
                                       THEN /\ IF (nextTrans_[self].name = "PrepareIR")
                                                  THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                                 "Failure of assertion at line 1129, column 9 of macro called at line 1735, column 13.")
                                                       /\ Assert(Len(nextTrans_[self].ops[1].key) = 2, 
                                                                 "Failure of assertion at line 1130, column 9 of macro called at line 1735, column 13.")
                                                       /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                       /\ Assert(nextTrans_[self].ops[2].table = NIBT_SET_SCHEDULED_IRS, 
                                                                 "Failure of assertion at line 1132, column 9 of macro called at line 1735, column 13.")
                                                       /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans_[self].ops[2].key] = nextTrans_[self].ops[2].value]
                                                       /\ UNCHANGED << FirstInstallNIB, 
                                                                       IRStatusNIB, 
                                                                       SwSuspensionStatusNIB, 
                                                                       IRQueueNIB, 
                                                                       value_N, 
                                                                       rowRemove_, 
                                                                       IR2Remove_, 
                                                                       send_NIB_back_, 
                                                                       IRIndex_ >>
                                                  ELSE /\ IF (nextTrans_[self].name = "ScheduleIR")
                                                             THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                            "Failure of assertion at line 1138, column 9 of macro called at line 1735, column 13.")
                                                                  /\ IF ~\E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans_[self].ops[1].value.IR
                                                                        THEN /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans_[self].ops[1].value)
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED IRQueueNIB
                                                                  /\ Assert(nextTrans_[self].ops[2].table = NIBT_CONTROLLER_STATE, 
                                                                            "Failure of assertion at line 1142, column 9 of macro called at line 1735, column 13.")
                                                                  /\ Assert(Len(nextTrans_[self].ops[2].key) = 2, 
                                                                            "Failure of assertion at line 1143, column 9 of macro called at line 1735, column 13.")
                                                                  /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans_[self].ops[2].key] = nextTrans_[self].ops[2].value]
                                                                  /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                 IRQueueNIB |->IRQueueNIB',
                                                                                                                 SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                 SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                  /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2OFC"]
                                                                  /\ UNCHANGED << FirstInstallNIB, 
                                                                                  IRStatusNIB, 
                                                                                  SwSuspensionStatusNIB, 
                                                                                  SetScheduledIRs, 
                                                                                  rowRemove_, 
                                                                                  IR2Remove_, 
                                                                                  IRIndex_ >>
                                                             ELSE /\ IF (nextTrans_[self].name = "RCScheduleIRInOneStep")
                                                                        THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                       "Failure of assertion at line 1149, column 9 of macro called at line 1735, column 13.")
                                                                             /\ IF ~\E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans_[self].ops[1].value.IR
                                                                                   THEN /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans_[self].ops[1].value)
                                                                                   ELSE /\ TRUE
                                                                                        /\ UNCHANGED IRQueueNIB
                                                                             /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                            IRQueueNIB |->IRQueueNIB',
                                                                                                                            SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                            SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                             /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2OFC"]
                                                                             /\ UNCHANGED << FirstInstallNIB, 
                                                                                             controllerStateNIB, 
                                                                                             IRStatusNIB, 
                                                                                             SwSuspensionStatusNIB, 
                                                                                             SetScheduledIRs, 
                                                                                             rowRemove_, 
                                                                                             IR2Remove_, 
                                                                                             IRIndex_ >>
                                                                        ELSE /\ IF (nextTrans_[self].name = "SeqReadNIBStates")
                                                                                   THEN /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                                       IRQueueNIB |->IRQueueNIB,
                                                                                                                                       SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                       SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                        /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                        /\ UNCHANGED << FirstInstallNIB, 
                                                                                                        controllerStateNIB, 
                                                                                                        IRStatusNIB, 
                                                                                                        SwSuspensionStatusNIB, 
                                                                                                        IRQueueNIB, 
                                                                                                        SetScheduledIRs, 
                                                                                                        rowRemove_, 
                                                                                                        IR2Remove_, 
                                                                                                        IRIndex_ >>
                                                                                   ELSE /\ IF (nextTrans_[self].name = "OFCOverrideIRStatus")
                                                                                              THEN /\ IRStatusNIB' = nextTrans_[self].ops[1]
                                                                                                   /\ FirstInstallNIB' = nextTrans_[self].ops[2]
                                                                                                   /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                                  IRQueueNIB |->IRQueueNIB,
                                                                                                                                                  SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                  SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                   /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                   /\ UNCHANGED << controllerStateNIB, 
                                                                                                                   SwSuspensionStatusNIB, 
                                                                                                                   IRQueueNIB, 
                                                                                                                   SetScheduledIRs, 
                                                                                                                   rowRemove_, 
                                                                                                                   IR2Remove_, 
                                                                                                                   IRIndex_ >>
                                                                                              ELSE /\ IF (nextTrans_[self].name = "OFCReadNIBStates")
                                                                                                         THEN /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                                                             IRQueueNIB |->IRQueueNIB,
                                                                                                                                                             SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                             SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                              /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2OFC"]
                                                                                                              /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                              controllerStateNIB, 
                                                                                                                              IRStatusNIB, 
                                                                                                                              SwSuspensionStatusNIB, 
                                                                                                                              IRQueueNIB, 
                                                                                                                              SetScheduledIRs, 
                                                                                                                              rowRemove_, 
                                                                                                                              IR2Remove_, 
                                                                                                                              IRIndex_ >>
                                                                                                         ELSE /\ IF (nextTrans_[self].name = "UpdateControllerState")
                                                                                                                    THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                                                                                                   "Failure of assertion at line 1180, column 17 of macro called at line 1735, column 13.")
                                                                                                                         /\ Assert(Len(nextTrans_[self].ops[1].key) = 2, 
                                                                                                                                   "Failure of assertion at line 1181, column 17 of macro called at line 1735, column 13.")
                                                                                                                         /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                         /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                         IRStatusNIB, 
                                                                                                                                         SwSuspensionStatusNIB, 
                                                                                                                                         IRQueueNIB, 
                                                                                                                                         SetScheduledIRs, 
                                                                                                                                         value_N, 
                                                                                                                                         rowRemove_, 
                                                                                                                                         IR2Remove_, 
                                                                                                                                         send_NIB_back_, 
                                                                                                                                         IRIndex_ >>
                                                                                                                    ELSE /\ IF (nextTrans_[self].name = "RemoveIR")
                                                                                                                               THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                              "Failure of assertion at line 1184, column 17 of macro called at line 1735, column 13.")
                                                                                                                                    /\ IR2Remove_' = [IR2Remove_ EXCEPT ![self] = nextTrans_[self].ops[1].key]
                                                                                                                                    /\ IF \E i \in DOMAIN IRQueueNIB: IRQueueNIB[i].IR = IR2Remove_'[self]
                                                                                                                                          THEN /\ rowRemove_' = [rowRemove_ EXCEPT ![self] = getFirstIndexWithNIB(IR2Remove_'[self], IRQueueNIB)]
                                                                                                                                               /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove_'[self])
                                                                                                                                          ELSE /\ TRUE
                                                                                                                                               /\ UNCHANGED << IRQueueNIB, 
                                                                                                                                                               rowRemove_ >>
                                                                                                                                    /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                    IRStatusNIB, 
                                                                                                                                                    SwSuspensionStatusNIB, 
                                                                                                                                                    SetScheduledIRs, 
                                                                                                                                                    value_N, 
                                                                                                                                                    send_NIB_back_, 
                                                                                                                                                    IRIndex_ >>
                                                                                                                               ELSE /\ IF (nextTrans_[self].name = "OFCChangeIRStatus2Sent")
                                                                                                                                          THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                         "Failure of assertion at line 1192, column 17 of macro called at line 1735, column 13.")
                                                                                                                                               /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                         "Failure of assertion at line 1193, column 17 of macro called at line 1735, column 13.")
                                                                                                                                               /\ IRStatusNIB' = [IRStatusNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                               /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                                                                              IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                              SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                              SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                                                               /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                                                               /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                               SwSuspensionStatusNIB, 
                                                                                                                                                               IRQueueNIB, 
                                                                                                                                                               SetScheduledIRs, 
                                                                                                                                                               IRIndex_ >>
                                                                                                                                          ELSE /\ IF (nextTrans_[self].name = "ChangeSetScheduledIRs")
                                                                                                                                                     THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_SET_SCHEDULED_IRS, 
                                                                                                                                                                    "Failure of assertion at line 1198, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                          /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                                    "Failure of assertion at line 1199, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                          /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                                          /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                          IRStatusNIB, 
                                                                                                                                                                          SwSuspensionStatusNIB, 
                                                                                                                                                                          IRQueueNIB, 
                                                                                                                                                                          value_N, 
                                                                                                                                                                          send_NIB_back_, 
                                                                                                                                                                          IRIndex_ >>
                                                                                                                                                     ELSE /\ IF (nextTrans_[self].name = "UpdateIRTag")
                                                                                                                                                                THEN /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                                                               "Failure of assertion at line 1202, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                                     /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                                               "Failure of assertion at line 1203, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                                     /\ Assert(Len(IRQueueNIB) > 0, 
                                                                                                                                                                               "Failure of assertion at line 1204, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                                     /\ IRIndex_' = [IRIndex_ EXCEPT ![self] = CHOOSE x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans_[self].ops[1].key]
                                                                                                                                                                     /\ Assert(IRIndex_'[self] # -1, 
                                                                                                                                                                               "Failure of assertion at line 1206, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                                     /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![IRIndex_'[self]].tag = nextTrans_[self].ops[1].value]
                                                                                                                                                                     /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                                     IRStatusNIB, 
                                                                                                                                                                                     SwSuspensionStatusNIB, 
                                                                                                                                                                                     value_N, 
                                                                                                                                                                                     send_NIB_back_ >>
                                                                                                                                                                ELSE /\ IF (nextTrans_[self].name = "FirstInstallIR")
                                                                                                                                                                           THEN /\ Assert(Len(nextTrans_[self].ops) = 2, 
                                                                                                                                                                                          "Failure of assertion at line 1209, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                                                /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                                                          "Failure of assertion at line 1210, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                                                /\ IRStatusNIB' = [IRStatusNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                                                                /\ Assert(nextTrans_[self].ops[2].table = NIBT_FIRST_INSTALL, 
                                                                                                                                                                                          "Failure of assertion at line 1212, column 17 of macro called at line 1735, column 13.")
                                                                                                                                                                                /\ FirstInstallNIB' = [FirstInstallNIB EXCEPT ![nextTrans_[self].ops[2].key] = nextTrans_[self].ops[2].value]
                                                                                                                                                                                /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                                                                                                               IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                               SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                               SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                                                                                                /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                                /\ UNCHANGED SwSuspensionStatusNIB
                                                                                                                                                                           ELSE /\ IF (nextTrans_[self].name = "ChangeIRDoneToNone")
                                                                                                                                                                                      THEN /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                                                                     "Failure of assertion at line 1217, column 13 of macro called at line 1735, column 13.")
                                                                                                                                                                                           /\ Assert(nextTrans_[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                                                                     "Failure of assertion at line 1218, column 13 of macro called at line 1735, column 13.")
                                                                                                                                                                                           /\ IRStatusNIB' = [IRStatusNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                                                                           /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                                                                                                                          IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                                          SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                                          SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                                                                                                           /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                                           /\ UNCHANGED SwSuspensionStatusNIB
                                                                                                                                                                                      ELSE /\ IF (nextTrans_[self].name = "SwitchDown")
                                                                                                                                                                                                 THEN /\ Assert(Len(nextTrans_[self].ops) = 1, 
                                                                                                                                                                                                                "Failure of assertion at line 1223, column 13 of macro called at line 1735, column 13.")
                                                                                                                                                                                                      /\ Assert(nextTrans_[self].ops[1].table = NIBT_SW_STATUS, 
                                                                                                                                                                                                                "Failure of assertion at line 1224, column 13 of macro called at line 1735, column 13.")
                                                                                                                                                                                                      /\ SwSuspensionStatusNIB' = [SwSuspensionStatusNIB EXCEPT ![nextTrans_[self].ops[1].key] = nextTrans_[self].ops[1].value]
                                                                                                                                                                                                      /\ value_N' = [value_N EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                                                                                                                                                     IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                                                     SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                                                     SwSuspensionStatusNIB |-> SwSuspensionStatusNIB']]
                                                                                                                                                                                                      /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                                                 ELSE /\ TRUE
                                                                                                                                                                                                      /\ UNCHANGED << SwSuspensionStatusNIB, 
                                                                                                                                                                                                                      value_N, 
                                                                                                                                                                                                                      send_NIB_back_ >>
                                                                                                                                                                                           /\ UNCHANGED IRStatusNIB
                                                                                                                                                                                /\ UNCHANGED FirstInstallNIB
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
                                                            IRStatusNIB, 
                                                            SwSuspensionStatusNIB, 
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
                                                 irTypeMapping, 
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
                                                 dependencyGraph, ir2sw, 
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 SwSuspensionStatusRC, 
                                                 IRQueueRC, SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, IRChangeForRC, 
                                                 TopoChangeForRC, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 IRDoneSet, 
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
                                                 FlagNIBOFCEventhandlerFailover, 
                                                 NIB_READY_FOR_RC, 
                                                 NIB_READY_FOR_OFC, 
                                                 masterState, X2NIB_len, 
                                                 NIBThreadID, RCThreadID, 
                                                 ingressPkt, ingressIR, 
                                                 egressMsg, ofaInMsg, 
                                                 ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem, value_, 
                                                 nextTrans_, stepOfFailure_, 
                                                 nextTrans, value, rowRemove_N, 
                                                 IR2Remove, send_NIB_back, 
                                                 stepOfFailure_N, IRIndex, 
                                                 debug_N, NIBMsg_, 
                                                 isBootStrap_, sw_id, 
                                                 transaction_, topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, toBeScheduledIRs, 
                                                 nextIR, transaction_c, 
                                                 stepOfFailure_c, currDAG, 
                                                 IRSet, key, op1_, op2, debug, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 newIRSet, newIR, nextIRToSent, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_co, 
                                                 transaction_co, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, 
                                                 transaction_con, topo_change, 
                                                 irID, removedIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBUpdateRCIfAny(self) == /\ pc[self] = "NIBUpdateRCIfAny"
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ IF moduleIsUp(self)
                                THEN /\ IF send_NIB_back_[self] = "NIB2RC"
                                           THEN /\ isRCUp(RCThreadID)
                                                /\ NIB2RC' = Append(NIB2RC, [value |-> value_N[self]])
                                                /\ UNCHANGED NIB2OFC
                                           ELSE /\ IF send_NIB_back_[self] = "NIB2OFC"
                                                      THEN /\ isOFCUp(RCThreadID)
                                                           /\ NIB2OFC' = Append(NIB2OFC, [value |-> value_N[self]])
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED NIB2OFC
                                                /\ UNCHANGED NIB2RC
                                     /\ send_NIB_back_' = [send_NIB_back_ EXCEPT ![self] = ""]
                                     /\ pc' = [pc EXCEPT ![self] = "NIBDequeueRCTransaction"]
                                     /\ UNCHANGED FlagNIBRCEventhandlerFailover
                                ELSE /\ FlagNIBRCEventhandlerFailover' = TRUE
                                     /\ pc' = [pc EXCEPT ![self] = "NIBForRCReconciliation"]
                                     /\ UNCHANGED << NIB2OFC, NIB2RC, 
                                                     send_NIB_back_ >>
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          FirstInstallOFC, FirstInstallNIB, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, irTypeMapping, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          ir2sw, NIBUpdateForRC, 
                                          controllerStateRC, IRStatusRC, 
                                          SwSuspensionStatusRC, IRQueueRC, 
                                          SetScheduledIRsRC, 
                                          FlagRCNIBEventHandlerFailover, 
                                          FlagRCSequencerFailover, RC_READY, 
                                          IRChangeForRC, TopoChangeForRC, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, DAGID, MaxDAGID, DAGState, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          IRDoneSet, idThreadWorkingOnIR, 
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
                                          IRStatusNIB, SwSuspensionStatusNIB, 
                                          IRQueueNIB, SetScheduledIRs, 
                                          X2NIB_len, NIBThreadID, RCThreadID, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, obj, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, value_, nextTrans_, 
                                          value_N, rowRemove_, IR2Remove_, 
                                          stepOfFailure_, IRIndex_, debug_, 
                                          nextTrans, value, rowRemove_N, 
                                          IR2Remove, send_NIB_back, 
                                          stepOfFailure_N, IRIndex, debug_N, 
                                          NIBMsg_, isBootStrap_, sw_id, 
                                          transaction_, topoChangeEvent, 
                                          currSetDownSw, prev_dag_id, init, 
                                          nxtDAG, setRemovableIRs, currIR, 
                                          currIRInDAG, nxtDAGVertices, 
                                          setIRsInDAG, prev_dag, 
                                          toBeScheduledIRs, nextIR, 
                                          transaction_c, stepOfFailure_c, 
                                          currDAG, IRSet, key, op1_, op2, 
                                          debug, transaction_O, IRQueueTmp, 
                                          NIBMsg_O, isBootStrap, localIRSet, 
                                          NIBIRSet, newIRSet, newIR, 
                                          nextIRToSent, rowIndex, rowRemove, 
                                          stepOfFailure_co, transaction_co, 
                                          NIBMsg, op1, IRQueue, 
                                          op_ir_status_change_, removeIR, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, 
                                          transaction_con, topo_change, irID, 
                                          removedIR, msg, op_ir_status_change, 
                                          op_first_install, transaction >>

NIBForRCReconciliation(self) == /\ pc[self] = "NIBForRCReconciliation"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
                                   controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed
                                /\ pc' = [pc EXCEPT ![self] = "NIBDequeueRCTransaction"]
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstallOFC, 
                                                FirstInstallNIB, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, 
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
                                                dependencyGraph, ir2sw, 
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                SwSuspensionStatusRC, 
                                                IRQueueRC, SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, IRChangeForRC, 
                                                TopoChangeForRC, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
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
                                                controllerStateNIB, 
                                                IRStatusNIB, 
                                                SwSuspensionStatusNIB, 
                                                IRQueueNIB, SetScheduledIRs, 
                                                X2NIB_len, NIBThreadID, 
                                                RCThreadID, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug_N, NIBMsg_, 
                                                isBootStrap_, sw_id, 
                                                transaction_, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, nxtDAG, setRemovableIRs, 
                                                currIR, currIRInDAG, 
                                                nxtDAGVertices, setIRsInDAG, 
                                                prev_dag, toBeScheduledIRs, 
                                                nextIR, transaction_c, 
                                                stepOfFailure_c, currDAG, 
                                                IRSet, key, op1_, op2, debug, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, newIRSet, 
                                                newIR, nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_co, 
                                                transaction_co, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, transaction_con, 
                                                topo_change, irID, removedIR, 
                                                msg, op_ir_status_change, 
                                                op_first_install, transaction >>

NIBRCEventHandler(self) == NIBDequeueRCTransaction(self)
                              \/ NIBProcessRCTransaction(self)
                              \/ NIBUpdateRCIfAny(self)
                              \/ NIBForRCReconciliation(self)

NIBDequeueOFCTransaction(self) == /\ pc[self] = "NIBDequeueOFCTransaction"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = ""]
                                  /\ IF moduleIsUp(self)
                                        THEN /\ OFC2NIB # <<>>
                                             /\ nextTrans' = [nextTrans EXCEPT ![self] = Head(OFC2NIB)]
                                             /\ OFC2NIB' = Tail(OFC2NIB)
                                             /\ pc' = [pc EXCEPT ![self] = "NIBOFCProcessTransaction"]
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
                                                  irTypeMapping, 
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
                                                  dependencyGraph, ir2sw, 
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, 
                                                  SwSuspensionStatusRC, 
                                                  IRQueueRC, SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, IRChangeForRC, 
                                                  TopoChangeForRC, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, DAGID, MaxDAGID, 
                                                  DAGState, nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
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
                                                  controllerStateNIB, 
                                                  IRStatusNIB, 
                                                  SwSuspensionStatusNIB, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
                                                  statusResolveMsg, 
                                                  recoveredElem, value_, 
                                                  nextTrans_, value_N, 
                                                  rowRemove_, IR2Remove_, 
                                                  send_NIB_back_, 
                                                  stepOfFailure_, IRIndex_, 
                                                  debug_, value, rowRemove_N, 
                                                  IR2Remove, stepOfFailure_N, 
                                                  IRIndex, debug_N, NIBMsg_, 
                                                  isBootStrap_, sw_id, 
                                                  transaction_, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  toBeScheduledIRs, nextIR, 
                                                  transaction_c, 
                                                  stepOfFailure_c, currDAG, 
                                                  IRSet, key, op1_, op2, debug, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  newIRSet, newIR, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_co, 
                                                  transaction_co, NIBMsg, op1, 
                                                  IRQueue, 
                                                  op_ir_status_change_, 
                                                  removeIR, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, 
                                                  transaction_con, topo_change, 
                                                  irID, removedIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

NIBOFCProcessTransaction(self) == /\ pc[self] = "NIBOFCProcessTransaction"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF moduleIsUp(self)
                                        THEN /\ IF (nextTrans[self].name = "PrepareIR")
                                                   THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                                  "Failure of assertion at line 1129, column 9 of macro called at line 1789, column 13.")
                                                        /\ Assert(Len(nextTrans[self].ops[1].key) = 2, 
                                                                  "Failure of assertion at line 1130, column 9 of macro called at line 1789, column 13.")
                                                        /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                        /\ Assert(nextTrans[self].ops[2].table = NIBT_SET_SCHEDULED_IRS, 
                                                                  "Failure of assertion at line 1132, column 9 of macro called at line 1789, column 13.")
                                                        /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans[self].ops[2].key] = nextTrans[self].ops[2].value]
                                                        /\ UNCHANGED << FirstInstallNIB, 
                                                                        IRStatusNIB, 
                                                                        SwSuspensionStatusNIB, 
                                                                        IRQueueNIB, 
                                                                        value, 
                                                                        rowRemove_N, 
                                                                        IR2Remove, 
                                                                        send_NIB_back, 
                                                                        IRIndex >>
                                                   ELSE /\ IF (nextTrans[self].name = "ScheduleIR")
                                                              THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                             "Failure of assertion at line 1138, column 9 of macro called at line 1789, column 13.")
                                                                   /\ IF ~\E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans[self].ops[1].value.IR
                                                                         THEN /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans[self].ops[1].value)
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED IRQueueNIB
                                                                   /\ Assert(nextTrans[self].ops[2].table = NIBT_CONTROLLER_STATE, 
                                                                             "Failure of assertion at line 1142, column 9 of macro called at line 1789, column 13.")
                                                                   /\ Assert(Len(nextTrans[self].ops[2].key) = 2, 
                                                                             "Failure of assertion at line 1143, column 9 of macro called at line 1789, column 13.")
                                                                   /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans[self].ops[2].key] = nextTrans[self].ops[2].value]
                                                                   /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                              IRQueueNIB |->IRQueueNIB',
                                                                                                              SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                              SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                   /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2OFC"]
                                                                   /\ UNCHANGED << FirstInstallNIB, 
                                                                                   IRStatusNIB, 
                                                                                   SwSuspensionStatusNIB, 
                                                                                   SetScheduledIRs, 
                                                                                   rowRemove_N, 
                                                                                   IR2Remove, 
                                                                                   IRIndex >>
                                                              ELSE /\ IF (nextTrans[self].name = "RCScheduleIRInOneStep")
                                                                         THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                        "Failure of assertion at line 1149, column 9 of macro called at line 1789, column 13.")
                                                                              /\ IF ~\E x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans[self].ops[1].value.IR
                                                                                    THEN /\ IRQueueNIB' = Append(IRQueueNIB, nextTrans[self].ops[1].value)
                                                                                    ELSE /\ TRUE
                                                                                         /\ UNCHANGED IRQueueNIB
                                                                              /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                         IRQueueNIB |->IRQueueNIB',
                                                                                                                         SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                         SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                              /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2OFC"]
                                                                              /\ UNCHANGED << FirstInstallNIB, 
                                                                                              controllerStateNIB, 
                                                                                              IRStatusNIB, 
                                                                                              SwSuspensionStatusNIB, 
                                                                                              SetScheduledIRs, 
                                                                                              rowRemove_N, 
                                                                                              IR2Remove, 
                                                                                              IRIndex >>
                                                                         ELSE /\ IF (nextTrans[self].name = "SeqReadNIBStates")
                                                                                    THEN /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                                    IRQueueNIB |->IRQueueNIB,
                                                                                                                                    SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                    SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                         /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                         /\ UNCHANGED << FirstInstallNIB, 
                                                                                                         controllerStateNIB, 
                                                                                                         IRStatusNIB, 
                                                                                                         SwSuspensionStatusNIB, 
                                                                                                         IRQueueNIB, 
                                                                                                         SetScheduledIRs, 
                                                                                                         rowRemove_N, 
                                                                                                         IR2Remove, 
                                                                                                         IRIndex >>
                                                                                    ELSE /\ IF (nextTrans[self].name = "OFCOverrideIRStatus")
                                                                                               THEN /\ IRStatusNIB' = nextTrans[self].ops[1]
                                                                                                    /\ FirstInstallNIB' = nextTrans[self].ops[2]
                                                                                                    /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                               IRQueueNIB |->IRQueueNIB,
                                                                                                                                               SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                               SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                    /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                    /\ UNCHANGED << controllerStateNIB, 
                                                                                                                    SwSuspensionStatusNIB, 
                                                                                                                    IRQueueNIB, 
                                                                                                                    SetScheduledIRs, 
                                                                                                                    rowRemove_N, 
                                                                                                                    IR2Remove, 
                                                                                                                    IRIndex >>
                                                                                               ELSE /\ IF (nextTrans[self].name = "OFCReadNIBStates")
                                                                                                          THEN /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                                                          IRQueueNIB |->IRQueueNIB,
                                                                                                                                                          SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                          SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                               /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2OFC"]
                                                                                                               /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                               controllerStateNIB, 
                                                                                                                               IRStatusNIB, 
                                                                                                                               SwSuspensionStatusNIB, 
                                                                                                                               IRQueueNIB, 
                                                                                                                               SetScheduledIRs, 
                                                                                                                               rowRemove_N, 
                                                                                                                               IR2Remove, 
                                                                                                                               IRIndex >>
                                                                                                          ELSE /\ IF (nextTrans[self].name = "UpdateControllerState")
                                                                                                                     THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_CONTROLLER_STATE, 
                                                                                                                                    "Failure of assertion at line 1180, column 17 of macro called at line 1789, column 13.")
                                                                                                                          /\ Assert(Len(nextTrans[self].ops[1].key) = 2, 
                                                                                                                                    "Failure of assertion at line 1181, column 17 of macro called at line 1789, column 13.")
                                                                                                                          /\ controllerStateNIB' = [controllerStateNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                          /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                          IRStatusNIB, 
                                                                                                                                          SwSuspensionStatusNIB, 
                                                                                                                                          IRQueueNIB, 
                                                                                                                                          SetScheduledIRs, 
                                                                                                                                          value, 
                                                                                                                                          rowRemove_N, 
                                                                                                                                          IR2Remove, 
                                                                                                                                          send_NIB_back, 
                                                                                                                                          IRIndex >>
                                                                                                                     ELSE /\ IF (nextTrans[self].name = "RemoveIR")
                                                                                                                                THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                               "Failure of assertion at line 1184, column 17 of macro called at line 1789, column 13.")
                                                                                                                                     /\ IR2Remove' = [IR2Remove EXCEPT ![self] = nextTrans[self].ops[1].key]
                                                                                                                                     /\ IF \E i \in DOMAIN IRQueueNIB: IRQueueNIB[i].IR = IR2Remove'[self]
                                                                                                                                           THEN /\ rowRemove_N' = [rowRemove_N EXCEPT ![self] = getFirstIndexWithNIB(IR2Remove'[self], IRQueueNIB)]
                                                                                                                                                /\ IRQueueNIB' = removeFromSeq(IRQueueNIB, rowRemove_N'[self])
                                                                                                                                           ELSE /\ TRUE
                                                                                                                                                /\ UNCHANGED << IRQueueNIB, 
                                                                                                                                                                rowRemove_N >>
                                                                                                                                     /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                     IRStatusNIB, 
                                                                                                                                                     SwSuspensionStatusNIB, 
                                                                                                                                                     SetScheduledIRs, 
                                                                                                                                                     value, 
                                                                                                                                                     send_NIB_back, 
                                                                                                                                                     IRIndex >>
                                                                                                                                ELSE /\ IF (nextTrans[self].name = "OFCChangeIRStatus2Sent")
                                                                                                                                           THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                          "Failure of assertion at line 1192, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                          "Failure of assertion at line 1193, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                /\ IRStatusNIB' = [IRStatusNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                                /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                                                                           IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                           SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                           SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                                                                /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                SwSuspensionStatusNIB, 
                                                                                                                                                                IRQueueNIB, 
                                                                                                                                                                SetScheduledIRs, 
                                                                                                                                                                IRIndex >>
                                                                                                                                           ELSE /\ IF (nextTrans[self].name = "ChangeSetScheduledIRs")
                                                                                                                                                      THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_SET_SCHEDULED_IRS, 
                                                                                                                                                                     "Failure of assertion at line 1198, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                           /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                                     "Failure of assertion at line 1199, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                           /\ SetScheduledIRs' = [SetScheduledIRs EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                                           /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                           IRStatusNIB, 
                                                                                                                                                                           SwSuspensionStatusNIB, 
                                                                                                                                                                           IRQueueNIB, 
                                                                                                                                                                           value, 
                                                                                                                                                                           send_NIB_back, 
                                                                                                                                                                           IRIndex >>
                                                                                                                                                      ELSE /\ IF (nextTrans[self].name = "UpdateIRTag")
                                                                                                                                                                 THEN /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_QUEUE, 
                                                                                                                                                                                "Failure of assertion at line 1202, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                                      /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                                                "Failure of assertion at line 1203, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                                      /\ Assert(Len(IRQueueNIB) > 0, 
                                                                                                                                                                                "Failure of assertion at line 1204, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                                      /\ IRIndex' = [IRIndex EXCEPT ![self] = CHOOSE x \in DOMAIN IRQueueNIB: IRQueueNIB[x].IR = nextTrans[self].ops[1].key]
                                                                                                                                                                      /\ Assert(IRIndex'[self] # -1, 
                                                                                                                                                                                "Failure of assertion at line 1206, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                                      /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![IRIndex'[self]].tag = nextTrans[self].ops[1].value]
                                                                                                                                                                      /\ UNCHANGED << FirstInstallNIB, 
                                                                                                                                                                                      IRStatusNIB, 
                                                                                                                                                                                      SwSuspensionStatusNIB, 
                                                                                                                                                                                      value, 
                                                                                                                                                                                      send_NIB_back >>
                                                                                                                                                                 ELSE /\ IF (nextTrans[self].name = "FirstInstallIR")
                                                                                                                                                                            THEN /\ Assert(Len(nextTrans[self].ops) = 2, 
                                                                                                                                                                                           "Failure of assertion at line 1209, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                                                 /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                                                           "Failure of assertion at line 1210, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                                                 /\ IRStatusNIB' = [IRStatusNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                                                                 /\ Assert(nextTrans[self].ops[2].table = NIBT_FIRST_INSTALL, 
                                                                                                                                                                                           "Failure of assertion at line 1212, column 17 of macro called at line 1789, column 13.")
                                                                                                                                                                                 /\ FirstInstallNIB' = [FirstInstallNIB EXCEPT ![nextTrans[self].ops[2].key] = nextTrans[self].ops[2].value]
                                                                                                                                                                                 /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                                                                                                            IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                            SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                            SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                                                                                                 /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                                 /\ UNCHANGED SwSuspensionStatusNIB
                                                                                                                                                                            ELSE /\ IF (nextTrans[self].name = "ChangeIRDoneToNone")
                                                                                                                                                                                       THEN /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                                                                      "Failure of assertion at line 1217, column 13 of macro called at line 1789, column 13.")
                                                                                                                                                                                            /\ Assert(nextTrans[self].ops[1].table = NIBT_IR_STATUS, 
                                                                                                                                                                                                      "Failure of assertion at line 1218, column 13 of macro called at line 1789, column 13.")
                                                                                                                                                                                            /\ IRStatusNIB' = [IRStatusNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                                                                            /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB',
                                                                                                                                                                                                                                       IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                                       SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                                       SwSuspensionStatusNIB |-> SwSuspensionStatusNIB]]
                                                                                                                                                                                            /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                                            /\ UNCHANGED SwSuspensionStatusNIB
                                                                                                                                                                                       ELSE /\ IF (nextTrans[self].name = "SwitchDown")
                                                                                                                                                                                                  THEN /\ Assert(Len(nextTrans[self].ops) = 1, 
                                                                                                                                                                                                                 "Failure of assertion at line 1223, column 13 of macro called at line 1789, column 13.")
                                                                                                                                                                                                       /\ Assert(nextTrans[self].ops[1].table = NIBT_SW_STATUS, 
                                                                                                                                                                                                                 "Failure of assertion at line 1224, column 13 of macro called at line 1789, column 13.")
                                                                                                                                                                                                       /\ SwSuspensionStatusNIB' = [SwSuspensionStatusNIB EXCEPT ![nextTrans[self].ops[1].key] = nextTrans[self].ops[1].value]
                                                                                                                                                                                                       /\ value' = [value EXCEPT ![self] = [IRStatusNIB |-> IRStatusNIB,
                                                                                                                                                                                                                                                  IRQueueNIB |->IRQueueNIB,
                                                                                                                                                                                                                                                  SetScheduledIRsNIB |-> SetScheduledIRs,
                                                                                                                                                                                                                                                  SwSuspensionStatusNIB |-> SwSuspensionStatusNIB']]
                                                                                                                                                                                                       /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = "NIB2RC"]
                                                                                                                                                                                                  ELSE /\ TRUE
                                                                                                                                                                                                       /\ UNCHANGED << SwSuspensionStatusNIB, 
                                                                                                                                                                                                                       value, 
                                                                                                                                                                                                                       send_NIB_back >>
                                                                                                                                                                                            /\ UNCHANGED IRStatusNIB
                                                                                                                                                                                 /\ UNCHANGED FirstInstallNIB
                                                                                                                                                                      /\ UNCHANGED << IRQueueNIB, 
                                                                                                                                                                                      IRIndex >>
                                                                                                                                                           /\ UNCHANGED SetScheduledIRs
                                                                                                                                     /\ UNCHANGED << rowRemove_N, 
                                                                                                                                                     IR2Remove >>
                                                                                                                          /\ UNCHANGED controllerStateNIB
                                             /\ debug_N' = [debug_N EXCEPT ![self] = 0]
                                             /\ pc' = [pc EXCEPT ![self] = "NIBOFCSendBackIfAny"]
                                             /\ UNCHANGED FlagNIBOFCEventhandlerFailover
                                        ELSE /\ FlagNIBOFCEventhandlerFailover' = TRUE
                                             /\ pc' = [pc EXCEPT ![self] = "NIBForOFCReconciliation"]
                                             /\ UNCHANGED << FirstInstallNIB, 
                                                             controllerStateNIB, 
                                                             IRStatusNIB, 
                                                             SwSuspensionStatusNIB, 
                                                             IRQueueNIB, 
                                                             SetScheduledIRs, 
                                                             value, 
                                                             rowRemove_N, 
                                                             IR2Remove, 
                                                             send_NIB_back, 
                                                             IRIndex, debug_N >>
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstallOFC, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, 
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
                                                  dependencyGraph, ir2sw, 
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, 
                                                  SwSuspensionStatusRC, 
                                                  IRQueueRC, SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, IRChangeForRC, 
                                                  TopoChangeForRC, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, DAGID, MaxDAGID, 
                                                  DAGState, nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
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
                                                  NIB_READY_FOR_RC, 
                                                  NIB_READY_FOR_OFC, 
                                                  masterState, X2NIB_len, 
                                                  NIBThreadID, RCThreadID, 
                                                  ingressPkt, ingressIR, 
                                                  egressMsg, ofaInMsg, 
                                                  ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
                                                  statusResolveMsg, 
                                                  recoveredElem, value_, 
                                                  nextTrans_, value_N, 
                                                  rowRemove_, IR2Remove_, 
                                                  send_NIB_back_, 
                                                  stepOfFailure_, IRIndex_, 
                                                  debug_, nextTrans, 
                                                  stepOfFailure_N, NIBMsg_, 
                                                  isBootStrap_, sw_id, 
                                                  transaction_, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  toBeScheduledIRs, nextIR, 
                                                  transaction_c, 
                                                  stepOfFailure_c, currDAG, 
                                                  IRSet, key, op1_, op2, debug, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  newIRSet, newIR, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_co, 
                                                  transaction_co, NIBMsg, op1, 
                                                  IRQueue, 
                                                  op_ir_status_change_, 
                                                  removeIR, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, 
                                                  transaction_con, topo_change, 
                                                  irID, removedIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

NIBOFCSendBackIfAny(self) == /\ pc[self] = "NIBOFCSendBackIfAny"
                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ IF moduleIsUp(self)
                                   THEN /\ IF send_NIB_back[self] = "NIB2RC"
                                              THEN /\ isRCUp(RCThreadID)
                                                   /\ NIB2RC' = Append(NIB2RC, [value |-> value[self]])
                                                   /\ UNCHANGED NIB2OFC
                                              ELSE /\ IF send_NIB_back[self] = "NIB2OFC"
                                                         THEN /\ isOFCUp(RCThreadID)
                                                              /\ NIB2OFC' = Append(NIB2OFC, [value |-> value[self]])
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED NIB2OFC
                                                   /\ UNCHANGED NIB2RC
                                        /\ send_NIB_back' = [send_NIB_back EXCEPT ![self] = ""]
                                        /\ pc' = [pc EXCEPT ![self] = "NIBDequeueOFCTransaction"]
                                        /\ UNCHANGED FlagNIBOFCEventhandlerFailover
                                   ELSE /\ FlagNIBOFCEventhandlerFailover' = TRUE
                                        /\ pc' = [pc EXCEPT ![self] = "NIBForOFCReconciliation"]
                                        /\ UNCHANGED << NIB2OFC, NIB2RC, 
                                                        send_NIB_back >>
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstallOFC, FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, 
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
                                             switchOrdering, dependencyGraph, 
                                             ir2sw, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             SwSuspensionStatusRC, IRQueueRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             IRChangeForRC, TopoChangeForRC, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, DAGID, MaxDAGID, 
                                             DAGState, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, IRDoneSet, 
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
                                             NIB_READY_FOR_RC, 
                                             NIB_READY_FOR_OFC, masterState, 
                                             controllerStateNIB, IRStatusNIB, 
                                             SwSuspensionStatusNIB, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, obj, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, value_, nextTrans_, 
                                             value_N, rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             stepOfFailure_N, IRIndex, debug_N, 
                                             NIBMsg_, isBootStrap_, sw_id, 
                                             transaction_, topoChangeEvent, 
                                             currSetDownSw, prev_dag_id, init, 
                                             nxtDAG, setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, 
                                             toBeScheduledIRs, nextIR, 
                                             transaction_c, stepOfFailure_c, 
                                             currDAG, IRSet, key, op1_, op2, 
                                             debug, transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, newIRSet, newIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_co, transaction_co, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, 
                                             transaction_con, topo_change, 
                                             irID, removedIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

NIBForOFCReconciliation(self) == /\ pc[self] = "NIBForOFCReconciliation"
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ controllerSubmoduleFailStat[<<nib0,CONT_NIB_OFC_EVENT>>] = NotFailed /\
                                    controllerSubmoduleFailStat[<<nib0,CONT_NIB_RC_EVENT>>] = NotFailed
                                 /\ pc' = [pc EXCEPT ![self] = "NIBDequeueOFCTransaction"]
                                 /\ UNCHANGED << switchLock, controllerLock, 
                                                 FirstInstallOFC, 
                                                 FirstInstallNIB, 
                                                 sw_fail_ordering_var, 
                                                 ContProcSet, SwProcSet, 
                                                 irTypeMapping, 
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
                                                 dependencyGraph, ir2sw, 
                                                 NIBUpdateForRC, 
                                                 controllerStateRC, IRStatusRC, 
                                                 SwSuspensionStatusRC, 
                                                 IRQueueRC, SetScheduledIRsRC, 
                                                 FlagRCNIBEventHandlerFailover, 
                                                 FlagRCSequencerFailover, 
                                                 RC_READY, IRChangeForRC, 
                                                 TopoChangeForRC, TEEventQueue, 
                                                 DAGEventQueue, DAGQueue, 
                                                 DAGID, MaxDAGID, DAGState, 
                                                 nxtRCIRID, 
                                                 idWorkerWorkingOnDAG, 
                                                 IRDoneSet, 
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
                                                 IRStatusNIB, 
                                                 SwSuspensionStatusNIB, 
                                                 IRQueueNIB, SetScheduledIRs, 
                                                 X2NIB_len, NIBThreadID, 
                                                 RCThreadID, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
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
                                                 debug_N, NIBMsg_, 
                                                 isBootStrap_, sw_id, 
                                                 transaction_, topoChangeEvent, 
                                                 currSetDownSw, prev_dag_id, 
                                                 init, nxtDAG, setRemovableIRs, 
                                                 currIR, currIRInDAG, 
                                                 nxtDAGVertices, setIRsInDAG, 
                                                 prev_dag, toBeScheduledIRs, 
                                                 nextIR, transaction_c, 
                                                 stepOfFailure_c, currDAG, 
                                                 IRSet, key, op1_, op2, debug, 
                                                 transaction_O, IRQueueTmp, 
                                                 NIBMsg_O, isBootStrap, 
                                                 localIRSet, NIBIRSet, 
                                                 newIRSet, newIR, nextIRToSent, 
                                                 rowIndex, rowRemove, 
                                                 stepOfFailure_co, 
                                                 transaction_co, NIBMsg, op1, 
                                                 IRQueue, op_ir_status_change_, 
                                                 removeIR, monitoringEvent, 
                                                 setIRsToReset, resetIR, 
                                                 stepOfFailure, 
                                                 transaction_con, topo_change, 
                                                 irID, removedIR, msg, 
                                                 op_ir_status_change, 
                                                 op_first_install, transaction >>

NIBOFCEventHandler(self) == NIBDequeueOFCTransaction(self)
                               \/ NIBOFCProcessTransaction(self)
                               \/ NIBOFCSendBackIfAny(self)
                               \/ NIBForOFCReconciliation(self)

RCFailoverResetStates(self) == /\ pc[self] = "RCFailoverResetStates"
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = Failed /\
                                    controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = Failed
                               /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<rc0,CONT_WORKER_SEQ>>] = InReconciliation,
                                                                                                     ![<<rc0,CONT_RC_NIB_EVENT>>] = InReconciliation]
                               /\ FlagRCNIBEventHandlerFailover /\ FlagRCSequencerFailover
                               /\ NIB2RC' = <<>>
                               /\ RC2NIB' = <<>>
                               /\ SetScheduledIRsRC' = [y \in SW |-> {}]
                               /\ IRQueueRC' = <<>>
                               /\ RC_READY' = FALSE
                               /\ pc' = [pc EXCEPT ![self] = "RCReadNIB"]
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstallOFC, 
                                               FirstInstallNIB, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, 
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
                                               switchOrdering, dependencyGraph, 
                                               ir2sw, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               SwSuspensionStatusRC, 
                                               FlagRCNIBEventHandlerFailover, 
                                               FlagRCSequencerFailover, 
                                               IRChangeForRC, TopoChangeForRC, 
                                               TEEventQueue, DAGEventQueue, 
                                               DAGQueue, DAGID, MaxDAGID, 
                                               DAGState, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, IRDoneSet, 
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
                                               X2NIB, OFC2NIB, FlagNIBFailover, 
                                               FlagNIBRCEventhandlerFailover, 
                                               FlagNIBOFCEventhandlerFailover, 
                                               NIB_READY_FOR_RC, 
                                               NIB_READY_FOR_OFC, masterState, 
                                               controllerStateNIB, IRStatusNIB, 
                                               SwSuspensionStatusNIB, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               X2NIB_len, NIBThreadID, 
                                               RCThreadID, ingressPkt, 
                                               ingressIR, egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, value, 
                                               rowRemove_N, IR2Remove, 
                                               send_NIB_back, stepOfFailure_N, 
                                               IRIndex, debug_N, NIBMsg_, 
                                               isBootStrap_, sw_id, 
                                               transaction_, topoChangeEvent, 
                                               currSetDownSw, prev_dag_id, 
                                               init, nxtDAG, setRemovableIRs, 
                                               currIR, currIRInDAG, 
                                               nxtDAGVertices, setIRsInDAG, 
                                               prev_dag, toBeScheduledIRs, 
                                               nextIR, transaction_c, 
                                               stepOfFailure_c, currDAG, IRSet, 
                                               key, op1_, op2, debug, 
                                               transaction_O, IRQueueTmp, 
                                               NIBMsg_O, isBootStrap, 
                                               localIRSet, NIBIRSet, newIRSet, 
                                               newIR, nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure_co, 
                                               transaction_co, NIBMsg, op1, 
                                               IRQueue, op_ir_status_change_, 
                                               removeIR, monitoringEvent, 
                                               setIRsToReset, resetIR, 
                                               stepOfFailure, transaction_con, 
                                               topo_change, irID, removedIR, 
                                               msg, op_ir_status_change, 
                                               op_first_install, transaction >>

RCReadNIB(self) == /\ pc[self] = "RCReadNIB"
                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                   /\ NIB_READY_FOR_RC \/ isNIBUp(NIBThreadID)
                   /\ IRStatusRC' = IRStatusNIB
                   /\ SwSuspensionStatusRC' = SwSuspensionStatusNIB
                   /\ RC_READY' = TRUE
                   /\ pc' = [pc EXCEPT ![self] = "RCBack2Normal"]
                   /\ UNCHANGED << switchLock, controllerLock, FirstInstallOFC, 
                                   FirstInstallNIB, sw_fail_ordering_var, 
                                   ContProcSet, SwProcSet, irTypeMapping, 
                                   swSeqChangedStatus, controller2Switch, 
                                   switch2Controller, switchStatus, 
                                   installedIRs, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   RecoveryStatus, controllerSubmoduleFailNum, 
                                   controllerSubmoduleFailStat, switchOrdering, 
                                   dependencyGraph, ir2sw, NIBUpdateForRC, 
                                   controllerStateRC, IRQueueRC, 
                                   SetScheduledIRsRC, 
                                   FlagRCNIBEventHandlerFailover, 
                                   FlagRCSequencerFailover, IRChangeForRC, 
                                   TopoChangeForRC, TEEventQueue, 
                                   DAGEventQueue, DAGQueue, DAGID, MaxDAGID, 
                                   DAGState, nxtRCIRID, idWorkerWorkingOnDAG, 
                                   IRDoneSet, idThreadWorkingOnIR, 
                                   workerThreadRanking, controllerStateOFC, 
                                   IRStatusOFC, IRQueueOFC, 
                                   SwSuspensionStatusOFC, SetScheduledIRsOFC, 
                                   FlagOFCWorkerFailover, 
                                   FlagOFCMonitorFailover, 
                                   FlagOFCNIBEventHandlerFailover, OFCThreadID, 
                                   OFC_READY, NIB2OFC, NIB2RC, X2NIB, OFC2NIB, 
                                   RC2NIB, FlagNIBFailover, 
                                   FlagNIBRCEventhandlerFailover, 
                                   FlagNIBOFCEventhandlerFailover, 
                                   NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                   masterState, controllerStateNIB, 
                                   IRStatusNIB, SwSuspensionStatusNIB, 
                                   IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                   NIBThreadID, RCThreadID, ingressPkt, 
                                   ingressIR, egressMsg, ofaInMsg, 
                                   ofaOutConfirmation, installerInIR, 
                                   statusMsg, notFailedSet, failedElem, obj, 
                                   failedSet, statusResolveMsg, recoveredElem, 
                                   value_, nextTrans_, value_N, rowRemove_, 
                                   IR2Remove_, send_NIB_back_, stepOfFailure_, 
                                   IRIndex_, debug_, nextTrans, value, 
                                   rowRemove_N, IR2Remove, send_NIB_back, 
                                   stepOfFailure_N, IRIndex, debug_N, NIBMsg_, 
                                   isBootStrap_, sw_id, transaction_, 
                                   topoChangeEvent, currSetDownSw, prev_dag_id, 
                                   init, nxtDAG, setRemovableIRs, currIR, 
                                   currIRInDAG, nxtDAGVertices, setIRsInDAG, 
                                   prev_dag, toBeScheduledIRs, nextIR, 
                                   transaction_c, stepOfFailure_c, currDAG, 
                                   IRSet, key, op1_, op2, debug, transaction_O, 
                                   IRQueueTmp, NIBMsg_O, isBootStrap, 
                                   localIRSet, NIBIRSet, newIRSet, newIR, 
                                   nextIRToSent, rowIndex, rowRemove, 
                                   stepOfFailure_co, transaction_co, NIBMsg, 
                                   op1, IRQueue, op_ir_status_change_, 
                                   removeIR, monitoringEvent, setIRsToReset, 
                                   resetIR, stepOfFailure, transaction_con, 
                                   topo_change, irID, removedIR, msg, 
                                   op_ir_status_change, op_first_install, 
                                   transaction >>

RCBack2Normal(self) == /\ pc[self] = "RCBack2Normal"
                       /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                       /\ switchLock = <<NO_LOCK, NO_LOCK>>
                       /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<rc0,CONT_WORKER_SEQ>>] = NotFailed,
                                                                                             ![<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed]
                       /\ NIBUpdateForRC' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       FirstInstallOFC, FirstInstallNIB, 
                                       sw_fail_ordering_var, ContProcSet, 
                                       SwProcSet, irTypeMapping, 
                                       swSeqChangedStatus, controller2Switch, 
                                       switch2Controller, switchStatus, 
                                       installedIRs, NicAsic2OfaBuff, 
                                       Ofa2NicAsicBuff, Installer2OfaBuff, 
                                       Ofa2InstallerBuff, TCAM, 
                                       controlMsgCounter, RecoveryStatus, 
                                       controllerSubmoduleFailNum, 
                                       switchOrdering, dependencyGraph, ir2sw, 
                                       controllerStateRC, IRStatusRC, 
                                       SwSuspensionStatusRC, IRQueueRC, 
                                       SetScheduledIRsRC, 
                                       FlagRCNIBEventHandlerFailover, 
                                       FlagRCSequencerFailover, RC_READY, 
                                       IRChangeForRC, TopoChangeForRC, 
                                       TEEventQueue, DAGEventQueue, DAGQueue, 
                                       DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                       idWorkerWorkingOnDAG, IRDoneSet, 
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
                                       IRStatusNIB, SwSuspensionStatusNIB, 
                                       IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                       NIBThreadID, RCThreadID, ingressPkt, 
                                       ingressIR, egressMsg, ofaInMsg, 
                                       ofaOutConfirmation, installerInIR, 
                                       statusMsg, notFailedSet, failedElem, 
                                       obj, failedSet, statusResolveMsg, 
                                       recoveredElem, value_, nextTrans_, 
                                       value_N, rowRemove_, IR2Remove_, 
                                       send_NIB_back_, stepOfFailure_, 
                                       IRIndex_, debug_, nextTrans, value, 
                                       rowRemove_N, IR2Remove, send_NIB_back, 
                                       stepOfFailure_N, IRIndex, debug_N, 
                                       NIBMsg_, isBootStrap_, sw_id, 
                                       transaction_, topoChangeEvent, 
                                       currSetDownSw, prev_dag_id, init, 
                                       nxtDAG, setRemovableIRs, currIR, 
                                       currIRInDAG, nxtDAGVertices, 
                                       setIRsInDAG, prev_dag, toBeScheduledIRs, 
                                       nextIR, transaction_c, stepOfFailure_c, 
                                       currDAG, IRSet, key, op1_, op2, debug, 
                                       transaction_O, IRQueueTmp, NIBMsg_O, 
                                       isBootStrap, localIRSet, NIBIRSet, 
                                       newIRSet, newIR, nextIRToSent, rowIndex, 
                                       rowRemove, stepOfFailure_co, 
                                       transaction_co, NIBMsg, op1, IRQueue, 
                                       op_ir_status_change_, removeIR, 
                                       monitoringEvent, setIRsToReset, resetIR, 
                                       stepOfFailure, transaction_con, 
                                       topo_change, irID, removedIR, msg, 
                                       op_ir_status_change, op_first_install, 
                                       transaction >>

RCFailoverProc(self) == RCFailoverResetStates(self) \/ RCReadNIB(self)
                           \/ RCBack2Normal(self)

RCSendReadTransaction(self) == /\ pc[self] = "RCSendReadTransaction"
                               /\ Assert(RC_READY = FALSE, 
                                         "Failure of assertion at line 1878, column 9.")
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ IF isRCFailed(self)
                                     THEN /\ FlagRCNIBEventHandlerFailover' = TRUE
                                          /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHandlerFailover"]
                                          /\ UNCHANGED << RC2NIB, transaction_ >>
                                     ELSE /\ isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID)
                                          /\ transaction_' = [transaction_ EXCEPT ![self] = [name |-> "SeqReadNIBStates"]]
                                          /\ RC2NIB' = RC2NIB \o <<transaction_'[self]>>
                                          /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHanderProc"]
                                          /\ UNCHANGED FlagRCNIBEventHandlerFailover
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstallOFC, 
                                               FirstInstallNIB, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, 
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
                                               switchOrdering, dependencyGraph, 
                                               ir2sw, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               SwSuspensionStatusRC, IRQueueRC, 
                                               SetScheduledIRsRC, 
                                               FlagRCSequencerFailover, 
                                               RC_READY, IRChangeForRC, 
                                               TopoChangeForRC, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, DAGID, 
                                               MaxDAGID, DAGState, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, IRDoneSet, 
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
                                               NIB2RC, X2NIB, OFC2NIB, 
                                               FlagNIBFailover, 
                                               FlagNIBRCEventhandlerFailover, 
                                               FlagNIBOFCEventhandlerFailover, 
                                               NIB_READY_FOR_RC, 
                                               NIB_READY_FOR_OFC, masterState, 
                                               controllerStateNIB, IRStatusNIB, 
                                               SwSuspensionStatusNIB, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               X2NIB_len, NIBThreadID, 
                                               RCThreadID, ingressPkt, 
                                               ingressIR, egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, value, 
                                               rowRemove_N, IR2Remove, 
                                               send_NIB_back, stepOfFailure_N, 
                                               IRIndex, debug_N, NIBMsg_, 
                                               isBootStrap_, sw_id, 
                                               topoChangeEvent, currSetDownSw, 
                                               prev_dag_id, init, nxtDAG, 
                                               setRemovableIRs, currIR, 
                                               currIRInDAG, nxtDAGVertices, 
                                               setIRsInDAG, prev_dag, 
                                               toBeScheduledIRs, nextIR, 
                                               transaction_c, stepOfFailure_c, 
                                               currDAG, IRSet, key, op1_, op2, 
                                               debug, transaction_O, 
                                               IRQueueTmp, NIBMsg_O, 
                                               isBootStrap, localIRSet, 
                                               NIBIRSet, newIRSet, newIR, 
                                               nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure_co, 
                                               transaction_co, NIBMsg, op1, 
                                               IRQueue, op_ir_status_change_, 
                                               removeIR, monitoringEvent, 
                                               setIRsToReset, resetIR, 
                                               stepOfFailure, transaction_con, 
                                               topo_change, irID, removedIR, 
                                               msg, op_ir_status_change, 
                                               op_first_install, transaction >>

RCNIBEventHanderProc(self) == /\ pc[self] = "RCNIBEventHanderProc"
                              /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                              /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF isRCFailed(self)
                                    THEN /\ FlagRCNIBEventHandlerFailover' = TRUE
                                         /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHandlerFailover"]
                                         /\ UNCHANGED << NIBUpdateForRC, 
                                                         IRStatusRC, 
                                                         SwSuspensionStatusRC, 
                                                         IRQueueRC, 
                                                         SetScheduledIRsRC, 
                                                         RC_READY, 
                                                         IRChangeForRC, 
                                                         TopoChangeForRC, 
                                                         TEEventQueue, NIB2RC, 
                                                         NIBMsg_, isBootStrap_, 
                                                         sw_id >>
                                    ELSE /\ NIB2RC # <<>>
                                         /\ NIBMsg_' = [NIBMsg_ EXCEPT ![self] = Head(NIB2RC)]
                                         /\ NIB2RC' = Tail(NIB2RC)
                                         /\ IF isBootStrap_[self] = TRUE
                                               THEN /\ IRStatusRC' = [x \in 1..MaxNumIRs |-> IR_NONE]
                                                    /\ IRQueueRC' = <<>>
                                                    /\ SetScheduledIRsRC' = [y \in SW |-> {}]
                                                    /\ IF SwSuspensionStatusRC # NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                          THEN /\ sw_id' = [sw_id EXCEPT ![self] = CHOOSE x \in DOMAIN SwSuspensionStatusRC: SwSuspensionStatusRC[x] # NIBMsg_'[self].value.SwSuspensionStatusNIB[x]]
                                                               /\ SwSuspensionStatusRC' = NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                               /\ TEEventQueue' = [TEEventQueue EXCEPT ![self[1]] = Append(TEEventQueue[self[1]], [type |-> TOPO_MOD,
                                                                                                                                 sw |-> sw_id'[self],
                                                                                                                                 state |-> SW_SUSPEND])]
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED << SwSuspensionStatusRC, 
                                                                               TEEventQueue, 
                                                                               sw_id >>
                                                    /\ NIBUpdateForRC' = TRUE
                                                    /\ isBootStrap_' = [isBootStrap_ EXCEPT ![self] = FALSE]
                                                    /\ Assert(RC_READY = FALSE, 
                                                              "Failure of assertion at line 1923, column 21.")
                                                    /\ RC_READY' = TRUE
                                                    /\ UNCHANGED << IRChangeForRC, 
                                                                    TopoChangeForRC >>
                                               ELSE /\ IF   IRStatusRC # NIBMsg_'[self].value.IRStatusNIB
                                                          \/ SwSuspensionStatusRC # NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                          THEN /\ IF IRStatusRC # NIBMsg_'[self].value.IRStatusNIB
                                                                     THEN /\ IRStatusRC' = [ir \in DOMAIN IRStatusRC |-> IF ir \in DOMAIN NIBMsg_'[self].value.IRStatusNIB
                                                                                                                            /\ IRStatusRC[ir]# NIBMsg_'[self].value.IRStatusNIB[ir]
                                                                                                                         THEN NIBMsg_'[self].value.IRStatusNIB[ir]
                                                                                                                         ELSE IRStatusRC[ir]]
                                                                          /\ SetScheduledIRsRC' =  [sw \in SW |-> IF SetScheduledIRsRC[sw] = {}
                                                                                                  THEN SetScheduledIRsRC[sw]
                                                                                                  ELSE {ir \in SetScheduledIRsRC[sw]:
                                                                                                          IRStatusRC'[ir] # IR_DONE}]
                                                                          /\ IRQueueRC' = SelectSeq(IRQueueRC, LAMBDA i: IRStatusRC'[i.IR] # IR_DONE)
                                                                          /\ IRChangeForRC' = TRUE
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED << IRStatusRC, 
                                                                                          IRQueueRC, 
                                                                                          SetScheduledIRsRC, 
                                                                                          IRChangeForRC >>
                                                               /\ IF SwSuspensionStatusRC # NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                                     THEN /\ sw_id' = [sw_id EXCEPT ![self] = CHOOSE x \in DOMAIN SwSuspensionStatusRC: SwSuspensionStatusRC[x] # NIBMsg_'[self].value.SwSuspensionStatusNIB[x]]
                                                                          /\ SwSuspensionStatusRC' = NIBMsg_'[self].value.SwSuspensionStatusNIB
                                                                          /\ TEEventQueue' = [TEEventQueue EXCEPT ![self[1]] = Append(TEEventQueue[self[1]], [type |-> TOPO_MOD,
                                                                                                                                            sw |-> sw_id'[self],
                                                                                                                                            state |-> SW_SUSPEND])]
                                                                          /\ TopoChangeForRC' = TRUE
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED << SwSuspensionStatusRC, 
                                                                                          TopoChangeForRC, 
                                                                                          TEEventQueue, 
                                                                                          sw_id >>
                                                               /\ NIBUpdateForRC' = TRUE
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED << NIBUpdateForRC, 
                                                                               IRStatusRC, 
                                                                               SwSuspensionStatusRC, 
                                                                               IRQueueRC, 
                                                                               SetScheduledIRsRC, 
                                                                               IRChangeForRC, 
                                                                               TopoChangeForRC, 
                                                                               TEEventQueue, 
                                                                               sw_id >>
                                                    /\ UNCHANGED << RC_READY, 
                                                                    isBootStrap_ >>
                                         /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHanderProc"]
                                         /\ UNCHANGED FlagRCNIBEventHandlerFailover
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstallOFC, FirstInstallNIB, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, 
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
                                              switchOrdering, dependencyGraph, 
                                              ir2sw, controllerStateRC, 
                                              FlagRCSequencerFailover, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, IRDoneSet, 
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
                                              controllerStateNIB, IRStatusNIB, 
                                              SwSuspensionStatusNIB, 
                                              IRQueueNIB, SetScheduledIRs, 
                                              X2NIB_len, NIBThreadID, 
                                              RCThreadID, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, value_, 
                                              nextTrans_, value_N, rowRemove_, 
                                              IR2Remove_, send_NIB_back_, 
                                              stepOfFailure_, IRIndex_, debug_, 
                                              nextTrans, value, rowRemove_N, 
                                              IR2Remove, send_NIB_back, 
                                              stepOfFailure_N, IRIndex, 
                                              debug_N, transaction_, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, 
                                              toBeScheduledIRs, nextIR, 
                                              transaction_c, stepOfFailure_c, 
                                              currDAG, IRSet, key, op1_, op2, 
                                              debug, transaction_O, IRQueueTmp, 
                                              NIBMsg_O, isBootStrap, 
                                              localIRSet, NIBIRSet, newIRSet, 
                                              newIR, nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure_co, 
                                              transaction_co, NIBMsg, op1, 
                                              IRQueue, op_ir_status_change_, 
                                              removeIR, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, transaction_con, 
                                              topo_change, irID, removedIR, 
                                              msg, op_ir_status_change, 
                                              op_first_install, transaction >>

RCNIBEventHandlerFailover(self) == /\ pc[self] = "RCNIBEventHandlerFailover"
                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                   /\ controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = NotFailed /\
                                            controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
                                   /\ isBootStrap_' = [isBootStrap_ EXCEPT ![self] = FALSE]
                                   /\ pc' = [pc EXCEPT ![self] = "RCNIBEventHanderProc"]
                                   /\ UNCHANGED << switchLock, controllerLock, 
                                                   FirstInstallOFC, 
                                                   FirstInstallNIB, 
                                                   sw_fail_ordering_var, 
                                                   ContProcSet, SwProcSet, 
                                                   irTypeMapping, 
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
                                                   dependencyGraph, ir2sw, 
                                                   NIBUpdateForRC, 
                                                   controllerStateRC, 
                                                   IRStatusRC, 
                                                   SwSuspensionStatusRC, 
                                                   IRQueueRC, 
                                                   SetScheduledIRsRC, 
                                                   FlagRCNIBEventHandlerFailover, 
                                                   FlagRCSequencerFailover, 
                                                   RC_READY, IRChangeForRC, 
                                                   TopoChangeForRC, 
                                                   TEEventQueue, DAGEventQueue, 
                                                   DAGQueue, DAGID, MaxDAGID, 
                                                   DAGState, nxtRCIRID, 
                                                   idWorkerWorkingOnDAG, 
                                                   IRDoneSet, 
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
                                                   IRStatusNIB, 
                                                   SwSuspensionStatusNIB, 
                                                   IRQueueNIB, SetScheduledIRs, 
                                                   X2NIB_len, NIBThreadID, 
                                                   RCThreadID, ingressPkt, 
                                                   ingressIR, egressMsg, 
                                                   ofaInMsg, 
                                                   ofaOutConfirmation, 
                                                   installerInIR, statusMsg, 
                                                   notFailedSet, failedElem, 
                                                   obj, failedSet, 
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
                                                   debug_N, NIBMsg_, sw_id, 
                                                   transaction_, 
                                                   topoChangeEvent, 
                                                   currSetDownSw, prev_dag_id, 
                                                   init, nxtDAG, 
                                                   setRemovableIRs, currIR, 
                                                   currIRInDAG, nxtDAGVertices, 
                                                   setIRsInDAG, prev_dag, 
                                                   toBeScheduledIRs, nextIR, 
                                                   transaction_c, 
                                                   stepOfFailure_c, currDAG, 
                                                   IRSet, key, op1_, op2, 
                                                   debug, transaction_O, 
                                                   IRQueueTmp, NIBMsg_O, 
                                                   isBootStrap, localIRSet, 
                                                   NIBIRSet, newIRSet, newIR, 
                                                   nextIRToSent, rowIndex, 
                                                   rowRemove, stepOfFailure_co, 
                                                   transaction_co, NIBMsg, op1, 
                                                   IRQueue, 
                                                   op_ir_status_change_, 
                                                   removeIR, monitoringEvent, 
                                                   setIRsToReset, resetIR, 
                                                   stepOfFailure, 
                                                   transaction_con, 
                                                   topo_change, irID, 
                                                   removedIR, msg, 
                                                   op_ir_status_change, 
                                                   op_first_install, 
                                                   transaction >>

RCNIBEventHandler(self) == RCSendReadTransaction(self)
                              \/ RCNIBEventHanderProc(self)
                              \/ RCNIBEventHandlerFailover(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ controllerIsMaster(self[1])
                          /\ moduleIsUp(self)
                          /\ RC_READY = TRUE
                          /\ init[self] = 1 \/ TEEventQueue[self[1]] # <<>>
                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ controllerLock' = self
                          /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                          /\ UNCHANGED << switchLock, FirstInstallOFC, 
                                          FirstInstallNIB, 
                                          sw_fail_ordering_var, ContProcSet, 
                                          SwProcSet, irTypeMapping, 
                                          swSeqChangedStatus, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Installer2OfaBuff, Ofa2InstallerBuff, 
                                          TCAM, controlMsgCounter, 
                                          RecoveryStatus, 
                                          controllerSubmoduleFailNum, 
                                          controllerSubmoduleFailStat, 
                                          switchOrdering, dependencyGraph, 
                                          ir2sw, NIBUpdateForRC, 
                                          controllerStateRC, IRStatusRC, 
                                          SwSuspensionStatusRC, IRQueueRC, 
                                          SetScheduledIRsRC, 
                                          FlagRCNIBEventHandlerFailover, 
                                          FlagRCSequencerFailover, RC_READY, 
                                          IRChangeForRC, TopoChangeForRC, 
                                          TEEventQueue, DAGEventQueue, 
                                          DAGQueue, DAGID, MaxDAGID, DAGState, 
                                          nxtRCIRID, idWorkerWorkingOnDAG, 
                                          IRDoneSet, idThreadWorkingOnIR, 
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
                                          IRStatusNIB, SwSuspensionStatusNIB, 
                                          IRQueueNIB, SetScheduledIRs, 
                                          X2NIB_len, NIBThreadID, RCThreadID, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, ofaOutConfirmation, 
                                          installerInIR, statusMsg, 
                                          notFailedSet, failedElem, obj, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem, value_, nextTrans_, 
                                          value_N, rowRemove_, IR2Remove_, 
                                          send_NIB_back_, stepOfFailure_, 
                                          IRIndex_, debug_, nextTrans, value, 
                                          rowRemove_N, IR2Remove, 
                                          send_NIB_back, stepOfFailure_N, 
                                          IRIndex, debug_N, NIBMsg_, 
                                          isBootStrap_, sw_id, transaction_, 
                                          topoChangeEvent, currSetDownSw, 
                                          prev_dag_id, init, nxtDAG, 
                                          setRemovableIRs, currIR, currIRInDAG, 
                                          nxtDAGVertices, setIRsInDAG, 
                                          prev_dag, toBeScheduledIRs, nextIR, 
                                          transaction_c, stepOfFailure_c, 
                                          currDAG, IRSet, key, op1_, op2, 
                                          debug, transaction_O, IRQueueTmp, 
                                          NIBMsg_O, isBootStrap, localIRSet, 
                                          NIBIRSet, newIRSet, newIR, 
                                          nextIRToSent, rowIndex, rowRemove, 
                                          stepOfFailure_co, transaction_co, 
                                          NIBMsg, op1, IRQueue, 
                                          op_ir_status_change_, removeIR, 
                                          monitoringEvent, setIRsToReset, 
                                          resetIR, stepOfFailure, 
                                          transaction_con, topo_change, irID, 
                                          removedIR, msg, op_ir_status_change, 
                                          op_first_install, transaction >>

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF TEEventQueue[self[1]] # <<>>
                                           THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                /\ topoChangeEvent' = [topoChangeEvent EXCEPT ![self] = Head(TEEventQueue[self[1]])]
                                                /\ Assert(topoChangeEvent'[self].type \in {TOPO_MOD}, 
                                                          "Failure of assertion at line 1985, column 17.")
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
                                     /\ UNCHANGED << switchLock, 
                                                     FirstInstallOFC, 
                                                     FirstInstallNIB, 
                                                     sw_fail_ordering_var, 
                                                     ContProcSet, SwProcSet, 
                                                     irTypeMapping, 
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
                                                     dependencyGraph, ir2sw, 
                                                     NIBUpdateForRC, 
                                                     controllerStateRC, 
                                                     IRStatusRC, 
                                                     SwSuspensionStatusRC, 
                                                     IRQueueRC, 
                                                     SetScheduledIRsRC, 
                                                     FlagRCNIBEventHandlerFailover, 
                                                     FlagRCSequencerFailover, 
                                                     RC_READY, IRChangeForRC, 
                                                     TopoChangeForRC, 
                                                     DAGEventQueue, DAGQueue, 
                                                     DAGID, MaxDAGID, DAGState, 
                                                     nxtRCIRID, 
                                                     idWorkerWorkingOnDAG, 
                                                     IRDoneSet, 
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
                                                     IRStatusNIB, 
                                                     SwSuspensionStatusNIB, 
                                                     IRQueueNIB, 
                                                     SetScheduledIRs, 
                                                     X2NIB_len, NIBThreadID, 
                                                     RCThreadID, ingressPkt, 
                                                     ingressIR, egressMsg, 
                                                     ofaInMsg, 
                                                     ofaOutConfirmation, 
                                                     installerInIR, statusMsg, 
                                                     notFailedSet, failedElem, 
                                                     obj, failedSet, 
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
                                                     debug_N, NIBMsg_, 
                                                     isBootStrap_, sw_id, 
                                                     transaction_, prev_dag_id, 
                                                     init, nxtDAG, 
                                                     setRemovableIRs, currIR, 
                                                     currIRInDAG, 
                                                     nxtDAGVertices, 
                                                     setIRsInDAG, prev_dag, 
                                                     toBeScheduledIRs, nextIR, 
                                                     transaction_c, 
                                                     stepOfFailure_c, currDAG, 
                                                     IRSet, key, op1_, op2, 
                                                     debug, transaction_O, 
                                                     IRQueueTmp, NIBMsg_O, 
                                                     isBootStrap, localIRSet, 
                                                     NIBIRSet, newIRSet, newIR, 
                                                     nextIRToSent, rowIndex, 
                                                     rowRemove, 
                                                     stepOfFailure_co, 
                                                     transaction_co, NIBMsg, 
                                                     op1, IRQueue, 
                                                     op_ir_status_change_, 
                                                     removeIR, monitoringEvent, 
                                                     setIRsToReset, resetIR, 
                                                     stepOfFailure, 
                                                     transaction_con, 
                                                     topo_change, irID, 
                                                     removedIR, msg, 
                                                     op_ir_status_change, 
                                                     op_first_install, 
                                                     transaction >>

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
                                                                 /\ pc' = [pc EXCEPT ![self] = "TEWaitSequencerTerminate"]
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
                                                           FirstInstallOFC, 
                                                           FirstInstallNIB, 
                                                           sw_fail_ordering_var, 
                                                           ContProcSet, 
                                                           SwProcSet, 
                                                           irTypeMapping, 
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
                                                           dependencyGraph, 
                                                           ir2sw, 
                                                           NIBUpdateForRC, 
                                                           controllerStateRC, 
                                                           IRStatusRC, 
                                                           SwSuspensionStatusRC, 
                                                           IRQueueRC, 
                                                           SetScheduledIRsRC, 
                                                           FlagRCNIBEventHandlerFailover, 
                                                           FlagRCSequencerFailover, 
                                                           RC_READY, 
                                                           IRChangeForRC, 
                                                           TopoChangeForRC, 
                                                           TEEventQueue, 
                                                           DAGEventQueue, 
                                                           DAGQueue, MaxDAGID, 
                                                           nxtRCIRID, 
                                                           idWorkerWorkingOnDAG, 
                                                           IRDoneSet, 
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
                                                           IRStatusNIB, 
                                                           SwSuspensionStatusNIB, 
                                                           IRQueueNIB, 
                                                           SetScheduledIRs, 
                                                           X2NIB_len, 
                                                           NIBThreadID, 
                                                           RCThreadID, 
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
                                                           IRIndex, debug_N, 
                                                           NIBMsg_, 
                                                           isBootStrap_, sw_id, 
                                                           transaction_, 
                                                           topoChangeEvent, 
                                                           currSetDownSw, 
                                                           setRemovableIRs, 
                                                           currIR, currIRInDAG, 
                                                           setIRsInDAG, 
                                                           toBeScheduledIRs, 
                                                           nextIR, 
                                                           transaction_c, 
                                                           stepOfFailure_c, 
                                                           currDAG, IRSet, key, 
                                                           op1_, op2, debug, 
                                                           transaction_O, 
                                                           IRQueueTmp, 
                                                           NIBMsg_O, 
                                                           isBootStrap, 
                                                           localIRSet, 
                                                           NIBIRSet, newIRSet, 
                                                           newIR, nextIRToSent, 
                                                           rowIndex, rowRemove, 
                                                           stepOfFailure_co, 
                                                           transaction_co, 
                                                           NIBMsg, op1, 
                                                           IRQueue, 
                                                           op_ir_status_change_, 
                                                           removeIR, 
                                                           monitoringEvent, 
                                                           setIRsToReset, 
                                                           resetIR, 
                                                           stepOfFailure, 
                                                           transaction_con, 
                                                           topo_change, irID, 
                                                           removedIR, msg, 
                                                           op_ir_status_change, 
                                                           op_first_install, 
                                                           transaction >>

TEWaitSequencerTerminate(self) == /\ pc[self] = "TEWaitSequencerTerminate"
                                  /\ IF idWorkerWorkingOnDAG[prev_dag_id[self]] # DAG_UNLOCK
                                        THEN /\ idWorkerWorkingOnDAG[prev_dag_id[self]] = DAG_UNLOCK
                                             /\ DAGState' = [DAGState EXCEPT ![prev_dag_id[self]] = DAG_NONE]
                                        ELSE /\ DAGState' = [DAGState EXCEPT ![prev_dag_id[self]] = DAG_NONE]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstallOFC, 
                                                  FirstInstallNIB, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, 
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
                                                  dependencyGraph, ir2sw, 
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, 
                                                  SwSuspensionStatusRC, 
                                                  IRQueueRC, SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, IRChangeForRC, 
                                                  TopoChangeForRC, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, DAGID, MaxDAGID, 
                                                  nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
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
                                                  IRStatusNIB, 
                                                  SwSuspensionStatusNIB, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
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
                                                  debug_N, NIBMsg_, 
                                                  isBootStrap_, sw_id, 
                                                  transaction_, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  toBeScheduledIRs, nextIR, 
                                                  transaction_c, 
                                                  stepOfFailure_c, currDAG, 
                                                  IRSet, key, op1_, op2, debug, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  newIRSet, newIR, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_co, 
                                                  transaction_co, NIBMsg, op1, 
                                                  IRQueue, 
                                                  op_ir_status_change_, 
                                                  removeIR, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, 
                                                  transaction_con, topo_change, 
                                                  irID, removedIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

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
                                                                FirstInstallOFC, 
                                                                FirstInstallNIB, 
                                                                sw_fail_ordering_var, 
                                                                ContProcSet, 
                                                                SwProcSet, 
                                                                irTypeMapping, 
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
                                                                dependencyGraph, 
                                                                ir2sw, 
                                                                NIBUpdateForRC, 
                                                                controllerStateRC, 
                                                                IRStatusRC, 
                                                                SwSuspensionStatusRC, 
                                                                IRQueueRC, 
                                                                SetScheduledIRsRC, 
                                                                FlagRCNIBEventHandlerFailover, 
                                                                FlagRCSequencerFailover, 
                                                                RC_READY, 
                                                                IRChangeForRC, 
                                                                TopoChangeForRC, 
                                                                TEEventQueue, 
                                                                DAGEventQueue, 
                                                                DAGQueue, 
                                                                DAGID, 
                                                                MaxDAGID, 
                                                                DAGState, 
                                                                nxtRCIRID, 
                                                                idWorkerWorkingOnDAG, 
                                                                IRDoneSet, 
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
                                                                OFC_READY, 
                                                                NIB2OFC, 
                                                                NIB2RC, X2NIB, 
                                                                OFC2NIB, 
                                                                RC2NIB, 
                                                                FlagNIBFailover, 
                                                                FlagNIBRCEventhandlerFailover, 
                                                                FlagNIBOFCEventhandlerFailover, 
                                                                NIB_READY_FOR_RC, 
                                                                NIB_READY_FOR_OFC, 
                                                                masterState, 
                                                                controllerStateNIB, 
                                                                IRStatusNIB, 
                                                                SwSuspensionStatusNIB, 
                                                                IRQueueNIB, 
                                                                SetScheduledIRs, 
                                                                X2NIB_len, 
                                                                NIBThreadID, 
                                                                RCThreadID, 
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
                                                                value_, 
                                                                nextTrans_, 
                                                                value_N, 
                                                                rowRemove_, 
                                                                IR2Remove_, 
                                                                send_NIB_back_, 
                                                                stepOfFailure_, 
                                                                IRIndex_, 
                                                                debug_, 
                                                                nextTrans, 
                                                                value, 
                                                                rowRemove_N, 
                                                                IR2Remove, 
                                                                send_NIB_back, 
                                                                stepOfFailure_N, 
                                                                IRIndex, 
                                                                debug_N, 
                                                                NIBMsg_, 
                                                                isBootStrap_, 
                                                                sw_id, 
                                                                transaction_, 
                                                                topoChangeEvent, 
                                                                currSetDownSw, 
                                                                init, nxtDAG, 
                                                                currIR, 
                                                                currIRInDAG, 
                                                                nxtDAGVertices, 
                                                                setIRsInDAG, 
                                                                toBeScheduledIRs, 
                                                                nextIR, 
                                                                transaction_c, 
                                                                stepOfFailure_c, 
                                                                currDAG, IRSet, 
                                                                key, op1_, op2, 
                                                                debug, 
                                                                transaction_O, 
                                                                IRQueueTmp, 
                                                                NIBMsg_O, 
                                                                isBootStrap, 
                                                                localIRSet, 
                                                                NIBIRSet, 
                                                                newIRSet, 
                                                                newIR, 
                                                                nextIRToSent, 
                                                                rowIndex, 
                                                                rowRemove, 
                                                                stepOfFailure_co, 
                                                                transaction_co, 
                                                                NIBMsg, op1, 
                                                                IRQueue, 
                                                                op_ir_status_change_, 
                                                                removeIR, 
                                                                monitoringEvent, 
                                                                setIRsToReset, 
                                                                resetIR, 
                                                                stepOfFailure, 
                                                                transaction_con, 
                                                                topo_change, 
                                                                irID, 
                                                                removedIR, msg, 
                                                                op_ir_status_change, 
                                                                op_first_install, 
                                                                transaction >>

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF setRemovableIRs[self] # {}
                                                THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = self
                                                     /\ currIR' = [currIR EXCEPT ![self] = CHOOSE x \in setRemovableIRs[self]: TRUE]
                                                     /\ setRemovableIRs' = [setRemovableIRs EXCEPT ![self] = setRemovableIRs[self] \ {currIR'[self]}]
                                                     /\ IRStatusRC' = IRStatusRC @@ (nxtRCIRID :> IR_NONE)
                                                     /\ IRStatusNIB' = IRStatusNIB @@ (nxtRCIRID :> IR_NONE)
                                                     /\ irTypeMapping' = irTypeMapping @@ (nxtRCIRID :> [type |-> DELETE_FLOW, flow |-> IR2FLOW[currIR'[self]]])
                                                     /\ ir2sw' = ir2sw @@ (nxtRCIRID :> ir2sw[currIR'[self]])
                                                     /\ nxtDAG' = [nxtDAG EXCEPT ![self].dag.v = nxtDAG[self].dag.v \cup {nxtRCIRID}]
                                                     /\ setIRsInDAG' = [setIRsInDAG EXCEPT ![self] = getSetIRsForSwitchInDAG(ir2sw'[currIR'[self]], nxtDAGVertices[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEAddEdge"]
                                                ELSE /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]
                                                     /\ UNCHANGED << irTypeMapping, 
                                                                     ir2sw, 
                                                                     IRStatusRC, 
                                                                     IRStatusNIB, 
                                                                     nxtDAG, 
                                                                     setRemovableIRs, 
                                                                     currIR, 
                                                                     setIRsInDAG >>
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
                                                          RecoveryStatus, 
                                                          controllerSubmoduleFailNum, 
                                                          controllerSubmoduleFailStat, 
                                                          switchOrdering, 
                                                          dependencyGraph, 
                                                          NIBUpdateForRC, 
                                                          controllerStateRC, 
                                                          SwSuspensionStatusRC, 
                                                          IRQueueRC, 
                                                          SetScheduledIRsRC, 
                                                          FlagRCNIBEventHandlerFailover, 
                                                          FlagRCSequencerFailover, 
                                                          RC_READY, 
                                                          IRChangeForRC, 
                                                          TopoChangeForRC, 
                                                          TEEventQueue, 
                                                          DAGEventQueue, 
                                                          DAGQueue, DAGID, 
                                                          MaxDAGID, DAGState, 
                                                          nxtRCIRID, 
                                                          idWorkerWorkingOnDAG, 
                                                          IRDoneSet, 
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
                                                          SwSuspensionStatusNIB, 
                                                          IRQueueNIB, 
                                                          SetScheduledIRs, 
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
                                                          failedElem, obj, 
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
                                                          IRIndex, debug_N, 
                                                          NIBMsg_, 
                                                          isBootStrap_, sw_id, 
                                                          transaction_, 
                                                          topoChangeEvent, 
                                                          currSetDownSw, 
                                                          prev_dag_id, init, 
                                                          currIRInDAG, 
                                                          nxtDAGVertices, 
                                                          prev_dag, 
                                                          toBeScheduledIRs, 
                                                          nextIR, 
                                                          transaction_c, 
                                                          stepOfFailure_c, 
                                                          currDAG, IRSet, key, 
                                                          op1_, op2, debug, 
                                                          transaction_O, 
                                                          IRQueueTmp, NIBMsg_O, 
                                                          isBootStrap, 
                                                          localIRSet, NIBIRSet, 
                                                          newIRSet, newIR, 
                                                          nextIRToSent, 
                                                          rowIndex, rowRemove, 
                                                          stepOfFailure_co, 
                                                          transaction_co, 
                                                          NIBMsg, op1, IRQueue, 
                                                          op_ir_status_change_, 
                                                          removeIR, 
                                                          monitoringEvent, 
                                                          setIRsToReset, 
                                                          resetIR, 
                                                          stepOfFailure, 
                                                          transaction_con, 
                                                          topo_change, irID, 
                                                          removedIR, msg, 
                                                          op_ir_status_change, 
                                                          op_first_install, 
                                                          transaction >>

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
                             /\ UNCHANGED << switchLock, FirstInstallOFC, 
                                             FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, 
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
                                             switchOrdering, dependencyGraph, 
                                             ir2sw, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             SwSuspensionStatusRC, IRQueueRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             IRChangeForRC, TopoChangeForRC, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, DAGID, MaxDAGID, 
                                             DAGState, idWorkerWorkingOnDAG, 
                                             IRDoneSet, idThreadWorkingOnIR, 
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
                                             controllerStateNIB, IRStatusNIB, 
                                             SwSuspensionStatusNIB, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, obj, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, value_, nextTrans_, 
                                             value_N, rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug_N, NIBMsg_, 
                                             isBootStrap_, sw_id, transaction_, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, 
                                             setRemovableIRs, currIR, 
                                             nxtDAGVertices, prev_dag, 
                                             toBeScheduledIRs, nextIR, 
                                             transaction_c, stepOfFailure_c, 
                                             currDAG, IRSet, key, op1_, op2, 
                                             debug, transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, newIRSet, newIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_co, transaction_co, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, 
                                             transaction_con, topo_change, 
                                             irID, removedIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG[self].id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' = [DAGEventQueue EXCEPT ![self[1]] = Append(DAGEventQueue[self[1]], [type |-> DAG_NEW, dag_obj |-> nxtDAG[self]])]
                                  /\ DAGQueue' = [DAGQueue EXCEPT ![self[1]] = Append(DAGQueue[self[1]], nxtDAG[self])]
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]
                                  /\ UNCHANGED << switchLock, FirstInstallOFC, 
                                                  FirstInstallNIB, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, 
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
                                                  dependencyGraph, ir2sw, 
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, 
                                                  SwSuspensionStatusRC, 
                                                  IRQueueRC, SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, IRChangeForRC, 
                                                  TopoChangeForRC, 
                                                  TEEventQueue, DAGID, 
                                                  MaxDAGID, nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
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
                                                  IRStatusNIB, 
                                                  SwSuspensionStatusNIB, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
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
                                                  debug_N, NIBMsg_, 
                                                  isBootStrap_, sw_id, 
                                                  transaction_, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  toBeScheduledIRs, nextIR, 
                                                  transaction_c, 
                                                  stepOfFailure_c, currDAG, 
                                                  IRSet, key, op1_, op2, debug, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  newIRSet, newIR, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_co, 
                                                  transaction_co, NIBMsg, op1, 
                                                  IRQueue, 
                                                  op_ir_status_change_, 
                                                  removeIR, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, 
                                                  transaction_con, topo_change, 
                                                  irID, removedIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ TEWaitSequencerTerminate(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ControllerTEAddEdge(self)
                                         \/ ControllerTESubmitNewDAG(self)

RCWorkerSeqProc(self) == /\ pc[self] = "RCWorkerSeqProc"
                         /\ controllerIsMaster(self[1])
                         /\ moduleIsUp(self)
                         /\ RC_READY = TRUE
                         /\ DAGQueue[self[1]] # <<>>
                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                         /\ currDAG' = [currDAG EXCEPT ![self] = Head(DAGQueue[self[1]])]
                         /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG'[self].id] = self[2]]
                         /\ NIBUpdateForRC' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "RCWorkerSeqScheduleDAG"]
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstallOFC, FirstInstallNIB, 
                                         sw_fail_ordering_var, ContProcSet, 
                                         SwProcSet, irTypeMapping, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         ir2sw, controllerStateRC, IRStatusRC, 
                                         SwSuspensionStatusRC, IRQueueRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         IRChangeForRC, TopoChangeForRC, 
                                         TEEventQueue, DAGEventQueue, DAGQueue, 
                                         DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                         IRDoneSet, idThreadWorkingOnIR, 
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
                                         IRStatusNIB, SwSuspensionStatusNIB, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, obj, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug_N, 
                                         NIBMsg_, isBootStrap_, sw_id, 
                                         transaction_, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, 
                                         toBeScheduledIRs, nextIR, 
                                         transaction_c, stepOfFailure_c, IRSet, 
                                         key, op1_, op2, debug, transaction_O, 
                                         IRQueueTmp, NIBMsg_O, isBootStrap, 
                                         localIRSet, NIBIRSet, newIRSet, newIR, 
                                         nextIRToSent, rowIndex, rowRemove, 
                                         stepOfFailure_co, transaction_co, 
                                         NIBMsg, op1, IRQueue, 
                                         op_ir_status_change_, removeIR, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, 
                                         transaction_con, topo_change, irID, 
                                         removedIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

RCWorkerSeqScheduleDAG(self) == /\ pc[self] = "RCWorkerSeqScheduleDAG"
                                /\ IF ~allIRsInDAGInstalled(self[1], currDAG[self].dag) /\ ~isDAGStale(currDAG[self].id)
                                      THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                           /\ IF isRCFailed(self)
                                                 THEN /\ FlagRCSequencerFailover' = TRUE
                                                      /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                                                      /\ UNCHANGED << NIBUpdateForRC, 
                                                                      toBeScheduledIRs >>
                                                 ELSE /\ NIBUpdateForRC
                                                      /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = getSetIRsCanBeScheduledNextRC(currDAG[self].dag)]
                                                      /\ IF toBeScheduledIRs'[self] = {}
                                                            THEN /\ IF TopoChangeForRC
                                                                       THEN /\ pc' = [pc EXCEPT ![self] = "RemoveDAGFromQueue"]
                                                                            /\ UNCHANGED NIBUpdateForRC
                                                                       ELSE /\ NIBUpdateForRC' = FALSE
                                                                            /\ pc' = [pc EXCEPT ![self] = "RCWorkerSeqScheduleDAG"]
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                                                 /\ UNCHANGED NIBUpdateForRC
                                                      /\ UNCHANGED FlagRCSequencerFailover
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDAGFromQueue"]
                                           /\ UNCHANGED << NIBUpdateForRC, 
                                                           FlagRCSequencerFailover, 
                                                           toBeScheduledIRs >>
                                /\ UNCHANGED << switchLock, controllerLock, 
                                                FirstInstallOFC, 
                                                FirstInstallNIB, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, 
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
                                                dependencyGraph, ir2sw, 
                                                controllerStateRC, IRStatusRC, 
                                                SwSuspensionStatusRC, 
                                                IRQueueRC, SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                RC_READY, IRChangeForRC, 
                                                TopoChangeForRC, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
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
                                                controllerStateNIB, 
                                                IRStatusNIB, 
                                                SwSuspensionStatusNIB, 
                                                IRQueueNIB, SetScheduledIRs, 
                                                X2NIB_len, NIBThreadID, 
                                                RCThreadID, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug_N, NIBMsg_, 
                                                isBootStrap_, sw_id, 
                                                transaction_, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, nxtDAG, setRemovableIRs, 
                                                currIR, currIRInDAG, 
                                                nxtDAGVertices, setIRsInDAG, 
                                                prev_dag, nextIR, 
                                                transaction_c, stepOfFailure_c, 
                                                currDAG, IRSet, key, op1_, op2, 
                                                debug, transaction_O, 
                                                IRQueueTmp, NIBMsg_O, 
                                                isBootStrap, localIRSet, 
                                                NIBIRSet, newIRSet, newIR, 
                                                nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_co, 
                                                transaction_co, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, transaction_con, 
                                                topo_change, irID, removedIR, 
                                                msg, op_ir_status_change, 
                                                op_first_install, transaction >>

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF isRCFailed(self)
                                  THEN /\ FlagRCSequencerFailover' = TRUE
                                       /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                                       /\ UNCHANGED << IRQueueRC, 
                                                       SetScheduledIRsRC, 
                                                       toBeScheduledIRs, 
                                                       nextIR >>
                                  ELSE /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in toBeScheduledIRs[self]: TRUE]
                                       /\ SetScheduledIRsRC' = [SetScheduledIRsRC EXCEPT ![ir2sw[nextIR'[self]]] = SetScheduledIRsRC[ir2sw[nextIR'[self]]] \cup {nextIR'[self]}]
                                       /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = toBeScheduledIRs[self]\{nextIR'[self]}]
                                       /\ IRQueueRC' = Append(IRQueueRC, [IR |-> nextIR'[self], tag |-> NO_TAG])
                                       /\ pc' = [pc EXCEPT ![self] = "AddDeleteIRDoneSet"]
                                       /\ UNCHANGED FlagRCSequencerFailover
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            RC_READY, IRChangeForRC, 
                                            TopoChangeForRC, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, DAGID, 
                                            MaxDAGID, DAGState, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, IRDoneSet, 
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
                                            controllerStateNIB, IRStatusNIB, 
                                            SwSuspensionStatusNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, IRSet, key, op1_, op2, 
                                            debug, transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_co, transaction_co, 
                                            NIBMsg, op1, IRQueue, 
                                            op_ir_status_change_, removeIR, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, 
                                            transaction_con, topo_change, irID, 
                                            removedIR, msg, 
                                            op_ir_status_change, 
                                            op_first_install, transaction >>

AddDeleteIRDoneSet(self) == /\ pc[self] = "AddDeleteIRDoneSet"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF irTypeMapping[nextIR[self]].type = INSTALL_FLOW
                                  THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \cup {nextIR[self]}]
                                  ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR[self]].flow, INSTALLED_SUCCESSFULLY)}]
                            /\ pc' = [pc EXCEPT ![self] = "RCSendIR2NIB"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, IRQueueRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            IRChangeForRC, TopoChangeForRC, 
                                            TEEventQueue, DAGEventQueue, 
                                            DAGQueue, DAGID, MaxDAGID, 
                                            DAGState, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, 
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
                                            controllerStateNIB, IRStatusNIB, 
                                            SwSuspensionStatusNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            toBeScheduledIRs, nextIR, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, IRSet, key, op1_, op2, 
                                            debug, transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_co, transaction_co, 
                                            NIBMsg, op1, IRQueue, 
                                            op_ir_status_change_, removeIR, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, 
                                            transaction_con, topo_change, irID, 
                                            removedIR, msg, 
                                            op_ir_status_change, 
                                            op_first_install, transaction >>

RCSendIR2NIB(self) == /\ pc[self] = "RCSendIR2NIB"
                      /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                      /\ IF isRCFailed(self)
                            THEN /\ FlagRCSequencerFailover' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "RCSequencerFailover"]
                                 /\ UNCHANGED << RC2NIB, transaction_c, op1_ >>
                            ELSE /\ isNIBUp(NIBThreadID) \/ isNIBFailed(NIBThreadID)
                                 /\ op1_' = [op1_ EXCEPT ![self] = [table |-> NIBT_IR_QUEUE, key |-> NULL, value |-> [IR |-> nextIR[self], tag |-> NO_TAG]]]
                                 /\ transaction_c' = [transaction_c EXCEPT ![self] = [name |-> "RCScheduleIRInOneStep", ops |-> <<op1_'[self]>>]]
                                 /\ RC2NIB' = RC2NIB \o <<transaction_c'[self]>>
                                 /\ IF toBeScheduledIRs[self] = {} \/ isDAGStale(currDAG[self].id)
                                       THEN /\ pc' = [pc EXCEPT ![self] = "RCWorkerSeqScheduleDAG"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                 /\ UNCHANGED FlagRCSequencerFailover
                      /\ UNCHANGED << switchLock, controllerLock, 
                                      FirstInstallOFC, FirstInstallNIB, 
                                      sw_fail_ordering_var, ContProcSet, 
                                      SwProcSet, irTypeMapping, 
                                      swSeqChangedStatus, controller2Switch, 
                                      switch2Controller, switchStatus, 
                                      installedIRs, NicAsic2OfaBuff, 
                                      Ofa2NicAsicBuff, Installer2OfaBuff, 
                                      Ofa2InstallerBuff, TCAM, 
                                      controlMsgCounter, RecoveryStatus, 
                                      controllerSubmoduleFailNum, 
                                      controllerSubmoduleFailStat, 
                                      switchOrdering, dependencyGraph, ir2sw, 
                                      NIBUpdateForRC, controllerStateRC, 
                                      IRStatusRC, SwSuspensionStatusRC, 
                                      IRQueueRC, SetScheduledIRsRC, 
                                      FlagRCNIBEventHandlerFailover, RC_READY, 
                                      IRChangeForRC, TopoChangeForRC, 
                                      TEEventQueue, DAGEventQueue, DAGQueue, 
                                      DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                      idWorkerWorkingOnDAG, IRDoneSet, 
                                      idThreadWorkingOnIR, workerThreadRanking, 
                                      controllerStateOFC, IRStatusOFC, 
                                      IRQueueOFC, SwSuspensionStatusOFC, 
                                      SetScheduledIRsOFC, 
                                      FlagOFCWorkerFailover, 
                                      FlagOFCMonitorFailover, 
                                      FlagOFCNIBEventHandlerFailover, 
                                      OFCThreadID, OFC_READY, NIB2OFC, NIB2RC, 
                                      X2NIB, OFC2NIB, FlagNIBFailover, 
                                      FlagNIBRCEventhandlerFailover, 
                                      FlagNIBOFCEventhandlerFailover, 
                                      NIB_READY_FOR_RC, NIB_READY_FOR_OFC, 
                                      masterState, controllerStateNIB, 
                                      IRStatusNIB, SwSuspensionStatusNIB, 
                                      IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                      NIBThreadID, RCThreadID, ingressPkt, 
                                      ingressIR, egressMsg, ofaInMsg, 
                                      ofaOutConfirmation, installerInIR, 
                                      statusMsg, notFailedSet, failedElem, obj, 
                                      failedSet, statusResolveMsg, 
                                      recoveredElem, value_, nextTrans_, 
                                      value_N, rowRemove_, IR2Remove_, 
                                      send_NIB_back_, stepOfFailure_, IRIndex_, 
                                      debug_, nextTrans, value, rowRemove_N, 
                                      IR2Remove, send_NIB_back, 
                                      stepOfFailure_N, IRIndex, debug_N, 
                                      NIBMsg_, isBootStrap_, sw_id, 
                                      transaction_, topoChangeEvent, 
                                      currSetDownSw, prev_dag_id, init, nxtDAG, 
                                      setRemovableIRs, currIR, currIRInDAG, 
                                      nxtDAGVertices, setIRsInDAG, prev_dag, 
                                      toBeScheduledIRs, nextIR, 
                                      stepOfFailure_c, currDAG, IRSet, key, 
                                      op2, debug, transaction_O, IRQueueTmp, 
                                      NIBMsg_O, isBootStrap, localIRSet, 
                                      NIBIRSet, newIRSet, newIR, nextIRToSent, 
                                      rowIndex, rowRemove, stepOfFailure_co, 
                                      transaction_co, NIBMsg, op1, IRQueue, 
                                      op_ir_status_change_, removeIR, 
                                      monitoringEvent, setIRsToReset, resetIR, 
                                      stepOfFailure, transaction_con, 
                                      topo_change, irID, removedIR, msg, 
                                      op_ir_status_change, op_first_install, 
                                      transaction >>

RemoveDAGFromQueue(self) == /\ pc[self] = "RemoveDAGFromQueue"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF TopoChangeForRC
                                  THEN /\ isDAGStale(currDAG[self].id)
                                       /\ TopoChangeForRC' = FALSE
                                  ELSE /\ TRUE
                                       /\ UNCHANGED TopoChangeForRC
                            /\ idWorkerWorkingOnDAG' = [idWorkerWorkingOnDAG EXCEPT ![currDAG[self].id] = DAG_UNLOCK]
                            /\ IRSet' = [IRSet EXCEPT ![self] = currDAG[self].dag.v]
                            /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, IRQueueRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            IRChangeForRC, TEEventQueue, 
                                            DAGEventQueue, DAGQueue, DAGID, 
                                            MaxDAGID, DAGState, nxtRCIRID, 
                                            IRDoneSet, idThreadWorkingOnIR, 
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
                                            controllerStateNIB, IRStatusNIB, 
                                            SwSuspensionStatusNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            toBeScheduledIRs, nextIR, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, key, op1_, op2, debug, 
                                            transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_co, transaction_co, 
                                            NIBMsg, op1, IRQueue, 
                                            op_ir_status_change_, removeIR, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, 
                                            transaction_con, topo_change, irID, 
                                            removedIR, msg, 
                                            op_ir_status_change, 
                                            op_first_install, transaction >>

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF IRSet[self] # {} /\ allIRsInDAGInstalled(self[1], currDAG[self].dag)
                                     THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = self
                                          /\ nextIR' = [nextIR EXCEPT ![self] = CHOOSE x \in IRSet[self]: TRUE]
                                          /\ IF irTypeMapping[nextIR'[self]].type = INSTALL_FLOW
                                                THEN /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \cup {nextIR'[self]}]
                                                ELSE /\ IRDoneSet' = [IRDoneSet EXCEPT ![self[1]] = IRDoneSet[self[1]] \ {getIRIDForFlow(irTypeMapping[nextIR'[self]].flow, INSTALLED_SUCCESSFULLY)}]
                                          /\ IRSet' = [IRSet EXCEPT ![self] = IRSet[self] \ {nextIR'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                          /\ UNCHANGED DAGQueue
                                     ELSE /\ IF allIRsInDAGInstalled(self[1], currDAG[self].dag) \/ isDAGStale(currDAG[self].id)
                                                THEN /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                     /\ DAGQueue' = [DAGQueue EXCEPT ![self[1]] = Tail(DAGQueue[self[1]])]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED DAGQueue
                                          /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                          /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                          /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                          /\ pc' = [pc EXCEPT ![self] = "RCWorkerSeqProc"]
                                          /\ UNCHANGED << IRDoneSet, nextIR, 
                                                          IRSet >>
                               /\ UNCHANGED << switchLock, FirstInstallOFC, 
                                               FirstInstallNIB, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, 
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
                                               switchOrdering, dependencyGraph, 
                                               ir2sw, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               SwSuspensionStatusRC, IRQueueRC, 
                                               SetScheduledIRsRC, 
                                               FlagRCNIBEventHandlerFailover, 
                                               FlagRCSequencerFailover, 
                                               RC_READY, IRChangeForRC, 
                                               TopoChangeForRC, TEEventQueue, 
                                               DAGEventQueue, DAGID, MaxDAGID, 
                                               DAGState, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, 
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
                                               NIB2RC, X2NIB, OFC2NIB, RC2NIB, 
                                               FlagNIBFailover, 
                                               FlagNIBRCEventhandlerFailover, 
                                               FlagNIBOFCEventhandlerFailover, 
                                               NIB_READY_FOR_RC, 
                                               NIB_READY_FOR_OFC, masterState, 
                                               controllerStateNIB, IRStatusNIB, 
                                               SwSuspensionStatusNIB, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               X2NIB_len, NIBThreadID, 
                                               RCThreadID, ingressPkt, 
                                               ingressIR, egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, value, 
                                               rowRemove_N, IR2Remove, 
                                               send_NIB_back, stepOfFailure_N, 
                                               IRIndex, debug_N, NIBMsg_, 
                                               isBootStrap_, sw_id, 
                                               transaction_, topoChangeEvent, 
                                               currSetDownSw, prev_dag_id, 
                                               init, nxtDAG, setRemovableIRs, 
                                               currIR, currIRInDAG, 
                                               nxtDAGVertices, setIRsInDAG, 
                                               prev_dag, toBeScheduledIRs, 
                                               transaction_c, stepOfFailure_c, 
                                               currDAG, key, op1_, op2, debug, 
                                               transaction_O, IRQueueTmp, 
                                               NIBMsg_O, isBootStrap, 
                                               localIRSet, NIBIRSet, newIRSet, 
                                               newIR, nextIRToSent, rowIndex, 
                                               rowRemove, stepOfFailure_co, 
                                               transaction_co, NIBMsg, op1, 
                                               IRQueue, op_ir_status_change_, 
                                               removeIR, monitoringEvent, 
                                               setIRsToReset, resetIR, 
                                               stepOfFailure, transaction_con, 
                                               topo_change, irID, removedIR, 
                                               msg, op_ir_status_change, 
                                               op_first_install, transaction >>

RCSequencerFailover(self) == /\ pc[self] = "RCSequencerFailover"
                             /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                             /\ toBeScheduledIRs' = [toBeScheduledIRs EXCEPT ![self] = {}]
                             /\ controllerSubmoduleFailStat[<<rc0,CONT_WORKER_SEQ>>] = NotFailed /\
                                      controllerSubmoduleFailStat[<<rc0,CONT_RC_NIB_EVENT>>] = NotFailed
                             /\ pc' = [pc EXCEPT ![self] = "RCWorkerSeqScheduleDAG"]
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstallOFC, FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, 
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
                                             switchOrdering, dependencyGraph, 
                                             ir2sw, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             SwSuspensionStatusRC, IRQueueRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             IRChangeForRC, TopoChangeForRC, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, DAGID, MaxDAGID, 
                                             DAGState, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, IRDoneSet, 
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
                                             controllerStateNIB, IRStatusNIB, 
                                             SwSuspensionStatusNIB, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, obj, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, value_, nextTrans_, 
                                             value_N, rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug_N, NIBMsg_, 
                                             isBootStrap_, sw_id, transaction_, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, nextIR, 
                                             transaction_c, stepOfFailure_c, 
                                             currDAG, IRSet, key, op1_, op2, 
                                             debug, transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, newIRSet, newIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_co, transaction_co, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, 
                                             transaction_con, topo_change, 
                                             irID, removedIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

controllerSequencer(self) == RCWorkerSeqProc(self)
                                \/ RCWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteIRDoneSet(self)
                                \/ RCSendIR2NIB(self)
                                \/ RemoveDAGFromQueue(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ RCSequencerFailover(self)

NIBFailure(self) == /\ pc[self] = "NIBFailure"
                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                    /\ controllerSubmoduleFailStat' = [controllerSubmoduleFailStat EXCEPT ![<<nib0,CONT_NIB_RC_EVENT>>] = Failed,
                                                                                          ![<<nib0,CONT_NIB_OFC_EVENT>>] = Failed]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << switchLock, controllerLock, 
                                    FirstInstallOFC, FirstInstallNIB, 
                                    sw_fail_ordering_var, ContProcSet, 
                                    SwProcSet, irTypeMapping, 
                                    swSeqChangedStatus, controller2Switch, 
                                    switch2Controller, switchStatus, 
                                    installedIRs, NicAsic2OfaBuff, 
                                    Ofa2NicAsicBuff, Installer2OfaBuff, 
                                    Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                    RecoveryStatus, controllerSubmoduleFailNum, 
                                    switchOrdering, dependencyGraph, ir2sw, 
                                    NIBUpdateForRC, controllerStateRC, 
                                    IRStatusRC, SwSuspensionStatusRC, 
                                    IRQueueRC, SetScheduledIRsRC, 
                                    FlagRCNIBEventHandlerFailover, 
                                    FlagRCSequencerFailover, RC_READY, 
                                    IRChangeForRC, TopoChangeForRC, 
                                    TEEventQueue, DAGEventQueue, DAGQueue, 
                                    DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                    idWorkerWorkingOnDAG, IRDoneSet, 
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
                                    masterState, controllerStateNIB, 
                                    IRStatusNIB, SwSuspensionStatusNIB, 
                                    IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                    NIBThreadID, RCThreadID, ingressPkt, 
                                    ingressIR, egressMsg, ofaInMsg, 
                                    ofaOutConfirmation, installerInIR, 
                                    statusMsg, notFailedSet, failedElem, obj, 
                                    failedSet, statusResolveMsg, recoveredElem, 
                                    value_, nextTrans_, value_N, rowRemove_, 
                                    IR2Remove_, send_NIB_back_, stepOfFailure_, 
                                    IRIndex_, debug_, nextTrans, value, 
                                    rowRemove_N, IR2Remove, send_NIB_back, 
                                    stepOfFailure_N, IRIndex, debug_N, NIBMsg_, 
                                    isBootStrap_, sw_id, transaction_, 
                                    topoChangeEvent, currSetDownSw, 
                                    prev_dag_id, init, nxtDAG, setRemovableIRs, 
                                    currIR, currIRInDAG, nxtDAGVertices, 
                                    setIRsInDAG, prev_dag, toBeScheduledIRs, 
                                    nextIR, transaction_c, stepOfFailure_c, 
                                    currDAG, IRSet, key, op1_, op2, debug, 
                                    transaction_O, IRQueueTmp, NIBMsg_O, 
                                    isBootStrap, localIRSet, NIBIRSet, 
                                    newIRSet, newIR, nextIRToSent, rowIndex, 
                                    rowRemove, stepOfFailure_co, 
                                    transaction_co, NIBMsg, op1, IRQueue, 
                                    op_ir_status_change_, removeIR, 
                                    monitoringEvent, setIRsToReset, resetIR, 
                                    stepOfFailure, transaction_con, 
                                    topo_change, irID, removedIR, msg, 
                                    op_ir_status_change, op_first_install, 
                                    transaction >>

NIBFailureProc(self) == NIBFailure(self)

OFCFailoverResetStates(self) == /\ pc[self] = "OFCFailoverResetStates"
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                                irTypeMapping, 
                                                swSeqChangedStatus, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, 
                                                Ofa2InstallerBuff, TCAM, 
                                                controlMsgCounter, 
                                                RecoveryStatus, 
                                                controllerSubmoduleFailNum, 
                                                switchOrdering, 
                                                dependencyGraph, ir2sw, 
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                SwSuspensionStatusRC, 
                                                IRQueueRC, SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, IRChangeForRC, 
                                                TopoChangeForRC, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
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
                                                controllerStateNIB, 
                                                IRStatusNIB, 
                                                SwSuspensionStatusNIB, 
                                                IRQueueNIB, SetScheduledIRs, 
                                                X2NIB_len, NIBThreadID, 
                                                RCThreadID, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug_N, NIBMsg_, 
                                                isBootStrap_, sw_id, 
                                                transaction_, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, nxtDAG, setRemovableIRs, 
                                                currIR, currIRInDAG, 
                                                nxtDAGVertices, setIRsInDAG, 
                                                prev_dag, toBeScheduledIRs, 
                                                nextIR, transaction_c, 
                                                stepOfFailure_c, currDAG, 
                                                IRSet, key, op1_, op2, debug, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, newIRSet, 
                                                newIR, nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_co, 
                                                transaction_co, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, transaction_con, 
                                                topo_change, irID, removedIR, 
                                                msg, op_ir_status_change, 
                                                op_first_install, transaction >>

OFCReadSwitches(self) == /\ pc[self] = "OFCReadSwitches"
                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         ir2sw, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         SwSuspensionStatusRC, IRQueueRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         IRChangeForRC, TopoChangeForRC, 
                                         TEEventQueue, DAGEventQueue, DAGQueue, 
                                         DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                         idWorkerWorkingOnDAG, IRDoneSet, 
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
                                         IRStatusNIB, SwSuspensionStatusNIB, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, obj, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug_N, 
                                         NIBMsg_, isBootStrap_, sw_id, 
                                         transaction_, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, 
                                         toBeScheduledIRs, nextIR, 
                                         transaction_c, stepOfFailure_c, 
                                         currDAG, IRSet, key, op1_, op2, debug, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         newIRSet, newIR, nextIRToSent, 
                                         rowIndex, rowRemove, stepOfFailure_co, 
                                         transaction_co, NIBMsg, op1, IRQueue, 
                                         op_ir_status_change_, removeIR, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, 
                                         transaction_con, topo_change, irID, 
                                         removedIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

OFCReadNIB(self) == /\ pc[self] = "OFCReadNIB"
                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                    /\ NIB_READY_FOR_OFC \/ isNIBUp(NIBThreadID)
                    /\ IRQueueOFC' = SelectSeq(IRQueueRC, LAMBDA i: IRStatusOFC[i.IR] # IR_DONE)
                    /\ pc' = [pc EXCEPT ![self] = "OFCBack2Normal"]
                    /\ UNCHANGED << switchLock, controllerLock, 
                                    FirstInstallOFC, FirstInstallNIB, 
                                    sw_fail_ordering_var, ContProcSet, 
                                    SwProcSet, irTypeMapping, 
                                    swSeqChangedStatus, controller2Switch, 
                                    switch2Controller, switchStatus, 
                                    installedIRs, NicAsic2OfaBuff, 
                                    Ofa2NicAsicBuff, Installer2OfaBuff, 
                                    Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                    RecoveryStatus, controllerSubmoduleFailNum, 
                                    controllerSubmoduleFailStat, 
                                    switchOrdering, dependencyGraph, ir2sw, 
                                    NIBUpdateForRC, controllerStateRC, 
                                    IRStatusRC, SwSuspensionStatusRC, 
                                    IRQueueRC, SetScheduledIRsRC, 
                                    FlagRCNIBEventHandlerFailover, 
                                    FlagRCSequencerFailover, RC_READY, 
                                    IRChangeForRC, TopoChangeForRC, 
                                    TEEventQueue, DAGEventQueue, DAGQueue, 
                                    DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                    idWorkerWorkingOnDAG, IRDoneSet, 
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
                                    masterState, controllerStateNIB, 
                                    IRStatusNIB, SwSuspensionStatusNIB, 
                                    IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                    NIBThreadID, RCThreadID, ingressPkt, 
                                    ingressIR, egressMsg, ofaInMsg, 
                                    ofaOutConfirmation, installerInIR, 
                                    statusMsg, notFailedSet, failedElem, obj, 
                                    failedSet, statusResolveMsg, recoveredElem, 
                                    value_, nextTrans_, value_N, rowRemove_, 
                                    IR2Remove_, send_NIB_back_, stepOfFailure_, 
                                    IRIndex_, debug_, nextTrans, value, 
                                    rowRemove_N, IR2Remove, send_NIB_back, 
                                    stepOfFailure_N, IRIndex, debug_N, NIBMsg_, 
                                    isBootStrap_, sw_id, transaction_, 
                                    topoChangeEvent, currSetDownSw, 
                                    prev_dag_id, init, nxtDAG, setRemovableIRs, 
                                    currIR, currIRInDAG, nxtDAGVertices, 
                                    setIRsInDAG, prev_dag, toBeScheduledIRs, 
                                    nextIR, transaction_c, stepOfFailure_c, 
                                    currDAG, IRSet, key, op1_, op2, debug, 
                                    transaction_O, IRQueueTmp, NIBMsg_O, 
                                    isBootStrap, localIRSet, NIBIRSet, 
                                    newIRSet, newIR, nextIRToSent, rowIndex, 
                                    rowRemove, stepOfFailure_co, 
                                    transaction_co, NIBMsg, op1, IRQueue, 
                                    op_ir_status_change_, removeIR, 
                                    monitoringEvent, setIRsToReset, resetIR, 
                                    stepOfFailure, transaction_con, 
                                    topo_change, irID, removedIR, msg, 
                                    op_ir_status_change, op_first_install, 
                                    transaction >>

OFCBack2Normal(self) == /\ pc[self] = "OFCBack2Normal"
                        /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
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
                                        SwProcSet, irTypeMapping, 
                                        swSeqChangedStatus, controller2Switch, 
                                        switch2Controller, switchStatus, 
                                        installedIRs, NicAsic2OfaBuff, 
                                        Ofa2NicAsicBuff, Installer2OfaBuff, 
                                        Ofa2InstallerBuff, TCAM, 
                                        controlMsgCounter, RecoveryStatus, 
                                        controllerSubmoduleFailNum, 
                                        switchOrdering, dependencyGraph, ir2sw, 
                                        NIBUpdateForRC, controllerStateRC, 
                                        IRStatusRC, SwSuspensionStatusRC, 
                                        IRQueueRC, SetScheduledIRsRC, 
                                        FlagRCNIBEventHandlerFailover, 
                                        FlagRCSequencerFailover, RC_READY, 
                                        IRChangeForRC, TopoChangeForRC, 
                                        TEEventQueue, DAGEventQueue, DAGQueue, 
                                        DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                        idWorkerWorkingOnDAG, IRDoneSet, 
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
                                        IRStatusNIB, SwSuspensionStatusNIB, 
                                        IRQueueNIB, SetScheduledIRs, X2NIB_len, 
                                        NIBThreadID, RCThreadID, ingressPkt, 
                                        ingressIR, egressMsg, ofaInMsg, 
                                        ofaOutConfirmation, installerInIR, 
                                        statusMsg, notFailedSet, failedElem, 
                                        obj, failedSet, statusResolveMsg, 
                                        recoveredElem, value_, nextTrans_, 
                                        value_N, rowRemove_, IR2Remove_, 
                                        send_NIB_back_, stepOfFailure_, 
                                        IRIndex_, debug_, nextTrans, value, 
                                        rowRemove_N, IR2Remove, send_NIB_back, 
                                        stepOfFailure_N, IRIndex, debug_N, 
                                        NIBMsg_, isBootStrap_, sw_id, 
                                        transaction_, topoChangeEvent, 
                                        currSetDownSw, prev_dag_id, init, 
                                        nxtDAG, setRemovableIRs, currIR, 
                                        currIRInDAG, nxtDAGVertices, 
                                        setIRsInDAG, prev_dag, 
                                        toBeScheduledIRs, nextIR, 
                                        transaction_c, stepOfFailure_c, 
                                        currDAG, IRSet, key, op1_, op2, debug, 
                                        IRQueueTmp, NIBMsg_O, isBootStrap, 
                                        localIRSet, NIBIRSet, newIRSet, newIR, 
                                        nextIRToSent, rowIndex, rowRemove, 
                                        stepOfFailure_co, transaction_co, 
                                        NIBMsg, op1, IRQueue, 
                                        op_ir_status_change_, removeIR, 
                                        monitoringEvent, setIRsToReset, 
                                        resetIR, stepOfFailure, 
                                        transaction_con, topo_change, irID, 
                                        removedIR, msg, op_ir_status_change, 
                                        op_first_install, transaction >>

OFCFailoverProc(self) == OFCFailoverResetStates(self)
                            \/ OFCReadSwitches(self) \/ OFCReadNIB(self)
                            \/ OFCBack2Normal(self)

OFCNIBEventHanderProc(self) == /\ pc[self] = "OFCNIBEventHanderProc"
                               /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                               /\ switchLock = <<NO_LOCK, NO_LOCK>>
                               /\ IF isOFCFailed(self)
                                     THEN /\ FlagOFCNIBEventHandlerFailover' = TRUE
                                          /\ pc' = [pc EXCEPT ![self] = "OFCNIBEventHandlerFailover"]
                                          /\ UNCHANGED << IRStatusOFC, 
                                                          IRQueueOFC, NIB2OFC, 
                                                          NIBMsg_O, localIRSet, 
                                                          NIBIRSet, newIRSet, 
                                                          newIR >>
                                     ELSE /\ NIB2OFC # <<>>
                                          /\ NIBMsg_O' = [NIBMsg_O EXCEPT ![self] = Head(NIB2OFC)]
                                          /\ NIB2OFC' = Tail(NIB2OFC)
                                          /\ IF Cardinality(DOMAIN NIBMsg_O'[self].value.IRStatusNIB) > Cardinality(DOMAIN IRStatusOFC)
                                                THEN /\ newIRSet' = [newIRSet EXCEPT ![self] = DOMAIN NIBMsg_O'[self].value.IRStatusNIB \ DOMAIN IRStatusOFC]
                                                     /\ Assert(Cardinality(newIRSet'[self])=1, 
                                                               "Failure of assertion at line 2381, column 21.")
                                                     /\ newIR' = [newIR EXCEPT ![self] = CHOOSE x \in newIRSet'[self]: TRUE]
                                                     /\ IRStatusOFC' = IRStatusOFC @@ (newIR'[self] :> IR_NONE)
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << IRStatusOFC, 
                                                                     newIRSet, 
                                                                     newIR >>
                                          /\ localIRSet' = [localIRSet EXCEPT ![self] = {IRQueueOFC[i].IR: i \in DOMAIN IRQueueOFC}]
                                          /\ NIBIRSet' = [NIBIRSet EXCEPT ![self] = {NIBMsg_O'[self].value.IRQueueNIB[i].IR: i \in DOMAIN NIBMsg_O'[self].value.IRQueueNIB}]
                                          /\ IF localIRSet'[self] # NIBIRSet'[self]
                                                THEN /\ IRQueueOFC' = SelectSeq(NIBMsg_O'[self].value.IRQueueNIB, LAMBDA i: i.IR \notin DOMAIN IRStatusOFC' \/ IRStatusOFC'[i.IR] = IR_NONE)
                                                     /\ Assert(Len(IRQueueOFC') <= MaxNumIRs, 
                                                               "Failure of assertion at line 2391, column 21.")
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED IRQueueOFC
                                          /\ pc' = [pc EXCEPT ![self] = "OFCNIBEventHanderProc"]
                                          /\ UNCHANGED FlagOFCNIBEventHandlerFailover
                               /\ UNCHANGED << switchLock, controllerLock, 
                                               FirstInstallOFC, 
                                               FirstInstallNIB, 
                                               sw_fail_ordering_var, 
                                               ContProcSet, SwProcSet, 
                                               irTypeMapping, 
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
                                               switchOrdering, dependencyGraph, 
                                               ir2sw, NIBUpdateForRC, 
                                               controllerStateRC, IRStatusRC, 
                                               SwSuspensionStatusRC, IRQueueRC, 
                                               SetScheduledIRsRC, 
                                               FlagRCNIBEventHandlerFailover, 
                                               FlagRCSequencerFailover, 
                                               RC_READY, IRChangeForRC, 
                                               TopoChangeForRC, TEEventQueue, 
                                               DAGEventQueue, DAGQueue, DAGID, 
                                               MaxDAGID, DAGState, nxtRCIRID, 
                                               idWorkerWorkingOnDAG, IRDoneSet, 
                                               idThreadWorkingOnIR, 
                                               workerThreadRanking, 
                                               controllerStateOFC, 
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
                                               controllerStateNIB, IRStatusNIB, 
                                               SwSuspensionStatusNIB, 
                                               IRQueueNIB, SetScheduledIRs, 
                                               X2NIB_len, NIBThreadID, 
                                               RCThreadID, ingressPkt, 
                                               ingressIR, egressMsg, ofaInMsg, 
                                               ofaOutConfirmation, 
                                               installerInIR, statusMsg, 
                                               notFailedSet, failedElem, obj, 
                                               failedSet, statusResolveMsg, 
                                               recoveredElem, value_, 
                                               nextTrans_, value_N, rowRemove_, 
                                               IR2Remove_, send_NIB_back_, 
                                               stepOfFailure_, IRIndex_, 
                                               debug_, nextTrans, value, 
                                               rowRemove_N, IR2Remove, 
                                               send_NIB_back, stepOfFailure_N, 
                                               IRIndex, debug_N, NIBMsg_, 
                                               isBootStrap_, sw_id, 
                                               transaction_, topoChangeEvent, 
                                               currSetDownSw, prev_dag_id, 
                                               init, nxtDAG, setRemovableIRs, 
                                               currIR, currIRInDAG, 
                                               nxtDAGVertices, setIRsInDAG, 
                                               prev_dag, toBeScheduledIRs, 
                                               nextIR, transaction_c, 
                                               stepOfFailure_c, currDAG, IRSet, 
                                               key, op1_, op2, debug, 
                                               transaction_O, IRQueueTmp, 
                                               isBootStrap, nextIRToSent, 
                                               rowIndex, rowRemove, 
                                               stepOfFailure_co, 
                                               transaction_co, NIBMsg, op1, 
                                               IRQueue, op_ir_status_change_, 
                                               removeIR, monitoringEvent, 
                                               setIRsToReset, resetIR, 
                                               stepOfFailure, transaction_con, 
                                               topo_change, irID, removedIR, 
                                               msg, op_ir_status_change, 
                                               op_first_install, transaction >>

OFCNIBEventHandlerFailover(self) == /\ pc[self] = "OFCNIBEventHandlerFailover"
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ isOFCUp(OFCThreadID)
                                    /\ pc' = [pc EXCEPT ![self] = "OFCNIBEventHanderProc"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstallOFC, 
                                                    FirstInstallNIB, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    irTypeMapping, 
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
                                                    dependencyGraph, ir2sw, 
                                                    NIBUpdateForRC, 
                                                    controllerStateRC, 
                                                    IRStatusRC, 
                                                    SwSuspensionStatusRC, 
                                                    IRQueueRC, 
                                                    SetScheduledIRsRC, 
                                                    FlagRCNIBEventHandlerFailover, 
                                                    FlagRCSequencerFailover, 
                                                    RC_READY, IRChangeForRC, 
                                                    TopoChangeForRC, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    IRDoneSet, 
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
                                                    IRStatusNIB, 
                                                    SwSuspensionStatusNIB, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, X2NIB_len, 
                                                    NIBThreadID, RCThreadID, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    obj, failedSet, 
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
                                                    debug_N, NIBMsg_, 
                                                    isBootStrap_, sw_id, 
                                                    transaction_, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    toBeScheduledIRs, nextIR, 
                                                    transaction_c, 
                                                    stepOfFailure_c, currDAG, 
                                                    IRSet, key, op1_, op2, 
                                                    debug, transaction_O, 
                                                    IRQueueTmp, NIBMsg_O, 
                                                    isBootStrap, localIRSet, 
                                                    NIBIRSet, newIRSet, newIR, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, 
                                                    stepOfFailure_co, 
                                                    transaction_co, NIBMsg, 
                                                    op1, IRQueue, 
                                                    op_ir_status_change_, 
                                                    removeIR, monitoringEvent, 
                                                    setIRsToReset, resetIR, 
                                                    stepOfFailure, 
                                                    transaction_con, 
                                                    topo_change, irID, 
                                                    removedIR, msg, 
                                                    op_ir_status_change, 
                                                    op_first_install, 
                                                    transaction >>

OFCNIBEventHandler(self) == OFCNIBEventHanderProc(self)
                               \/ OFCNIBEventHandlerFailover(self)

OFCThreadGetNextIR(self) == /\ pc[self] = "OFCThreadGetNextIR"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, IRQueueRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            IRChangeForRC, TopoChangeForRC, 
                                            TEEventQueue, DAGEventQueue, 
                                            DAGQueue, DAGID, MaxDAGID, 
                                            DAGState, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, IRDoneSet, 
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
                                            controllerStateNIB, IRStatusNIB, 
                                            SwSuspensionStatusNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            toBeScheduledIRs, nextIR, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, IRSet, key, op1_, op2, 
                                            debug, transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            rowRemove, stepOfFailure_co, 
                                            transaction_co, NIBMsg, op1, 
                                            IRQueue, op_ir_status_change_, 
                                            removeIR, monitoringEvent, 
                                            setIRsToReset, resetIR, 
                                            stepOfFailure, transaction_con, 
                                            topo_change, irID, removedIR, msg, 
                                            op_ir_status_change, 
                                            op_first_install, transaction >>

OFCThreadSendIR(self) == /\ pc[self] = "OFCThreadSendIR"
                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                         SwProcSet, irTypeMapping, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         ir2sw, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         SwSuspensionStatusRC, IRQueueRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         IRChangeForRC, TopoChangeForRC, 
                                         TEEventQueue, DAGEventQueue, DAGQueue, 
                                         DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                         idWorkerWorkingOnDAG, IRDoneSet, 
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
                                         IRStatusNIB, SwSuspensionStatusNIB, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, obj, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug_N, 
                                         NIBMsg_, isBootStrap_, sw_id, 
                                         transaction_, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, 
                                         toBeScheduledIRs, nextIR, 
                                         transaction_c, stepOfFailure_c, 
                                         currDAG, IRSet, key, op1_, op2, debug, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         newIRSet, newIR, nextIRToSent, 
                                         rowIndex, rowRemove, stepOfFailure_co, 
                                         transaction_co, NIBMsg, op1, IRQueue, 
                                         op_ir_status_change_, removeIR, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, 
                                         transaction_con, topo_change, irID, 
                                         removedIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

OFCThreadNotifyNIBIRSent(self) == /\ pc[self] = "OFCThreadNotifyNIBIRSent"
                                  /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                  /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                  /\ IF isOFCFailed(self)
                                        THEN /\ FlagOFCWorkerFailover' = TRUE
                                             /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                             /\ UNCHANGED << OFC2NIB, 
                                                             transaction_co, 
                                                             op_ir_status_change_ >>
                                        ELSE /\ isNIBUp(NIBThreadID)
                                             /\ op_ir_status_change_' = [op_ir_status_change_ EXCEPT ![self] = [table |-> NIBT_IR_STATUS, key |-> nextIRToSent[self], value |-> IR_SENT]]
                                             /\ transaction_co' = [transaction_co EXCEPT ![self] = [name |-> "OFCChangeIRStatus2Sent", ops |-> <<op_ir_status_change_'[self]>>]]
                                             /\ OFC2NIB' = OFC2NIB \o <<transaction_co'[self]>>
                                             /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIRInner"]
                                             /\ UNCHANGED FlagOFCWorkerFailover
                                  /\ UNCHANGED << switchLock, controllerLock, 
                                                  FirstInstallOFC, 
                                                  FirstInstallNIB, 
                                                  sw_fail_ordering_var, 
                                                  ContProcSet, SwProcSet, 
                                                  irTypeMapping, 
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
                                                  dependencyGraph, ir2sw, 
                                                  NIBUpdateForRC, 
                                                  controllerStateRC, 
                                                  IRStatusRC, 
                                                  SwSuspensionStatusRC, 
                                                  IRQueueRC, SetScheduledIRsRC, 
                                                  FlagRCNIBEventHandlerFailover, 
                                                  FlagRCSequencerFailover, 
                                                  RC_READY, IRChangeForRC, 
                                                  TopoChangeForRC, 
                                                  TEEventQueue, DAGEventQueue, 
                                                  DAGQueue, DAGID, MaxDAGID, 
                                                  DAGState, nxtRCIRID, 
                                                  idWorkerWorkingOnDAG, 
                                                  IRDoneSet, 
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
                                                  IRStatusNIB, 
                                                  SwSuspensionStatusNIB, 
                                                  IRQueueNIB, SetScheduledIRs, 
                                                  X2NIB_len, NIBThreadID, 
                                                  RCThreadID, ingressPkt, 
                                                  ingressIR, egressMsg, 
                                                  ofaInMsg, ofaOutConfirmation, 
                                                  installerInIR, statusMsg, 
                                                  notFailedSet, failedElem, 
                                                  obj, failedSet, 
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
                                                  debug_N, NIBMsg_, 
                                                  isBootStrap_, sw_id, 
                                                  transaction_, 
                                                  topoChangeEvent, 
                                                  currSetDownSw, prev_dag_id, 
                                                  init, nxtDAG, 
                                                  setRemovableIRs, currIR, 
                                                  currIRInDAG, nxtDAGVertices, 
                                                  setIRsInDAG, prev_dag, 
                                                  toBeScheduledIRs, nextIR, 
                                                  transaction_c, 
                                                  stepOfFailure_c, currDAG, 
                                                  IRSet, key, op1_, op2, debug, 
                                                  transaction_O, IRQueueTmp, 
                                                  NIBMsg_O, isBootStrap, 
                                                  localIRSet, NIBIRSet, 
                                                  newIRSet, newIR, 
                                                  nextIRToSent, rowIndex, 
                                                  rowRemove, stepOfFailure_co, 
                                                  NIBMsg, op1, IRQueue, 
                                                  removeIR, monitoringEvent, 
                                                  setIRsToReset, resetIR, 
                                                  stepOfFailure, 
                                                  transaction_con, topo_change, 
                                                  irID, removedIR, msg, 
                                                  op_ir_status_change, 
                                                  op_first_install, 
                                                  transaction >>

ControllerThreadForwardIRInner(self) == /\ pc[self] = "ControllerThreadForwardIRInner"
                                        /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                        /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                        /\ IF isOFCFailed(self)
                                              THEN /\ FlagOFCWorkerFailover' = TRUE
                                                   /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   controller2Switch >>
                                              ELSE /\ Assert(irTypeMapping[nextIRToSent[self]].type \in {INSTALL_FLOW, DELETE_FLOW}, 
                                                             "Failure of assertion at line 1057, column 9 of macro called at line 2462, column 17.")
                                                   /\ Assert(irTypeMapping[nextIRToSent[self]].flow \in 1..MaxNumFlows, 
                                                             "Failure of assertion at line 1058, column 9 of macro called at line 2462, column 17.")
                                                   /\ controller2Switch' = [controller2Switch EXCEPT ![ir2sw[nextIRToSent[self]]] = Append(controller2Switch[ir2sw[nextIRToSent[self]]], [type |-> irTypeMapping[nextIRToSent[self]].type,
                                                                                                                                                                                          to |-> ir2sw[nextIRToSent[self]],
                                                                                                                                                                                          flow |-> irTypeMapping[nextIRToSent[self]].flow])]
                                                   /\ IF whichSwitchModel(ir2sw[nextIRToSent[self]]) = SW_COMPLEX_MODEL
                                                         THEN /\ switchLock' = <<NIC_ASIC_IN, ir2sw[nextIRToSent[self]]>>
                                                         ELSE /\ switchLock' = <<SW_SIMPLE_ID, ir2sw[nextIRToSent[self]]>>
                                                   /\ pc' = [pc EXCEPT ![self] = "OFCRemoveIRFromIRQueueOFCLocal"]
                                                   /\ UNCHANGED FlagOFCWorkerFailover
                                        /\ UNCHANGED << controllerLock, 
                                                        FirstInstallOFC, 
                                                        FirstInstallNIB, 
                                                        sw_fail_ordering_var, 
                                                        ContProcSet, SwProcSet, 
                                                        irTypeMapping, 
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
                                                        RecoveryStatus, 
                                                        controllerSubmoduleFailNum, 
                                                        controllerSubmoduleFailStat, 
                                                        switchOrdering, 
                                                        dependencyGraph, ir2sw, 
                                                        NIBUpdateForRC, 
                                                        controllerStateRC, 
                                                        IRStatusRC, 
                                                        SwSuspensionStatusRC, 
                                                        IRQueueRC, 
                                                        SetScheduledIRsRC, 
                                                        FlagRCNIBEventHandlerFailover, 
                                                        FlagRCSequencerFailover, 
                                                        RC_READY, 
                                                        IRChangeForRC, 
                                                        TopoChangeForRC, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, DAGID, 
                                                        MaxDAGID, DAGState, 
                                                        nxtRCIRID, 
                                                        idWorkerWorkingOnDAG, 
                                                        IRDoneSet, 
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
                                                        IRStatusNIB, 
                                                        SwSuspensionStatusNIB, 
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
                                                        failedElem, obj, 
                                                        failedSet, 
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
                                                        IRIndex, debug_N, 
                                                        NIBMsg_, isBootStrap_, 
                                                        sw_id, transaction_, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        nxtDAG, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        toBeScheduledIRs, 
                                                        nextIR, transaction_c, 
                                                        stepOfFailure_c, 
                                                        currDAG, IRSet, key, 
                                                        op1_, op2, debug, 
                                                        transaction_O, 
                                                        IRQueueTmp, NIBMsg_O, 
                                                        isBootStrap, 
                                                        localIRSet, NIBIRSet, 
                                                        newIRSet, newIR, 
                                                        nextIRToSent, rowIndex, 
                                                        rowRemove, 
                                                        stepOfFailure_co, 
                                                        transaction_co, NIBMsg, 
                                                        op1, IRQueue, 
                                                        op_ir_status_change_, 
                                                        removeIR, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, 
                                                        transaction_con, 
                                                        topo_change, irID, 
                                                        removedIR, msg, 
                                                        op_ir_status_change, 
                                                        op_first_install, 
                                                        transaction >>

OFCRemoveIRFromIRQueueOFCLocal(self) == /\ pc[self] = "OFCRemoveIRFromIRQueueOFCLocal"
                                        /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                                        irTypeMapping, 
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
                                                        dependencyGraph, ir2sw, 
                                                        NIBUpdateForRC, 
                                                        controllerStateRC, 
                                                        IRStatusRC, 
                                                        SwSuspensionStatusRC, 
                                                        IRQueueRC, 
                                                        SetScheduledIRsRC, 
                                                        FlagRCNIBEventHandlerFailover, 
                                                        FlagRCSequencerFailover, 
                                                        RC_READY, 
                                                        IRChangeForRC, 
                                                        TopoChangeForRC, 
                                                        TEEventQueue, 
                                                        DAGEventQueue, 
                                                        DAGQueue, DAGID, 
                                                        MaxDAGID, DAGState, 
                                                        nxtRCIRID, 
                                                        idWorkerWorkingOnDAG, 
                                                        IRDoneSet, 
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
                                                        IRStatusNIB, 
                                                        SwSuspensionStatusNIB, 
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
                                                        failedElem, obj, 
                                                        failedSet, 
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
                                                        IRIndex, debug_N, 
                                                        NIBMsg_, isBootStrap_, 
                                                        sw_id, transaction_, 
                                                        topoChangeEvent, 
                                                        currSetDownSw, 
                                                        prev_dag_id, init, 
                                                        nxtDAG, 
                                                        setRemovableIRs, 
                                                        currIR, currIRInDAG, 
                                                        nxtDAGVertices, 
                                                        setIRsInDAG, prev_dag, 
                                                        toBeScheduledIRs, 
                                                        nextIR, transaction_c, 
                                                        stepOfFailure_c, 
                                                        currDAG, IRSet, key, 
                                                        op1_, op2, debug, 
                                                        transaction_O, 
                                                        IRQueueTmp, NIBMsg_O, 
                                                        isBootStrap, 
                                                        localIRSet, NIBIRSet, 
                                                        newIRSet, newIR, 
                                                        nextIRToSent, rowIndex, 
                                                        stepOfFailure_co, 
                                                        transaction_co, NIBMsg, 
                                                        op1, IRQueue, 
                                                        op_ir_status_change_, 
                                                        monitoringEvent, 
                                                        setIRsToReset, resetIR, 
                                                        stepOfFailure, 
                                                        transaction_con, 
                                                        topo_change, irID, 
                                                        removedIR, msg, 
                                                        op_ir_status_change, 
                                                        op_first_install, 
                                                        transaction >>

OFCRemoveIRFromIRQueueRemote(self) == /\ pc[self] = "OFCRemoveIRFromIRQueueRemote"
                                      /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                      /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                      /\ IF isOFCFailed(self)
                                            THEN /\ FlagOFCWorkerFailover' = TRUE
                                                 /\ pc' = [pc EXCEPT ![self] = "OFCWorkerFailover"]
                                                 /\ UNCHANGED << OFC2NIB, 
                                                                 transaction_co, 
                                                                 op1, removeIR >>
                                            ELSE /\ IF removeIR[self] = TRUE
                                                       THEN /\ isNIBUp(NIBThreadID)
                                                            /\ op1' = [op1 EXCEPT ![self] = [table |-> NIBT_IR_QUEUE, key |-> nextIRToSent[self]]]
                                                            /\ transaction_co' = [transaction_co EXCEPT ![self] = [name |-> "RemoveIR", ops |-> <<op1'[self]>>]]
                                                            /\ OFC2NIB' = OFC2NIB \o <<transaction_co'[self]>>
                                                            /\ removeIR' = [removeIR EXCEPT ![self] = FALSE]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED << OFC2NIB, 
                                                                            transaction_co, 
                                                                            op1, 
                                                                            removeIR >>
                                                 /\ pc' = [pc EXCEPT ![self] = "OFCThreadGetNextIR"]
                                                 /\ UNCHANGED FlagOFCWorkerFailover
                                      /\ UNCHANGED << switchLock, 
                                                      controllerLock, 
                                                      FirstInstallOFC, 
                                                      FirstInstallNIB, 
                                                      sw_fail_ordering_var, 
                                                      ContProcSet, SwProcSet, 
                                                      irTypeMapping, 
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
                                                      dependencyGraph, ir2sw, 
                                                      NIBUpdateForRC, 
                                                      controllerStateRC, 
                                                      IRStatusRC, 
                                                      SwSuspensionStatusRC, 
                                                      IRQueueRC, 
                                                      SetScheduledIRsRC, 
                                                      FlagRCNIBEventHandlerFailover, 
                                                      FlagRCSequencerFailover, 
                                                      RC_READY, IRChangeForRC, 
                                                      TopoChangeForRC, 
                                                      TEEventQueue, 
                                                      DAGEventQueue, DAGQueue, 
                                                      DAGID, MaxDAGID, 
                                                      DAGState, nxtRCIRID, 
                                                      idWorkerWorkingOnDAG, 
                                                      IRDoneSet, 
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
                                                      IRStatusNIB, 
                                                      SwSuspensionStatusNIB, 
                                                      IRQueueNIB, 
                                                      SetScheduledIRs, 
                                                      X2NIB_len, NIBThreadID, 
                                                      RCThreadID, ingressPkt, 
                                                      ingressIR, egressMsg, 
                                                      ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
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
                                                      debug_N, NIBMsg_, 
                                                      isBootStrap_, sw_id, 
                                                      transaction_, 
                                                      topoChangeEvent, 
                                                      currSetDownSw, 
                                                      prev_dag_id, init, 
                                                      nxtDAG, setRemovableIRs, 
                                                      currIR, currIRInDAG, 
                                                      nxtDAGVertices, 
                                                      setIRsInDAG, prev_dag, 
                                                      toBeScheduledIRs, nextIR, 
                                                      transaction_c, 
                                                      stepOfFailure_c, currDAG, 
                                                      IRSet, key, op1_, op2, 
                                                      debug, transaction_O, 
                                                      IRQueueTmp, NIBMsg_O, 
                                                      isBootStrap, localIRSet, 
                                                      NIBIRSet, newIRSet, 
                                                      newIR, nextIRToSent, 
                                                      rowIndex, rowRemove, 
                                                      stepOfFailure_co, NIBMsg, 
                                                      IRQueue, 
                                                      op_ir_status_change_, 
                                                      monitoringEvent, 
                                                      setIRsToReset, resetIR, 
                                                      stepOfFailure, 
                                                      transaction_con, 
                                                      topo_change, irID, 
                                                      removedIR, msg, 
                                                      op_ir_status_change, 
                                                      op_first_install, 
                                                      transaction >>

OFCWorkerFailover(self) == /\ pc[self] = "OFCWorkerFailover"
                           /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                           /\ switchLock = <<NO_LOCK, NO_LOCK>>
                           /\ isOFCUp(OFCThreadID)
                           /\ pc' = [pc EXCEPT ![self] = "OFCThreadGetNextIR"]
                           /\ UNCHANGED << switchLock, controllerLock, 
                                           FirstInstallOFC, FirstInstallNIB, 
                                           sw_fail_ordering_var, ContProcSet, 
                                           SwProcSet, irTypeMapping, 
                                           swSeqChangedStatus, 
                                           controller2Switch, 
                                           switch2Controller, switchStatus, 
                                           installedIRs, NicAsic2OfaBuff, 
                                           Ofa2NicAsicBuff, Installer2OfaBuff, 
                                           Ofa2InstallerBuff, TCAM, 
                                           controlMsgCounter, RecoveryStatus, 
                                           controllerSubmoduleFailNum, 
                                           controllerSubmoduleFailStat, 
                                           switchOrdering, dependencyGraph, 
                                           ir2sw, NIBUpdateForRC, 
                                           controllerStateRC, IRStatusRC, 
                                           SwSuspensionStatusRC, IRQueueRC, 
                                           SetScheduledIRsRC, 
                                           FlagRCNIBEventHandlerFailover, 
                                           FlagRCSequencerFailover, RC_READY, 
                                           IRChangeForRC, TopoChangeForRC, 
                                           TEEventQueue, DAGEventQueue, 
                                           DAGQueue, DAGID, MaxDAGID, DAGState, 
                                           nxtRCIRID, idWorkerWorkingOnDAG, 
                                           IRDoneSet, idThreadWorkingOnIR, 
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
                                           IRStatusNIB, SwSuspensionStatusNIB, 
                                           IRQueueNIB, SetScheduledIRs, 
                                           X2NIB_len, NIBThreadID, RCThreadID, 
                                           ingressPkt, ingressIR, egressMsg, 
                                           ofaInMsg, ofaOutConfirmation, 
                                           installerInIR, statusMsg, 
                                           notFailedSet, failedElem, obj, 
                                           failedSet, statusResolveMsg, 
                                           recoveredElem, value_, nextTrans_, 
                                           value_N, rowRemove_, IR2Remove_, 
                                           send_NIB_back_, stepOfFailure_, 
                                           IRIndex_, debug_, nextTrans, value, 
                                           rowRemove_N, IR2Remove, 
                                           send_NIB_back, stepOfFailure_N, 
                                           IRIndex, debug_N, NIBMsg_, 
                                           isBootStrap_, sw_id, transaction_, 
                                           topoChangeEvent, currSetDownSw, 
                                           prev_dag_id, init, nxtDAG, 
                                           setRemovableIRs, currIR, 
                                           currIRInDAG, nxtDAGVertices, 
                                           setIRsInDAG, prev_dag, 
                                           toBeScheduledIRs, nextIR, 
                                           transaction_c, stepOfFailure_c, 
                                           currDAG, IRSet, key, op1_, op2, 
                                           debug, transaction_O, IRQueueTmp, 
                                           NIBMsg_O, isBootStrap, localIRSet, 
                                           NIBIRSet, newIRSet, newIR, 
                                           nextIRToSent, rowIndex, rowRemove, 
                                           stepOfFailure_co, transaction_co, 
                                           NIBMsg, op1, IRQueue, 
                                           op_ir_status_change_, removeIR, 
                                           monitoringEvent, setIRsToReset, 
                                           resetIR, stepOfFailure, 
                                           transaction_con, topo_change, irID, 
                                           removedIR, msg, op_ir_status_change, 
                                           op_first_install, transaction >>

controllerWorkerThreads(self) == OFCThreadGetNextIR(self)
                                    \/ OFCThreadSendIR(self)
                                    \/ OFCThreadNotifyNIBIRSent(self)
                                    \/ ControllerThreadForwardIRInner(self)
                                    \/ OFCRemoveIRFromIRQueueOFCLocal(self)
                                    \/ OFCRemoveIRFromIRQueueRemote(self)
                                    \/ OFCWorkerFailover(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ controllerIsMaster(self[1])
                                    /\ moduleIsUp(self)
                                    /\ swSeqChangedStatus # <<>>
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ monitoringEvent' = [monitoringEvent EXCEPT ![self] = Head(swSeqChangedStatus)]
                                    /\ IF shouldSuspendSw(monitoringEvent'[self]) /\ SwSuspensionStatusOFC[monitoringEvent'[self].swID] = SW_RUN
                                          THEN /\ pc' = [pc EXCEPT ![self] = "OFCSuspendSWLocally"]
                                          ELSE /\ Assert(FALSE, 
                                                         "Failure of assertion at line 2550, column 13.")
                                               /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    /\ UNCHANGED << switchLock, controllerLock, 
                                                    FirstInstallOFC, 
                                                    FirstInstallNIB, 
                                                    sw_fail_ordering_var, 
                                                    ContProcSet, SwProcSet, 
                                                    irTypeMapping, 
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
                                                    dependencyGraph, ir2sw, 
                                                    NIBUpdateForRC, 
                                                    controllerStateRC, 
                                                    IRStatusRC, 
                                                    SwSuspensionStatusRC, 
                                                    IRQueueRC, 
                                                    SetScheduledIRsRC, 
                                                    FlagRCNIBEventHandlerFailover, 
                                                    FlagRCSequencerFailover, 
                                                    RC_READY, IRChangeForRC, 
                                                    TopoChangeForRC, 
                                                    TEEventQueue, 
                                                    DAGEventQueue, DAGQueue, 
                                                    DAGID, MaxDAGID, DAGState, 
                                                    nxtRCIRID, 
                                                    idWorkerWorkingOnDAG, 
                                                    IRDoneSet, 
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
                                                    IRStatusNIB, 
                                                    SwSuspensionStatusNIB, 
                                                    IRQueueNIB, 
                                                    SetScheduledIRs, X2NIB_len, 
                                                    NIBThreadID, RCThreadID, 
                                                    ingressPkt, ingressIR, 
                                                    egressMsg, ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    obj, failedSet, 
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
                                                    debug_N, NIBMsg_, 
                                                    isBootStrap_, sw_id, 
                                                    transaction_, 
                                                    topoChangeEvent, 
                                                    currSetDownSw, prev_dag_id, 
                                                    init, nxtDAG, 
                                                    setRemovableIRs, currIR, 
                                                    currIRInDAG, 
                                                    nxtDAGVertices, 
                                                    setIRsInDAG, prev_dag, 
                                                    toBeScheduledIRs, nextIR, 
                                                    transaction_c, 
                                                    stepOfFailure_c, currDAG, 
                                                    IRSet, key, op1_, op2, 
                                                    debug, transaction_O, 
                                                    IRQueueTmp, NIBMsg_O, 
                                                    isBootStrap, localIRSet, 
                                                    NIBIRSet, newIRSet, newIR, 
                                                    nextIRToSent, rowIndex, 
                                                    rowRemove, 
                                                    stepOfFailure_co, 
                                                    transaction_co, NIBMsg, 
                                                    op1, IRQueue, 
                                                    op_ir_status_change_, 
                                                    removeIR, setIRsToReset, 
                                                    resetIR, stepOfFailure, 
                                                    transaction_con, 
                                                    topo_change, irID, 
                                                    removedIR, msg, 
                                                    op_ir_status_change, 
                                                    op_first_install, 
                                                    transaction >>

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
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
                                                                   FirstInstallOFC, 
                                                                   FirstInstallNIB, 
                                                                   sw_fail_ordering_var, 
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   irTypeMapping, 
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
                                                                   dependencyGraph, 
                                                                   ir2sw, 
                                                                   NIBUpdateForRC, 
                                                                   controllerStateRC, 
                                                                   IRStatusRC, 
                                                                   SwSuspensionStatusRC, 
                                                                   IRQueueRC, 
                                                                   SetScheduledIRsRC, 
                                                                   FlagRCNIBEventHandlerFailover, 
                                                                   FlagRCSequencerFailover, 
                                                                   RC_READY, 
                                                                   IRChangeForRC, 
                                                                   TopoChangeForRC, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   DAGID, 
                                                                   MaxDAGID, 
                                                                   DAGState, 
                                                                   nxtRCIRID, 
                                                                   idWorkerWorkingOnDAG, 
                                                                   IRDoneSet, 
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
                                                                   OFC_READY, 
                                                                   NIB2OFC, 
                                                                   NIB2RC, 
                                                                   X2NIB, 
                                                                   OFC2NIB, 
                                                                   RC2NIB, 
                                                                   FlagNIBFailover, 
                                                                   FlagNIBRCEventhandlerFailover, 
                                                                   FlagNIBOFCEventhandlerFailover, 
                                                                   NIB_READY_FOR_RC, 
                                                                   NIB_READY_FOR_OFC, 
                                                                   masterState, 
                                                                   IRStatusNIB, 
                                                                   SwSuspensionStatusNIB, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
                                                                   X2NIB_len, 
                                                                   NIBThreadID, 
                                                                   RCThreadID, 
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
                                                                   value_, 
                                                                   nextTrans_, 
                                                                   value_N, 
                                                                   rowRemove_, 
                                                                   IR2Remove_, 
                                                                   send_NIB_back_, 
                                                                   stepOfFailure_, 
                                                                   IRIndex_, 
                                                                   debug_, 
                                                                   nextTrans, 
                                                                   value, 
                                                                   rowRemove_N, 
                                                                   IR2Remove, 
                                                                   send_NIB_back, 
                                                                   stepOfFailure_N, 
                                                                   IRIndex, 
                                                                   debug_N, 
                                                                   NIBMsg_, 
                                                                   isBootStrap_, 
                                                                   sw_id, 
                                                                   transaction_, 
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
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   transaction_c, 
                                                                   stepOfFailure_c, 
                                                                   currDAG, 
                                                                   IRSet, key, 
                                                                   op1_, op2, 
                                                                   debug, 
                                                                   transaction_O, 
                                                                   IRQueueTmp, 
                                                                   NIBMsg_O, 
                                                                   isBootStrap, 
                                                                   localIRSet, 
                                                                   NIBIRSet, 
                                                                   newIRSet, 
                                                                   newIR, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_co, 
                                                                   transaction_co, 
                                                                   NIBMsg, op1, 
                                                                   IRQueue, 
                                                                   op_ir_status_change_, 
                                                                   removeIR, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   transaction_con, 
                                                                   topo_change, 
                                                                   irID, 
                                                                   removedIR, 
                                                                   msg, 
                                                                   op_ir_status_change, 
                                                                   op_first_install, 
                                                                   transaction >>

OFCSuspendSWLocally(self) == /\ pc[self] = "OFCSuspendSWLocally"
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
                                   THEN /\ SwSuspensionStatusOFC' = [SwSuspensionStatusOFC EXCEPT ![monitoringEvent[self].swID] = SW_SUSPEND]
                                        /\ pc' = [pc EXCEPT ![self] = "OFCSuspendSWRemotely"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                        /\ UNCHANGED SwSuspensionStatusOFC
                             /\ UNCHANGED << switchLock, controllerLock, 
                                             FirstInstallOFC, FirstInstallNIB, 
                                             sw_fail_ordering_var, ContProcSet, 
                                             SwProcSet, irTypeMapping, 
                                             swSeqChangedStatus, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             switchOrdering, dependencyGraph, 
                                             ir2sw, NIBUpdateForRC, 
                                             controllerStateRC, IRStatusRC, 
                                             SwSuspensionStatusRC, IRQueueRC, 
                                             SetScheduledIRsRC, 
                                             FlagRCNIBEventHandlerFailover, 
                                             FlagRCSequencerFailover, RC_READY, 
                                             IRChangeForRC, TopoChangeForRC, 
                                             TEEventQueue, DAGEventQueue, 
                                             DAGQueue, DAGID, MaxDAGID, 
                                             DAGState, nxtRCIRID, 
                                             idWorkerWorkingOnDAG, IRDoneSet, 
                                             idThreadWorkingOnIR, 
                                             workerThreadRanking, 
                                             controllerStateOFC, IRStatusOFC, 
                                             IRQueueOFC, SetScheduledIRsOFC, 
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
                                             controllerStateNIB, IRStatusNIB, 
                                             SwSuspensionStatusNIB, IRQueueNIB, 
                                             SetScheduledIRs, X2NIB_len, 
                                             NIBThreadID, RCThreadID, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             installerInIR, statusMsg, 
                                             notFailedSet, failedElem, obj, 
                                             failedSet, statusResolveMsg, 
                                             recoveredElem, value_, nextTrans_, 
                                             value_N, rowRemove_, IR2Remove_, 
                                             send_NIB_back_, stepOfFailure_, 
                                             IRIndex_, debug_, nextTrans, 
                                             value, rowRemove_N, IR2Remove, 
                                             send_NIB_back, stepOfFailure_N, 
                                             IRIndex, debug_N, NIBMsg_, 
                                             isBootStrap_, sw_id, transaction_, 
                                             topoChangeEvent, currSetDownSw, 
                                             prev_dag_id, init, nxtDAG, 
                                             setRemovableIRs, currIR, 
                                             currIRInDAG, nxtDAGVertices, 
                                             setIRsInDAG, prev_dag, 
                                             toBeScheduledIRs, nextIR, 
                                             transaction_c, stepOfFailure_c, 
                                             currDAG, IRSet, key, op1_, op2, 
                                             debug, transaction_O, IRQueueTmp, 
                                             NIBMsg_O, isBootStrap, localIRSet, 
                                             NIBIRSet, newIRSet, newIR, 
                                             nextIRToSent, rowIndex, rowRemove, 
                                             stepOfFailure_co, transaction_co, 
                                             NIBMsg, op1, IRQueue, 
                                             op_ir_status_change_, removeIR, 
                                             monitoringEvent, setIRsToReset, 
                                             resetIR, stepOfFailure, 
                                             transaction_con, topo_change, 
                                             irID, removedIR, msg, 
                                             op_ir_status_change, 
                                             op_first_install, transaction >>

OFCSuspendSWRemotely(self) == /\ pc[self] = "OFCSuspendSWRemotely"
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
                                    THEN /\ isNIBUp(NIBThreadID)
                                         /\ topo_change' = [topo_change EXCEPT ![self] = [table |-> NIBT_SW_STATUS, key |-> monitoringEvent[self].swID, value |-> SW_SUSPEND]]
                                         /\ transaction_con' = [transaction_con EXCEPT ![self] = [name |-> "SwitchDown", ops |-> <<topo_change'[self]>>]]
                                         /\ OFC2NIB' = OFC2NIB \o <<transaction_con'[self]>>
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerStateReconciliation"]
                                         /\ UNCHANGED << OFC2NIB, 
                                                         transaction_con, 
                                                         topo_change >>
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              FirstInstallOFC, FirstInstallNIB, 
                                              sw_fail_ordering_var, 
                                              ContProcSet, SwProcSet, 
                                              irTypeMapping, 
                                              swSeqChangedStatus, 
                                              controller2Switch, 
                                              switch2Controller, switchStatus, 
                                              installedIRs, NicAsic2OfaBuff, 
                                              Ofa2NicAsicBuff, 
                                              Installer2OfaBuff, 
                                              Ofa2InstallerBuff, TCAM, 
                                              controlMsgCounter, 
                                              RecoveryStatus, switchOrdering, 
                                              dependencyGraph, ir2sw, 
                                              NIBUpdateForRC, 
                                              controllerStateRC, IRStatusRC, 
                                              SwSuspensionStatusRC, IRQueueRC, 
                                              SetScheduledIRsRC, 
                                              FlagRCNIBEventHandlerFailover, 
                                              FlagRCSequencerFailover, 
                                              RC_READY, IRChangeForRC, 
                                              TopoChangeForRC, TEEventQueue, 
                                              DAGEventQueue, DAGQueue, DAGID, 
                                              MaxDAGID, DAGState, nxtRCIRID, 
                                              idWorkerWorkingOnDAG, IRDoneSet, 
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
                                              NIB2RC, X2NIB, RC2NIB, 
                                              FlagNIBFailover, 
                                              FlagNIBRCEventhandlerFailover, 
                                              FlagNIBOFCEventhandlerFailover, 
                                              NIB_READY_FOR_RC, 
                                              NIB_READY_FOR_OFC, masterState, 
                                              controllerStateNIB, IRStatusNIB, 
                                              SwSuspensionStatusNIB, 
                                              IRQueueNIB, SetScheduledIRs, 
                                              X2NIB_len, NIBThreadID, 
                                              RCThreadID, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj, 
                                              failedSet, statusResolveMsg, 
                                              recoveredElem, value_, 
                                              nextTrans_, value_N, rowRemove_, 
                                              IR2Remove_, send_NIB_back_, 
                                              stepOfFailure_, IRIndex_, debug_, 
                                              nextTrans, value, rowRemove_N, 
                                              IR2Remove, send_NIB_back, 
                                              stepOfFailure_N, IRIndex, 
                                              debug_N, NIBMsg_, isBootStrap_, 
                                              sw_id, transaction_, 
                                              topoChangeEvent, currSetDownSw, 
                                              prev_dag_id, init, nxtDAG, 
                                              setRemovableIRs, currIR, 
                                              currIRInDAG, nxtDAGVertices, 
                                              setIRsInDAG, prev_dag, 
                                              toBeScheduledIRs, nextIR, 
                                              transaction_c, stepOfFailure_c, 
                                              currDAG, IRSet, key, op1_, op2, 
                                              debug, transaction_O, IRQueueTmp, 
                                              NIBMsg_O, isBootStrap, 
                                              localIRSet, NIBIRSet, newIRSet, 
                                              newIR, nextIRToSent, rowIndex, 
                                              rowRemove, stepOfFailure_co, 
                                              transaction_co, NIBMsg, op1, 
                                              IRQueue, op_ir_status_change_, 
                                              removeIR, monitoringEvent, 
                                              setIRsToReset, resetIR, 
                                              stepOfFailure, irID, removedIR, 
                                              msg, op_ir_status_change, 
                                              op_first_install, transaction >>

ControllerEventHandlerStateReconciliation(self) == /\ pc[self] = "ControllerEventHandlerStateReconciliation"
                                                   /\ controllerIsMaster(self[1])
                                                   /\ moduleIsUp(self)
                                                   /\ swSeqChangedStatus # <<>>
                                                   /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                   /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                   /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                                   /\ IF (controllerStateNIB[self].type = START_RESET_IR)
                                                         THEN /\ SwSuspensionStatusOFC' = [SwSuspensionStatusOFC EXCEPT ![controllerStateNIB[self].sw] = SW_SUSPEND]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED SwSuspensionStatusOFC
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]
                                                   /\ UNCHANGED << switchLock, 
                                                                   FirstInstallOFC, 
                                                                   FirstInstallNIB, 
                                                                   sw_fail_ordering_var, 
                                                                   ContProcSet, 
                                                                   SwProcSet, 
                                                                   irTypeMapping, 
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
                                                                   dependencyGraph, 
                                                                   ir2sw, 
                                                                   NIBUpdateForRC, 
                                                                   controllerStateRC, 
                                                                   IRStatusRC, 
                                                                   SwSuspensionStatusRC, 
                                                                   IRQueueRC, 
                                                                   SetScheduledIRsRC, 
                                                                   FlagRCNIBEventHandlerFailover, 
                                                                   FlagRCSequencerFailover, 
                                                                   RC_READY, 
                                                                   IRChangeForRC, 
                                                                   TopoChangeForRC, 
                                                                   TEEventQueue, 
                                                                   DAGEventQueue, 
                                                                   DAGQueue, 
                                                                   DAGID, 
                                                                   MaxDAGID, 
                                                                   DAGState, 
                                                                   nxtRCIRID, 
                                                                   idWorkerWorkingOnDAG, 
                                                                   IRDoneSet, 
                                                                   idThreadWorkingOnIR, 
                                                                   workerThreadRanking, 
                                                                   controllerStateOFC, 
                                                                   IRStatusOFC, 
                                                                   IRQueueOFC, 
                                                                   SetScheduledIRsOFC, 
                                                                   FlagOFCWorkerFailover, 
                                                                   FlagOFCMonitorFailover, 
                                                                   FlagOFCNIBEventHandlerFailover, 
                                                                   OFCThreadID, 
                                                                   OFC_READY, 
                                                                   NIB2OFC, 
                                                                   NIB2RC, 
                                                                   X2NIB, 
                                                                   OFC2NIB, 
                                                                   RC2NIB, 
                                                                   FlagNIBFailover, 
                                                                   FlagNIBRCEventhandlerFailover, 
                                                                   FlagNIBOFCEventhandlerFailover, 
                                                                   NIB_READY_FOR_RC, 
                                                                   NIB_READY_FOR_OFC, 
                                                                   masterState, 
                                                                   controllerStateNIB, 
                                                                   IRStatusNIB, 
                                                                   SwSuspensionStatusNIB, 
                                                                   IRQueueNIB, 
                                                                   SetScheduledIRs, 
                                                                   X2NIB_len, 
                                                                   NIBThreadID, 
                                                                   RCThreadID, 
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
                                                                   value_, 
                                                                   nextTrans_, 
                                                                   value_N, 
                                                                   rowRemove_, 
                                                                   IR2Remove_, 
                                                                   send_NIB_back_, 
                                                                   stepOfFailure_, 
                                                                   IRIndex_, 
                                                                   debug_, 
                                                                   nextTrans, 
                                                                   value, 
                                                                   rowRemove_N, 
                                                                   IR2Remove, 
                                                                   send_NIB_back, 
                                                                   stepOfFailure_N, 
                                                                   IRIndex, 
                                                                   debug_N, 
                                                                   NIBMsg_, 
                                                                   isBootStrap_, 
                                                                   sw_id, 
                                                                   transaction_, 
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
                                                                   toBeScheduledIRs, 
                                                                   nextIR, 
                                                                   transaction_c, 
                                                                   stepOfFailure_c, 
                                                                   currDAG, 
                                                                   IRSet, key, 
                                                                   op1_, op2, 
                                                                   debug, 
                                                                   transaction_O, 
                                                                   IRQueueTmp, 
                                                                   NIBMsg_O, 
                                                                   isBootStrap, 
                                                                   localIRSet, 
                                                                   NIBIRSet, 
                                                                   newIRSet, 
                                                                   newIR, 
                                                                   nextIRToSent, 
                                                                   rowIndex, 
                                                                   rowRemove, 
                                                                   stepOfFailure_co, 
                                                                   transaction_co, 
                                                                   NIBMsg, op1, 
                                                                   IRQueue, 
                                                                   op_ir_status_change_, 
                                                                   removeIR, 
                                                                   monitoringEvent, 
                                                                   setIRsToReset, 
                                                                   resetIR, 
                                                                   stepOfFailure, 
                                                                   transaction_con, 
                                                                   topo_change, 
                                                                   irID, 
                                                                   removedIR, 
                                                                   msg, 
                                                                   op_ir_status_change, 
                                                                   op_first_install, 
                                                                   transaction >>

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ OFCSuspendSWLocally(self)
                                   \/ OFCSuspendSWRemotely(self)
                                   \/ ControllerEventHandlerStateReconciliation(self)

OFCMonitorCheckIfMastr(self) == /\ pc[self] = "OFCMonitorCheckIfMastr"
                                /\ switch2Controller # <<>>
                                /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                /\ controllerLock' = self
                                /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                                /\ Assert(msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY, FLOW_STAT_REPLY}, 
                                          "Failure of assertion at line 2617, column 9.")
                                /\ IF msg'[self].type \in {INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY}
                                      THEN /\ irID' = [irID EXCEPT ![self] = getIRIDForFlow(msg'[self].flow, msg'[self].type)]
                                           /\ Assert(msg'[self].from = ir2sw[irID'[self]], 
                                                     "Failure of assertion at line 2623, column 17.")
                                           /\ pc' = [pc EXCEPT ![self] = "OFCUpdateIRDone"]
                                      ELSE /\ Assert(FALSE, 
                                                     "Failure of assertion at line 2677, column 13.")
                                           /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                           /\ irID' = irID
                                /\ UNCHANGED << switchLock, FirstInstallOFC, 
                                                FirstInstallNIB, 
                                                sw_fail_ordering_var, 
                                                ContProcSet, SwProcSet, 
                                                irTypeMapping, 
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
                                                dependencyGraph, ir2sw, 
                                                NIBUpdateForRC, 
                                                controllerStateRC, IRStatusRC, 
                                                SwSuspensionStatusRC, 
                                                IRQueueRC, SetScheduledIRsRC, 
                                                FlagRCNIBEventHandlerFailover, 
                                                FlagRCSequencerFailover, 
                                                RC_READY, IRChangeForRC, 
                                                TopoChangeForRC, TEEventQueue, 
                                                DAGEventQueue, DAGQueue, DAGID, 
                                                MaxDAGID, DAGState, nxtRCIRID, 
                                                idWorkerWorkingOnDAG, 
                                                IRDoneSet, idThreadWorkingOnIR, 
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
                                                controllerStateNIB, 
                                                IRStatusNIB, 
                                                SwSuspensionStatusNIB, 
                                                IRQueueNIB, SetScheduledIRs, 
                                                X2NIB_len, NIBThreadID, 
                                                RCThreadID, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem, value_, 
                                                nextTrans_, value_N, 
                                                rowRemove_, IR2Remove_, 
                                                send_NIB_back_, stepOfFailure_, 
                                                IRIndex_, debug_, nextTrans, 
                                                value, rowRemove_N, IR2Remove, 
                                                send_NIB_back, stepOfFailure_N, 
                                                IRIndex, debug_N, NIBMsg_, 
                                                isBootStrap_, sw_id, 
                                                transaction_, topoChangeEvent, 
                                                currSetDownSw, prev_dag_id, 
                                                init, nxtDAG, setRemovableIRs, 
                                                currIR, currIRInDAG, 
                                                nxtDAGVertices, setIRsInDAG, 
                                                prev_dag, toBeScheduledIRs, 
                                                nextIR, transaction_c, 
                                                stepOfFailure_c, currDAG, 
                                                IRSet, key, op1_, op2, debug, 
                                                transaction_O, IRQueueTmp, 
                                                NIBMsg_O, isBootStrap, 
                                                localIRSet, NIBIRSet, newIRSet, 
                                                newIR, nextIRToSent, rowIndex, 
                                                rowRemove, stepOfFailure_co, 
                                                transaction_co, NIBMsg, op1, 
                                                IRQueue, op_ir_status_change_, 
                                                removeIR, monitoringEvent, 
                                                setIRsToReset, resetIR, 
                                                stepOfFailure, transaction_con, 
                                                topo_change, removedIR, 
                                                op_ir_status_change, 
                                                op_first_install, transaction >>

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
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
                                                         irTypeMapping, 
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
                                                         dependencyGraph, 
                                                         ir2sw, NIBUpdateForRC, 
                                                         controllerStateRC, 
                                                         IRStatusRC, 
                                                         SwSuspensionStatusRC, 
                                                         IRQueueRC, 
                                                         SetScheduledIRsRC, 
                                                         FlagRCNIBEventHandlerFailover, 
                                                         FlagRCSequencerFailover, 
                                                         RC_READY, 
                                                         IRChangeForRC, 
                                                         TopoChangeForRC, 
                                                         TEEventQueue, 
                                                         DAGEventQueue, 
                                                         DAGQueue, DAGID, 
                                                         MaxDAGID, DAGState, 
                                                         nxtRCIRID, 
                                                         idWorkerWorkingOnDAG, 
                                                         IRDoneSet, 
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
                                                         IRStatusNIB, 
                                                         SwSuspensionStatusNIB, 
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
                                                         failedElem, obj, 
                                                         failedSet, 
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
                                                         IRIndex, debug_N, 
                                                         NIBMsg_, isBootStrap_, 
                                                         sw_id, transaction_, 
                                                         topoChangeEvent, 
                                                         currSetDownSw, 
                                                         prev_dag_id, init, 
                                                         nxtDAG, 
                                                         setRemovableIRs, 
                                                         currIR, currIRInDAG, 
                                                         nxtDAGVertices, 
                                                         setIRsInDAG, prev_dag, 
                                                         toBeScheduledIRs, 
                                                         nextIR, transaction_c, 
                                                         stepOfFailure_c, 
                                                         currDAG, IRSet, key, 
                                                         op1_, op2, debug, 
                                                         transaction_O, 
                                                         IRQueueTmp, NIBMsg_O, 
                                                         isBootStrap, 
                                                         localIRSet, NIBIRSet, 
                                                         newIRSet, newIR, 
                                                         nextIRToSent, 
                                                         rowIndex, rowRemove, 
                                                         stepOfFailure_co, 
                                                         transaction_co, 
                                                         NIBMsg, op1, IRQueue, 
                                                         op_ir_status_change_, 
                                                         removeIR, 
                                                         monitoringEvent, 
                                                         setIRsToReset, 
                                                         resetIR, 
                                                         stepOfFailure, 
                                                         transaction_con, 
                                                         topo_change, irID, 
                                                         removedIR, msg, 
                                                         op_ir_status_change, 
                                                         op_first_install, 
                                                         transaction >>

OFCUpdateIRDone(self) == /\ pc[self] = "OFCUpdateIRDone"
                         /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                         /\ switchLock = <<NO_LOCK, NO_LOCK>>
                         /\ IF isOFCFailed(self)
                               THEN /\ FlagOFCMonitorFailover' = TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "OFCMonitorFailover"]
                                    /\ UNCHANGED << FirstInstallOFC, 
                                                    IRStatusOFC >>
                               ELSE /\ IRStatusOFC' = [IRStatusOFC EXCEPT ![irID[self]] = IR_DONE]
                                    /\ FirstInstallOFC' = [FirstInstallOFC EXCEPT ![irID[self]] = 1]
                                    /\ pc' = [pc EXCEPT ![self] = "OFCUpdateNIBIRDONE"]
                                    /\ UNCHANGED FlagOFCMonitorFailover
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         ir2sw, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         SwSuspensionStatusRC, IRQueueRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         IRChangeForRC, TopoChangeForRC, 
                                         TEEventQueue, DAGEventQueue, DAGQueue, 
                                         DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                         idWorkerWorkingOnDAG, IRDoneSet, 
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
                                         IRStatusNIB, SwSuspensionStatusNIB, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, obj, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug_N, 
                                         NIBMsg_, isBootStrap_, sw_id, 
                                         transaction_, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, 
                                         toBeScheduledIRs, nextIR, 
                                         transaction_c, stepOfFailure_c, 
                                         currDAG, IRSet, key, op1_, op2, debug, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         newIRSet, newIR, nextIRToSent, 
                                         rowIndex, rowRemove, stepOfFailure_co, 
                                         transaction_co, NIBMsg, op1, IRQueue, 
                                         op_ir_status_change_, removeIR, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, 
                                         transaction_con, topo_change, irID, 
                                         removedIR, msg, op_ir_status_change, 
                                         op_first_install, transaction >>

OFCUpdateNIBIRDONE(self) == /\ pc[self] = "OFCUpdateNIBIRDONE"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF isOFCFailed(self)
                                  THEN /\ FlagOFCMonitorFailover' = TRUE
                                       /\ pc' = [pc EXCEPT ![self] = "OFCMonitorFailover"]
                                       /\ UNCHANGED << OFC2NIB, 
                                                       op_ir_status_change, 
                                                       op_first_install, 
                                                       transaction >>
                                  ELSE /\ isNIBUp(NIBThreadID)
                                       /\ op_ir_status_change' = [op_ir_status_change EXCEPT ![self] = [table |-> NIBT_IR_STATUS, key |-> irID[self], value |-> IR_DONE]]
                                       /\ op_first_install' = [op_first_install EXCEPT ![self] = [table |-> NIBT_FIRST_INSTALL, key |-> irID[self], value |-> 1]]
                                       /\ transaction' = [transaction EXCEPT ![self] = [name |-> "FirstInstallIR",
                                                                                        ops |-> <<op_ir_status_change'[self], op_first_install'[self]>>]]
                                       /\ OFC2NIB' = OFC2NIB \o <<transaction'[self]>>
                                       /\ pc' = [pc EXCEPT ![self] = "OFCUpdateIRNone"]
                                       /\ UNCHANGED FlagOFCMonitorFailover
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, IRQueueRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            IRChangeForRC, TopoChangeForRC, 
                                            TEEventQueue, DAGEventQueue, 
                                            DAGQueue, DAGID, MaxDAGID, 
                                            DAGState, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, IRDoneSet, 
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
                                            controllerStateNIB, IRStatusNIB, 
                                            SwSuspensionStatusNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            toBeScheduledIRs, nextIR, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, IRSet, key, op1_, op2, 
                                            debug, transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_co, transaction_co, 
                                            NIBMsg, op1, IRQueue, 
                                            op_ir_status_change_, removeIR, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, 
                                            transaction_con, topo_change, irID, 
                                            removedIR, msg >>

OFCUpdateIRNone(self) == /\ pc[self] = "OFCUpdateIRNone"
                         /\ IF msg[self].type = DELETED_SUCCESSFULLY
                               THEN /\ removedIR' = [removedIR EXCEPT ![self] = getRemovedIRID(msg[self].flow)]
                                    /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                    /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                    /\ IF isOFCFailed(self)
                                          THEN /\ FlagOFCMonitorFailover' = TRUE
                                               /\ pc' = [pc EXCEPT ![self] = "OFCMonitorFailover"]
                                               /\ UNCHANGED << FirstInstallOFC, 
                                                               IRStatusOFC >>
                                          ELSE /\ IRStatusOFC' = [IRStatusOFC EXCEPT ![removedIR'[self]] = IR_NONE]
                                               /\ FirstInstallOFC' = [FirstInstallOFC EXCEPT ![removedIR'[self]] = 0]
                                               /\ pc' = [pc EXCEPT ![self] = "OFCUpdateNIBIRNone"]
                                               /\ UNCHANGED FlagOFCMonitorFailover
                               ELSE /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                    /\ UNCHANGED << FirstInstallOFC, 
                                                    IRStatusOFC, 
                                                    FlagOFCMonitorFailover, 
                                                    removedIR >>
                         /\ UNCHANGED << switchLock, controllerLock, 
                                         FirstInstallNIB, sw_fail_ordering_var, 
                                         ContProcSet, SwProcSet, irTypeMapping, 
                                         swSeqChangedStatus, controller2Switch, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, RecoveryStatus, 
                                         controllerSubmoduleFailNum, 
                                         controllerSubmoduleFailStat, 
                                         switchOrdering, dependencyGraph, 
                                         ir2sw, NIBUpdateForRC, 
                                         controllerStateRC, IRStatusRC, 
                                         SwSuspensionStatusRC, IRQueueRC, 
                                         SetScheduledIRsRC, 
                                         FlagRCNIBEventHandlerFailover, 
                                         FlagRCSequencerFailover, RC_READY, 
                                         IRChangeForRC, TopoChangeForRC, 
                                         TEEventQueue, DAGEventQueue, DAGQueue, 
                                         DAGID, MaxDAGID, DAGState, nxtRCIRID, 
                                         idWorkerWorkingOnDAG, IRDoneSet, 
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
                                         IRStatusNIB, SwSuspensionStatusNIB, 
                                         IRQueueNIB, SetScheduledIRs, 
                                         X2NIB_len, NIBThreadID, RCThreadID, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaInMsg, ofaOutConfirmation, 
                                         installerInIR, statusMsg, 
                                         notFailedSet, failedElem, obj, 
                                         failedSet, statusResolveMsg, 
                                         recoveredElem, value_, nextTrans_, 
                                         value_N, rowRemove_, IR2Remove_, 
                                         send_NIB_back_, stepOfFailure_, 
                                         IRIndex_, debug_, nextTrans, value, 
                                         rowRemove_N, IR2Remove, send_NIB_back, 
                                         stepOfFailure_N, IRIndex, debug_N, 
                                         NIBMsg_, isBootStrap_, sw_id, 
                                         transaction_, topoChangeEvent, 
                                         currSetDownSw, prev_dag_id, init, 
                                         nxtDAG, setRemovableIRs, currIR, 
                                         currIRInDAG, nxtDAGVertices, 
                                         setIRsInDAG, prev_dag, 
                                         toBeScheduledIRs, nextIR, 
                                         transaction_c, stepOfFailure_c, 
                                         currDAG, IRSet, key, op1_, op2, debug, 
                                         transaction_O, IRQueueTmp, NIBMsg_O, 
                                         isBootStrap, localIRSet, NIBIRSet, 
                                         newIRSet, newIR, nextIRToSent, 
                                         rowIndex, rowRemove, stepOfFailure_co, 
                                         transaction_co, NIBMsg, op1, IRQueue, 
                                         op_ir_status_change_, removeIR, 
                                         monitoringEvent, setIRsToReset, 
                                         resetIR, stepOfFailure, 
                                         transaction_con, topo_change, irID, 
                                         msg, op_ir_status_change, 
                                         op_first_install, transaction >>

OFCUpdateNIBIRNone(self) == /\ pc[self] = "OFCUpdateNIBIRNone"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ IF isOFCFailed(self)
                                  THEN /\ FlagOFCMonitorFailover' = TRUE
                                       /\ pc' = [pc EXCEPT ![self] = "OFCMonitorFailover"]
                                       /\ UNCHANGED << OFC2NIB, 
                                                       op_ir_status_change, 
                                                       op_first_install, 
                                                       transaction >>
                                  ELSE /\ isNIBUp(NIBThreadID)
                                       /\ op_ir_status_change' = [op_ir_status_change EXCEPT ![self] = [table |-> NIBT_IR_STATUS, key |-> removedIR[self], value |-> IR_NONE]]
                                       /\ op_first_install' = [op_first_install EXCEPT ![self] = [table |-> NIBT_FIRST_INSTALL, key |-> removedIR[self], value |-> 0]]
                                       /\ transaction' = [transaction EXCEPT ![self] =    [name |-> "FirstInstallIR",
                                                                                       ops |-> <<op_ir_status_change'[self], op_first_install'[self]>>]]
                                       /\ OFC2NIB' = OFC2NIB \o <<transaction'[self]>>
                                       /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]
                                       /\ UNCHANGED FlagOFCMonitorFailover
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, IRQueueRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            IRChangeForRC, TopoChangeForRC, 
                                            TEEventQueue, DAGEventQueue, 
                                            DAGQueue, DAGID, MaxDAGID, 
                                            DAGState, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, IRDoneSet, 
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
                                            controllerStateNIB, IRStatusNIB, 
                                            SwSuspensionStatusNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            toBeScheduledIRs, nextIR, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, IRSet, key, op1_, op2, 
                                            debug, transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_co, transaction_co, 
                                            NIBMsg, op1, IRQueue, 
                                            op_ir_status_change_, removeIR, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, 
                                            transaction_con, topo_change, irID, 
                                            removedIR, msg >>

OFCMonitorFailover(self) == /\ pc[self] = "OFCMonitorFailover"
                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                            /\ isOFCUp(OFCThreadID)
                            /\ pc' = [pc EXCEPT ![self] = "OFCMonitorCheckIfMastr"]
                            /\ UNCHANGED << switchLock, controllerLock, 
                                            FirstInstallOFC, FirstInstallNIB, 
                                            sw_fail_ordering_var, ContProcSet, 
                                            SwProcSet, irTypeMapping, 
                                            swSeqChangedStatus, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, NicAsic2OfaBuff, 
                                            Ofa2NicAsicBuff, Installer2OfaBuff, 
                                            Ofa2InstallerBuff, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            controllerSubmoduleFailNum, 
                                            controllerSubmoduleFailStat, 
                                            switchOrdering, dependencyGraph, 
                                            ir2sw, NIBUpdateForRC, 
                                            controllerStateRC, IRStatusRC, 
                                            SwSuspensionStatusRC, IRQueueRC, 
                                            SetScheduledIRsRC, 
                                            FlagRCNIBEventHandlerFailover, 
                                            FlagRCSequencerFailover, RC_READY, 
                                            IRChangeForRC, TopoChangeForRC, 
                                            TEEventQueue, DAGEventQueue, 
                                            DAGQueue, DAGID, MaxDAGID, 
                                            DAGState, nxtRCIRID, 
                                            idWorkerWorkingOnDAG, IRDoneSet, 
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
                                            controllerStateNIB, IRStatusNIB, 
                                            SwSuspensionStatusNIB, IRQueueNIB, 
                                            SetScheduledIRs, X2NIB_len, 
                                            NIBThreadID, RCThreadID, 
                                            ingressPkt, ingressIR, egressMsg, 
                                            ofaInMsg, ofaOutConfirmation, 
                                            installerInIR, statusMsg, 
                                            notFailedSet, failedElem, obj, 
                                            failedSet, statusResolveMsg, 
                                            recoveredElem, value_, nextTrans_, 
                                            value_N, rowRemove_, IR2Remove_, 
                                            send_NIB_back_, stepOfFailure_, 
                                            IRIndex_, debug_, nextTrans, value, 
                                            rowRemove_N, IR2Remove, 
                                            send_NIB_back, stepOfFailure_N, 
                                            IRIndex, debug_N, NIBMsg_, 
                                            isBootStrap_, sw_id, transaction_, 
                                            topoChangeEvent, currSetDownSw, 
                                            prev_dag_id, init, nxtDAG, 
                                            setRemovableIRs, currIR, 
                                            currIRInDAG, nxtDAGVertices, 
                                            setIRsInDAG, prev_dag, 
                                            toBeScheduledIRs, nextIR, 
                                            transaction_c, stepOfFailure_c, 
                                            currDAG, IRSet, key, op1_, op2, 
                                            debug, transaction_O, IRQueueTmp, 
                                            NIBMsg_O, isBootStrap, localIRSet, 
                                            NIBIRSet, newIRSet, newIR, 
                                            nextIRToSent, rowIndex, rowRemove, 
                                            stepOfFailure_co, transaction_co, 
                                            NIBMsg, op1, IRQueue, 
                                            op_ir_status_change_, removeIR, 
                                            monitoringEvent, setIRsToReset, 
                                            resetIR, stepOfFailure, 
                                            transaction_con, topo_change, irID, 
                                            removedIR, msg, 
                                            op_ir_status_change, 
                                            op_first_install, transaction >>

controllerMonitoringServer(self) == OFCMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ OFCUpdateIRDone(self)
                                       \/ OFCUpdateNIBIRDONE(self)
                                       \/ OFCUpdateIRNone(self)
                                       \/ OFCUpdateNIBIRNone(self)
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
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ( {"proc"} \X {NIB_FAILURE}): NIBFailureProc(self))
           \/ (\E self \in ({"proc"} \X {OFC_FAILOVER}): OFCFailoverProc(self))
           \/ (\E self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}): OFCNIBEventHandler(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
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
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ( {"proc"} \X {NIB_FAILURE}) : WF_vars(NIBFailureProc(self))
        /\ \A self \in ({"proc"} \X {OFC_FAILOVER}) : WF_vars(OFCFailoverProc(self))
        /\ \A self \in ({ofc0} \X {CONT_OFC_NIB_EVENT}) : WF_vars(OFCNIBEventHandler(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
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
CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in FINAL_DAG.v
                                                  /\ \E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x]
                                               \/ /\ x \notin FINAL_DAG.v
                                                  /\ ~\E y \in DOMAIN TCAM[ir2sw[x]]: TCAM[ir2sw[x]][y] = IR2FLOW[x])
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ IRStatusNIB[x] = IR_DONE
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
\* Only one thread is considered. Therefore the following property does not make sense.
\*IRCriticalSection == LET 
\*                        IRCriticalSet == {"ControllerThreadSendIR", "ControllerThreadForwardIR", "ControllerThreadSaveToDB2", "WaitForIRToHaveCorrectStatus", "ReScheduleifIRNone"}
\*                     IN   
\*                        \A x, y \in {ofc0} \X CONTROLLER_THREAD_POOL: \/ x = y
\*                                                                      \/ <<pc[x], pc[y]>> \notin IRCriticalSet \X IRCriticalSet
\*                                                                      \/ /\ <<pc[x], pc[y]>> \in IRCriticalSet \X IRCriticalSet
\*                                                                         /\ nextIRToSent[x] # nextIRToSent[y]

RedundantInstallation == \A x \in 1..MaxNumIRs: \/ IRStatusOFC[x] = IR_DONE
                                                \/ FirstInstallOFC[x] = 0
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
\* Last modified Thu Jul 08 16:17:22 PDT 2021 by zmy
\* Last modified Sun Feb 14 21:50:09 PST 2021 by root
\* Created Thu Nov 19 19:02:15 PST 2020 by root

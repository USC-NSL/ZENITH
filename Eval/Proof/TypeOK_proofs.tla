---- MODULE TypeOK_proofs ----
EXTENDS TLAPS, zenith, SequenceTheorems

LEMMA FunctionOfQueuesTailType == 
    ASSUME 
        NEW S, NEW T, 
        NEW f \in [S -> Seq(T)], 
        NEW s \in S, Len(f[s]) > 0,
        NEW t, t = Tail(f[s]),
        NEW g, g = [f EXCEPT ![s] = t]
    PROVE g \in [S -> Seq(T)]
    OBVIOUS 

LEMMA FunctionOfQueuesAppendType == 
    ASSUME 
        NEW S, NEW T, 
        NEW f \in [S -> Seq(T)], 
        NEW s \in S, NEW e \in T,
        NEW t, t = Append(f[s], e),
        NEW g, g = [f EXCEPT ![s] = t]
    PROVE g \in [S -> Seq(T)]
    OBVIOUS 

LEMMA FunctionExceptType ==
    ASSUME 
        NEW S, NEW T,
        NEW f \in [S -> T],
        NEW s \in S, NEW t \in T,
        NEW g, g = [f EXCEPT ![s] = t]
    PROVE g \in [S -> T]
    OBVIOUS 

LEMMA FunctionExceptUpdateAddType ==
    ASSUME 
        NEW S, NEW T,
        NEW f \in [S -> SUBSET T],
        NEW s \in S, NEW t \in T,
        NEW g, g = [f EXCEPT ![s] = f[s] \cup {t}]
    PROVE g \in [S -> SUBSET T]
    OBVIOUS 

LEMMA FunctionExceptUpdateRemoveType ==
    ASSUME 
        NEW S, NEW T,
        NEW f \in [S -> SUBSET T],
        NEW s \in S, NEW t,
        NEW g, g = [f EXCEPT ![s] = f[s] \ {t}]
    PROVE g \in [S -> SUBSET T]
    OBVIOUS 

LEMMA FunctionExceptClearType ==
    ASSUME 
        NEW S, NEW T,
        NEW f \in [S -> SUBSET T],
        NEW s \in S,
        NEW g, g = [f EXCEPT ![s] = {}]
    PROVE g \in [S -> SUBSET T]
    OBVIOUS 

LEMMA FunctionExceptNumericalUpdateType ==
    ASSUME 
        NEW S,
        NEW f \in [S -> Nat],
        NEW s \in S, NEW num \in Nat,
        NEW g, g = [f EXCEPT ![s] = f[s] + num]
    PROVE g \in [S -> Nat]
    OBVIOUS 

(* TODO: Finish this, it's trivial ... *)
LEMMA TEMessageTypeLemma == 
    \A msg \in MSG_SET_TE_EVENT: /\ msg.type = TOPO_MOD => msg \in MSG_SET_TOPO_MOD
                                 /\ msg.type = IR_MOD => msg \in MSG_SET_IR_MOD
                                 /\ msg.type = IR_FAILED => msg \in MSG_SET_IR_FAIL
    PROOF OMITTED 

LEMMA AUX_TypeOK_is_inv == Spec => []AUX_TypeOK
PROOF OMITTED

THEOREM TypeOK_inv == Spec => []TypeOK
<1> USE DEF 
    INSTALLABLE_IR_SET, SCHEDULABLE_IR_SET, ALL_IR_SET, DAG_ID_SET,
    ENUM_SET_INSTALLER_STATUS, ENUM_SET_OF_CMD, ENUM_SET_OF_ACK, ENUM_SET_SW_STATE, ENUM_SET_IR_STATE, ENUM_SET_DAG_STATE, ENUM_MODULE_STATE,
    STRUCT_SET_RC_DAG, STRUCT_SET_DAG_OBJECT, STRUCT_IR, STRUCT_IR_PAIR, STRUCT_SET_NIB_TAGGED_IR,
    MSG_SET_TIMEOUT, MSG_SET_KEEPALIVE, MSG_SET_OF_CMD, MSG_SET_OF_ACK, MSG_SET_SWITCH_EVENT, MSG_SET_TOPO_MOD, MSG_SET_IR_MOD, MSG_SET_IR_FAIL, MSG_SET_TE_EVENT, MSG_SET_DAG_STALE_NOTIF, MSG_SET_DAG_NEW_NOTIF, MSG_SET_DAG_EVENT,
    STRUCT_SET_SWITCH_OBJECT, STRUCT_SET_SWITCH_STATUS, STRUCT_RECOVERY_STATUS,
    ConstantAssumptions
<1>1 Init => TypeOK
    BY SMT, ConstantAssumptions DEF Init, TypeOK
<1>2 TypeOK /\ Next => TypeOK'
    <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK'
        OBVIOUS 
    <2>1  CASE (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
        <3> SUFFICES ASSUME \E self \in ({SW_SIMPLE_ID} \X SW): SwitchSimpleProcess(self) PROVE TypeOK'
            BY <2>1 DEF swProcess
        <3>1 PICK self \in ({SW_SIMPLE_ID} \X SW): SwitchSimpleProcess(self)
            OBVIOUS 
        <3> DEFINE sw == self[2]
        <3> USE DEF sw
        <3>2 /\ sw \in SW
             /\ Len(controller2Switch[sw]) > 0
             /\ ingressPkt' = [ingressPkt EXCEPT ![sw] = Head(controller2Switch[sw])]
             /\ controller2Switch' = [controller2Switch EXCEPT ![sw] = Tail(controller2Switch[sw])]
             /\ UNCHANGED << sw_fail_ordering_var, switchStatus, RecoveryStatus, statusMsg, switchObject, statusResolveMsg, swSeqChangedStatus, TEEventQueue, DAGEventQueue, DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, setRemovableIRs, irsToUnschedule, unschedule, irToRemove, irToAdd, irsToConnect, irToConnect, seqEvent, toBeScheduledIRs, nextIR, currDAG, IRDoneSet, irSet, pickedIR, nextIRObjectToSend, index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, AUX_IRQ_enq, AUX_IRQ_deq, AUX_C2S_enq, AUX_SEQ_sched_num, AUX_SEQ_enq >>
            BY <3>1 DEF SwitchSimpleProcess
        <3>3 /\ controller2Switch[sw] \in Seq(MSG_SET_OF_CMD)
             /\ Tail(controller2Switch[sw]) \in Seq(MSG_SET_OF_CMD)
             /\ Head(controller2Switch[sw]) \in MSG_SET_OF_CMD
            BY <3>2 DEF TypeOK
        <3> DEFINE current_msg == ingressPkt'[sw]
        <3> USE DEF current_msg
        <3>chunk1 /\ ingressPkt' \in [SW -> MSG_SET_OF_CMD \cup {NADIR_NULL}]
                  /\ controller2Switch' \in [SW -> Seq(MSG_SET_OF_CMD)]
                  /\ UNCHANGED << sw_fail_ordering_var, switchStatus, RecoveryStatus, statusMsg, switchObject, statusResolveMsg, swSeqChangedStatus, TEEventQueue, DAGEventQueue, DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, setRemovableIRs, irsToUnschedule, unschedule, irToRemove, irToAdd, irsToConnect, irToConnect, seqEvent, toBeScheduledIRs, nextIR, currDAG, IRDoneSet, irSet, pickedIR, nextIRObjectToSend, index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, AUX_IRQ_enq, AUX_IRQ_deq, AUX_C2S_enq, AUX_SEQ_sched_num, AUX_SEQ_enq >>
                  /\ current_msg \in MSG_SET_OF_CMD
            BY <3>2, <3>3, FunctionOfQueuesTailType, FunctionExceptType DEF TypeOK
        <3>install CASE current_msg.type = INSTALL_FLOW
            <4>1 /\ installedIRs' = Append(installedIRs, (current_msg.flow))
                 /\ TCAM' = [TCAM EXCEPT ![sw] = TCAM[sw] \cup {(current_msg.flow)}]
                 /\ switch2Controller' = Append(switch2Controller, ([
                                             type |-> INSTALLED_SUCCESSFULLY,
                                             from |-> sw,
                                             to |-> (current_msg.from),
                                             flow |-> (current_msg.flow)
                                         ]))
                 /\ UNCHANGED controlMsgCounter
                BY <3>1, <3>install DEF SwitchSimpleProcess
            <4>2 /\ current_msg.flow \in Nat
                 /\ current_msg.from \in {ofc0}
                 /\ [type |-> INSTALLED_SUCCESSFULLY,
                     from |-> sw,
                     to |-> (current_msg.from),
                     flow |-> (current_msg.flow)] \in MSG_SET_OF_ACK
                BY <3>chunk1
            <4>chunk1 /\ installedIRs' \in Seq(Nat)
                      /\ TCAM' \in [SW -> SUBSET Nat]
                      /\ switch2Controller' \in Seq(MSG_SET_SWITCH_EVENT)
                      /\ UNCHANGED controlMsgCounter
                BY <4>1, <4>2, FunctionExceptUpdateAddType, FunctionOfQueuesAppendType DEF TypeOK
            <4> QED BY <3>chunk1, <4>chunk1 DEF TypeOK
        <3>else CASE ~(current_msg.type = INSTALL_FLOW)
            <4>chunk1 UNCHANGED installedIRs
                BY <3>1, <3>else DEF SwitchSimpleProcess
            <4>delete CASE current_msg.type = DELETE_FLOW
                <5>1 /\ current_msg.flow \in Nat
                     /\ current_msg.from \in {ofc0}
                     /\ [type |-> DELETED_SUCCESSFULLY,
                         from |-> sw,
                         to |-> (current_msg.from),
                         flow |-> (current_msg.flow)] \in MSG_SET_OF_ACK
                    BY <3>chunk1
                <5>2 TCAM' \in [SW -> SUBSET Nat]
                    <6>1 CASE existMatchingEntryTCAM(sw, (current_msg.flow)) 
                        <7>1 TCAM' = [TCAM EXCEPT ![sw] = TCAM[sw] \ {(current_msg.flow)}]
                            BY <3>1, <3>else, <4>delete, <6>1 DEF SwitchSimpleProcess
                        <7> QED BY <5>1, <7>1, FunctionExceptUpdateRemoveType DEF TypeOK
                    <6>2 CASE ~existMatchingEntryTCAM(sw, (current_msg.flow))
                        BY <3>1, <3>else, <4>delete, <6>2 DEF SwitchSimpleProcess, TypeOK
                    <6> QED BY <6>1, <6>2
                <5>3 /\ switch2Controller' = Append(switch2Controller, ([
                            type |-> DELETED_SUCCESSFULLY,
                            from |-> sw,
                            to |-> (current_msg.from),
                            flow |-> (current_msg.flow)
                        ]))
                     /\ UNCHANGED controlMsgCounter
                <5>chunk1 /\ TCAM' \in [SW -> SUBSET Nat]
                          /\ switch2Controller' \in Seq(MSG_SET_SWITCH_EVENT)
                          /\ UNCHANGED controlMsgCounter
                    BY <5>1, <5>2, <5>3, FunctionOfQueuesAppendType DEF TypeOK
                <5> QED BY <3>chunk1, <4>chunk1, <5>chunk1 DEF TypeOK
            <4>else CASE ~(current_msg.type = DELETE_FLOW)
                <5>clear CASE current_msg.type = CLEAR_TCAM
                    <6>1 /\ current_msg.flow \in Nat
                         /\ current_msg.from \in {ofc0}
                        BY <3>chunk1
                    <6>2 /\ TCAM' = [TCAM EXCEPT ![sw] = {}]
                         /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![sw] = controlMsgCounter[sw] + 1]
                         /\ switch2Controller' = Append(
                                                     switch2Controller,
                                                     [
                                                         type |-> CLEARED_TCAM_SUCCESSFULLY,
                                                         swID |-> sw,
                                                         num |-> controlMsgCounter'[sw],
                                                         installerStatus |-> getInstallerStatus(switchStatus[sw].installer)
                                                     ]
                                                 )
                        BY <3>1, <3>else, <4>else, <5>clear DEF SwitchSimpleProcess
                    <6>chunk1 /\ TCAM' \in [SW -> SUBSET Nat]
                              /\ controlMsgCounter' \in [SW -> Nat]
                        BY <3>2, <6>2, FunctionExceptClearType, FunctionExceptNumericalUpdateType DEF TypeOK
                    <6>3 /\ switchStatus[sw].installer \in ENUM_MODULE_STATE
                         /\ getInstallerStatus(switchStatus[sw].installer) \in ENUM_SET_INSTALLER_STATUS
                        BY <3>2 DEF TypeOK, getInstallerStatus
                    <6>4 [
                            type |-> CLEARED_TCAM_SUCCESSFULLY,
                            swID |-> sw,
                            num |-> controlMsgCounter'[sw],
                            installerStatus |-> getInstallerStatus(switchStatus[sw].installer)
                        ] \in MSG_SET_KEEPALIVE
                        BY <3>2, <6>chunk1, <6>3
                    <6>chunk2 switch2Controller' \in Seq(MSG_SET_SWITCH_EVENT)
                        BY <6>2, <6>4 DEF TypeOK
                    <6> QED BY <3>chunk1, <4>chunk1, <6>chunk1, <6>chunk2 DEF TypeOK
                <5>else CASE ~(current_msg.type = CLEAR_TCAM)
                    <6>chunk1 UNCHANGED << TCAM, controlMsgCounter, switch2Controller >>
                        BY <3>1, <3>else, <4>else, <5>else DEF SwitchSimpleProcess
                    <6> QED BY <3>chunk1, <4>chunk1, <6>chunk1 DEF TypeOK
                <5> QED BY <5>clear, <5>else
            <4> QED BY <4>delete, <4>else
        <3> QED BY <3>install, <3>else
    <2>2  CASE (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
        PROOF OMITTED 
    <2>3  CASE (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
        PROOF OMITTED 
    <2>4  CASE (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
        <3>1 PICK self \in ({rc0} \X {NIB_EVENT_HANDLER}): RCSNIBEventHndlerProc(self)
            BY <2>4 DEF rcNibEventHandler
        <3>2 /\ Len(RCNIBEventQueue) > 0
             /\ nibEvent' = Head(RCNIBEventQueue)
             /\ RCNIBEventQueue' = Tail(RCNIBEventQueue)
             /\ UNCHANGED << sw_fail_ordering_var, switchStatus, installedIRs, TCAM, controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, switchObject, statusResolveMsg, swSeqChangedStatus, controller2Switch, switch2Controller, DAGEventQueue, DAGQueue, IRQueueNIB, DAGState, NIBIRStatus, SwSuspensionStatus, seqWorkerIsBusy, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, setRemovableIRs, irsToUnschedule, unschedule, irToRemove, irToAdd, irsToConnect, irToConnect, seqEvent, toBeScheduledIRs, nextIR, currDAG, IRDoneSet, irSet, pickedIR, nextIRObjectToSend, index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, AUX_IRQ_enq, AUX_IRQ_deq, AUX_C2S_enq, AUX_C2S_deq, AUX_SEQ_sched_num, AUX_SEQ_enq, AUX_SEQ_deq >>
            BY <3>1 DEF RCSNIBEventHndlerProc
        <3>chunk1 /\ nibEvent' \in MSG_SET_TE_EVENT
                  /\ RCNIBEventQueue' \in Seq(MSG_SET_TE_EVENT)
                  /\ UNCHANGED << sw_fail_ordering_var, switchStatus, installedIRs, TCAM, controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, switchObject, statusResolveMsg, swSeqChangedStatus, controller2Switch, switch2Controller, DAGEventQueue, DAGQueue, IRQueueNIB, DAGState, NIBIRStatus, SwSuspensionStatus, seqWorkerIsBusy, topoChangeEvent, currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, setRemovableIRs, irsToUnschedule, unschedule, irToRemove, irToAdd, irsToConnect, irToConnect, seqEvent, toBeScheduledIRs, nextIR, currDAG, IRDoneSet, irSet, pickedIR, nextIRObjectToSend, index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, AUX_IRQ_enq, AUX_IRQ_deq, AUX_C2S_enq, AUX_C2S_deq, AUX_SEQ_sched_num, AUX_SEQ_enq, AUX_SEQ_deq >>
            BY <3>2 DEF TypeOK
        <3>topo CASE (nibEvent'.type = TOPO_MOD)
            <4>1 nibEvent' \in MSG_SET_TOPO_MOD
                BY <3>topo, <3>chunk1, TEMessageTypeLemma
            <4>2 /\ nibEvent'.sw \in SW
                 /\ nibEvent'.state \in ENUM_SET_SW_STATE
                BY <4>1
            <4>chunk1 UNCHANGED << RCIRStatus, ScheduledIRs >>
                BY <3>1, <3>topo DEF RCSNIBEventHndlerProc
            <4>update CASE (RCSwSuspensionStatus[nibEvent'.sw] # nibEvent'.state)
                <5>1 /\ RCSwSuspensionStatus' = [RCSwSuspensionStatus EXCEPT ![nibEvent'.sw] = nibEvent'.state]
                     /\ TEEventQueue' = Append(TEEventQueue, nibEvent')
                    BY <3>1, <3>topo, <4>update DEF RCSNIBEventHndlerProc
                <5>chunk1 /\ RCSwSuspensionStatus' \in [SW -> ENUM_SET_SW_STATE]
                          /\ TEEventQueue' \in Seq(MSG_SET_TE_EVENT)
                    BY <3>chunk1, <5>1, <4>2 DEF TypeOK
                <5> QED BY <3>chunk1, <4>chunk1, <5>chunk1 DEF TypeOK
            <4>noop CASE ~(RCSwSuspensionStatus[nibEvent'.sw] # nibEvent'.state)
                <5>chunk1 UNCHANGED << TEEventQueue, RCSwSuspensionStatus >>
                    BY <3>topo, <4>noop, <3>1 DEF RCSNIBEventHndlerProc
                <5> QED BY <3>chunk1, <4>chunk1, <5>chunk1 DEF TypeOK
            <4> QED BY <4>update, <4>noop
        <3>else CASE ~(nibEvent'.type = TOPO_MOD)
            <4>chunk1 UNCHANGED << TEEventQueue, RCSwSuspensionStatus >>
                BY <3>1, <3>else DEF RCSNIBEventHndlerProc
            <4>ir CASE (nibEvent'.type = IR_MOD)
                <5>1 nibEvent' \in MSG_SET_IR_MOD
                    BY <3>else, <4>ir, <3>chunk1, TEMessageTypeLemma
                <5>update CASE (getRCIRState(nibEvent'.IR) # nibEvent'.state)
                    <6>1 ScheduledIRs' = [ScheduledIRs EXCEPT ![nibEvent'.IR] = FALSE]
                        BY <3>1, <3>else, <4>ir, <5>update DEF RCSNIBEventHndlerProc
                    <6>chunk1 ScheduledIRs' \in [SCHEDULABLE_IR_SET -> BOOLEAN]
                        BY <6>1, <5>1 DEF TypeOK
                    <6>primary CASE (isPrimary((nibEvent'.IR)))
                        <7>update CASE ((nibEvent'.state) = IR_DONE /\ RCIRStatus[(nibEvent'.IR)].dual = IR_DONE)
                            <8>1 RCIRStatus' = [RCIRStatus EXCEPT ![(nibEvent'.IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                BY <3>1, <3>else, <4>ir, <5>update, <6>primary, <7>update DEF RCSNIBEventHndlerProc
                            <8>2 [primary |-> IR_DONE, dual |-> IR_NONE] \in STRUCT_IR_PAIR
                                OBVIOUS 
                            <8>chunk1 RCIRStatus' \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]
                                BY <8>1, <8>2 DEF TypeOK
                            <8> QED BY <3>chunk1, <4>chunk1, <6>chunk1, <8>chunk1 DEF TypeOK
                        <7>noop CASE ~((nibEvent'.state) = IR_DONE /\ RCIRStatus[(nibEvent'.IR)].dual = IR_DONE)
                            <8>1 RCIRStatus' = [RCIRStatus EXCEPT ![(nibEvent'.IR)].primary = nibEvent'.state]
                                BY <3>1, <3>else, <4>ir, <5>update, <6>primary, <7>noop DEF RCSNIBEventHndlerProc
                            <8>chunk1 RCIRStatus' \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]
                                BY <5>1, <8>1 DEF TypeOK
                            <8> QED BY <3>chunk1, <4>chunk1, <6>chunk1, <8>chunk1 DEF TypeOK
                        <7> QED BY <7>update, <7>noop
                    <6>dual CASE ~(isPrimary((nibEvent'.IR)))
                        <7> DEFINE primary_of_event == getPrimaryOfIR((nibEvent'.IR))
                        <7> USE DEF primary_of_event
                        <7>1 primary_of_event \in INSTALLABLE_IR_SET
                            (* TODO: To prove this, we need an extra assumption ... *)
                            PROOF OMITTED 
                        <7>update CASE ((nibEvent'.state) = IR_DONE /\ RCIRStatus[(primary_of_event)].primary = IR_DONE)
                            <8>1 RCIRStatus' = [RCIRStatus EXCEPT ![primary_of_event] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                BY <3>1, <3>else, <4>ir, <5>update, <6>dual, <7>update DEF RCSNIBEventHndlerProc
                            <8>2 [primary |-> IR_DONE, dual |-> IR_NONE] \in STRUCT_IR_PAIR
                                OBVIOUS 
                            <8>chunk1 RCIRStatus' \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]
                                BY <8>1, <8>2, <7>1 DEF TypeOK
                            <8> QED BY <3>chunk1, <4>chunk1, <6>chunk1, <8>chunk1 DEF TypeOK
                        <7>noop CASE ~((nibEvent'.state) = IR_DONE /\ RCIRStatus[(primary_of_event)].primary = IR_DONE)
                            <8>1 RCIRStatus' = [RCIRStatus EXCEPT ![primary_of_event].dual = nibEvent'.state]
                                BY <3>1, <3>else, <4>ir, <5>update, <6>dual, <7>noop DEF RCSNIBEventHndlerProc
                            <8>chunk1 RCIRStatus' \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]
                                BY <5>1, <8>1 DEF TypeOK
                            <8> QED BY <3>chunk1, <4>chunk1, <6>chunk1, <8>chunk1 DEF TypeOK
                        <7> QED BY <7>update, <7>noop
                    <6> QED BY <6>primary, <6>dual
                <5>noop CASE ~(getRCIRState(nibEvent'.IR) # nibEvent'.state)
                    <6>chunk1 UNCHANGED << RCIRStatus, ScheduledIRs >>
                        BY <3>1, <3>else, <4>ir, <5>noop DEF RCSNIBEventHndlerProc
                    <6> QED BY <3>chunk1, <4>chunk1, <6>chunk1 DEF TypeOK
                <5> QED BY <5>update, <5>noop
            <4>else CASE ~(nibEvent'.type = IR_MOD)
                <5>1 nibEvent' \in MSG_SET_IR_FAIL
                    BY <3>chunk1, <3>else, <4>else, TEMessageTypeLemma
                <5>chunk1 UNCHANGED RCIRStatus
                    BY <3>1, <3>else, <4>else DEF RCSNIBEventHndlerProc
                <5>failed CASE (nibEvent'.type = IR_FAILED)
                    <6>1 ScheduledIRs' = [ScheduledIRs EXCEPT ![nibEvent'.IR] = FALSE]
                        BY <3>1, <3>else, <4>else, <5>failed DEF RCSNIBEventHndlerProc
                    <6>chunk1 ScheduledIRs' \in [SCHEDULABLE_IR_SET -> BOOLEAN]
                        BY <6>1, <5>1 DEF TypeOK
                    <6> QED BY <3>chunk1, <4>chunk1, <5>chunk1, <6>chunk1 DEF TypeOK
                <5>else CASE ~(nibEvent'.type = IR_FAILED)
                    <6>chunk1 UNCHANGED ScheduledIRs
                        BY <3>1, <3>else, <4>else, <5>else DEF RCSNIBEventHndlerProc
                    <6> QED BY <3>chunk1, <4>chunk1, <5>chunk1, <6>chunk1 DEF TypeOK
                <5> QED BY <5>failed, <5>else
            <4> QED BY <4>ir, <4>else
        <3> QED BY <3>topo, <3>else
    <2>5  CASE (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
    <2>6  CASE (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
    <2>7  CASE (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
    <2>8  CASE (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
    <2>9  CASE (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
    <2>10 CASE (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10 DEF Next
<1>3 TypeOK /\ UNCHANGED vars => TypeOK'
    BY DEF vars, TypeOK
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec

====
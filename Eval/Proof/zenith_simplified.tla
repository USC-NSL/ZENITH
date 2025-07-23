---- MODULE zenith_simplified ----
SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ swCanReceivePackets(self[2])
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ ingressPkt' = Head(controller2Switch[self[2]])
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ IF ingressPkt'.type = INSTALL_FLOW
                                   THEN /\ installedIRs' = Append(installedIRs, (ingressPkt'.flow))
                                        /\ TCAM' = [TCAM EXCEPT ![self[2]] = TCAM[self[2]] \cup {(ingressPkt'.flow)}]
                                        /\ switch2Controller' = Append(switch2Controller, (           [
                                                                    type |-> INSTALLED_SUCCESSFULLY,
                                                                    from |-> self[2],
                                                                    to |-> (ingressPkt'.from),
                                                                    flow |-> (ingressPkt'.flow)
                                                                ]))
                                   ELSE /\ IF ingressPkt'.type = DELETE_FLOW
                                              THEN /\ IF existMatchingEntryTCAM(self[2], (ingressPkt'.flow))
                                                         THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = TCAM[self[2]] \ {(ingressPkt'.flow)}]
                                                         ELSE /\ TRUE
                                                              /\ TCAM' = TCAM
                                                   /\ switch2Controller' = Append(switch2Controller, (           [
                                                                               type |-> DELETED_SUCCESSFULLY,
                                                                               from |-> self[2],
                                                                               to |-> (ingressPkt'.from),
                                                                               flow |-> (ingressPkt'.flow)
                                                                           ]))
                                              ELSE /\ IF ingressPkt'.type = CLEAR_TCAM
                                                         THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                              /\ switch2Controller' =                      Append(
                                                                                          switch2Controller,
                                                                                          [
                                                                                              type |-> CLEARED_TCAM_SUCCESSFULLY,
                                                                                              swID |-> self[2],
                                                                                              num |-> controlMsgCounter'[self[2]],
                                                                                              installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                                                                                          ]
                                                                                      )
                                                         ELSE /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]

swProcess(self) == SwitchSimpleProcess(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ sw_fail_ordering_var # <<>>
                       /\ \E x \in Head(sw_fail_ordering_var): x.sw = self[2]
                       /\ switchObject' = (CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2])
                       /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]].transient = switchObject'.transient,
                                                                   ![self[2]].partial = switchObject'.partial]
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{switchObject'})>> \o Tail(sw_fail_ordering_var)
                       /\ IF switchStatus[self[2]].nicAsic = NotFailed
                             THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                  /\ statusMsg' = [type |-> NIC_ASIC_DOWN,
                                                     swID |-> self[2],
                                                     num |-> controlMsgCounter'[self[2]]]
                                  /\ switch2Controller' = Append(switch2Controller, statusMsg')
                             ELSE /\ TRUE
                       /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> Failed, nicAsic |-> Failed,
                                                                               ofa |-> Failed, installer |-> Failed]]
                       /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                       /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ RecoveryStatus[self[2]].transient = 1
                              /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> NotFailed, nicAsic |-> NotFailed,
                                                                                      ofa |-> NotFailed, installer |-> NotFailed]]
                              /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                              /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                              /\ statusResolveMsg' =                     [
                                                         type |-> KEEP_ALIVE,
                                                         swID |-> self[2],
                                                         num |-> controlMsgCounter'[self[2]],
                                                         installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                     ]
                              /\ switch2Controller' = Append(switch2Controller, statusResolveMsg')
                              /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]] = [transient |-> 0, partial |-> 0]]
                              /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]

swResolveFailure(self) == SwitchResolveFailure(self)

RCSNIBEventHndlerProc(self) == /\ pc[self] = "RCSNIBEventHndlerProc"
                               /\ Len(RCNIBEventQueue) > 0
                               /\ nibEvent' = Head(RCNIBEventQueue)
                               /\ IF (nibEvent'.type = TOPO_MOD)
                                     THEN /\ IF RCSwSuspensionStatus[nibEvent'.sw] # nibEvent'.state
                                                THEN /\ RCSwSuspensionStatus' = [RCSwSuspensionStatus EXCEPT ![nibEvent'.sw] = nibEvent'.state]
                                                     /\ TEEventQueue' = Append(TEEventQueue, nibEvent')
                                                ELSE /\ TRUE
                                     ELSE /\ IF (nibEvent'.type = IR_MOD)
                                                THEN /\ IF getRCIRState(nibEvent'.IR) # nibEvent'.state
                                                           THEN /\ IF (isPrimary((nibEvent'.IR)))
                                                                      THEN /\ IF (nibEvent'.state) = IR_DONE /\ RCIRStatus[(nibEvent'.IR)].dual = IR_DONE
                                                                                 THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![(nibEvent'.IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                 ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![(nibEvent'.IR)].primary = nibEvent'.state]
                                                                      ELSE /\ LET primary == getPrimaryOfIR((nibEvent'.IR)) IN
                                                                                IF (nibEvent'.state) = IR_DONE /\ RCIRStatus[primary].primary = IR_DONE
                                                                                   THEN /\ RCIRStatus' = [RCIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                   ELSE /\ RCIRStatus' = [RCIRStatus EXCEPT ![primary].dual = nibEvent'.state]
                                                                /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![nibEvent'.IR] = FALSE]
                                                           ELSE /\ TRUE
                                                ELSE /\ IF (nibEvent'.type = IR_FAILED)
                                                           THEN /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![nibEvent'.IR] = FALSE]
                                                           ELSE /\ TRUE
                               /\ RCNIBEventQueue' = Tail(RCNIBEventQueue)
                               /\ pc' = [pc EXCEPT ![self] = "RCSNIBEventHndlerProc"]

rcNibEventHandler(self) == RCSNIBEventHndlerProc(self)

ControllerTEProc(self) == /\ pc[self] = "ControllerTEProc"
                          /\ IF init = TRUE
                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                ELSE /\ Len(TEEventQueue) > 0
                                     /\ topoChangeEvent' = Head(TEEventQueue)
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]

ControllerTEEventProcessing(self) == /\ pc[self] = "ControllerTEEventProcessing"
                                     /\ IF init # TRUE
                                           THEN /\ IF topoChangeEvent = NADIR_NULL
                                                      THEN /\ IF Len(TEEventQueue) > 0
                                                                 THEN /\ topoChangeEvent' = Head(TEEventQueue)
                                                                 ELSE /\ topoChangeEvent' = NADIR_NULL
                                                           /\ IF topoChangeEvent' = NADIR_NULL
                                                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]
                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                                      ELSE /\ IF topoChangeEvent.state = SW_SUSPEND
                                                                 THEN /\ currSetDownSw' = (currSetDownSw \cup {topoChangeEvent.sw})
                                                                 ELSE /\ currSetDownSw' = currSetDownSw \ {topoChangeEvent.sw}
                                                           /\ TEEventQueue' = Tail(TEEventQueue)
                                                           /\ topoChangeEvent' = NADIR_NULL
                                                           /\ pc' = [pc EXCEPT ![self] = "ControllerTEEventProcessing"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTEComputeDagBasedOnTopo"]

ControllerTEComputeDagBasedOnTopo(self) == /\ pc[self] = "ControllerTEComputeDagBasedOnTopo"
                                           /\ IF DAGID = NADIR_NULL
                                                 THEN /\ DAGID' = 1
                                                 ELSE /\ DAGID' = (DAGID % MaxDAGID) + 1
                                           /\ nxtDAG' = [id |-> DAGID', dag |-> TOPO_DAG_MAPPING[currSetDownSw]]
                                           /\ nxtDAGVertices' = nxtDAG'.dag.v
                                           /\ IF init = FALSE
                                                 THEN /\ DAGState' = [DAGState EXCEPT ![prev_dag_id] = DAG_STALE]
                                                      /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_STALE, id |-> prev_dag_id]))
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerTEWaitForStaleDAGToBeRemoved"]
                                                 ELSE /\ init' = FALSE
                                                      /\ prev_dag_id' = DAGID'
                                                      /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]

ControllerTEWaitForStaleDAGToBeRemoved(self) == /\ pc[self] = "ControllerTEWaitForStaleDAGToBeRemoved"
                                                /\ DAGState[prev_dag_id] = DAG_NONE
                                                /\ prev_dag_id' = DAGID
                                                /\ setRemovableIRs' = getSetRemovableIRs(SW \ currSetDownSw, nxtDAGVertices)
                                                /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]

ControllerTERemoveUnnecessaryIRs(self) == /\ pc[self] = "ControllerTERemoveUnnecessaryIRs"
                                          /\ IF Cardinality(setRemovableIRs) > 0
                                                THEN /\ irToRemove' = (CHOOSE x \in setRemovableIRs: TRUE)
                                                     /\ setRemovableIRs' = setRemovableIRs \ {irToRemove'}
                                                     /\ irToAdd' = getDualOfIR(irToRemove')
                                                     /\ irsToConnect' = getSetIRsForSwitchInDAG(getSwitchForIR(irToRemove'), nxtDAG.dag.v)
                                                     /\ nxtDAG' = [nxtDAG EXCEPT !.dag.v = nxtDAG.dag.v \cup {irToAdd'}]
                                                     /\ pc' = [pc EXCEPT ![self] = "ConnectEdges"]
                                                ELSE /\ irsToUnschedule' = nxtDAG.dag.v
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerUnscheduleIRsInDAG"]

ConnectEdges(self) == /\ pc[self] = "ConnectEdges"
                      /\ IF Cardinality(irsToConnect) > 0
                            THEN /\ irToConnect' = (CHOOSE x \in irsToConnect: TRUE)
                                 /\ irsToConnect' = irsToConnect \ {irToConnect'}
                                 /\ nxtDAG' = [nxtDAG EXCEPT !.dag.e = nxtDAG.dag.e \cup {<<irToAdd, irToConnect'>>}]
                                 /\ pc' = [pc EXCEPT ![self] = "ConnectEdges"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTERemoveUnnecessaryIRs"]

ControllerUnscheduleIRsInDAG(self) == /\ pc[self] = "ControllerUnscheduleIRsInDAG"
                                      /\ IF Cardinality(irsToUnschedule) > 0
                                            THEN /\ unschedule' = (CHOOSE x \in irsToUnschedule: TRUE)
                                                 /\ IF (getRCIRState(unschedule') # IR_NONE)
                                                       THEN /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![unschedule'] = FALSE]
                                                       ELSE /\ TRUE
                                                 /\ irsToUnschedule' = irsToUnschedule \ {unschedule'}
                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerUnscheduleIRsInDAG"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerTESubmitNewDAG"]

ControllerTESubmitNewDAG(self) == /\ pc[self] = "ControllerTESubmitNewDAG"
                                  /\ DAGState' = [DAGState EXCEPT ![nxtDAG.id] = DAG_SUBMIT]
                                  /\ DAGEventQueue' = Append(DAGEventQueue, ([type |-> DAG_NEW, dag_obj |-> nxtDAG]))
                                  /\ pc' = [pc EXCEPT ![self] = "ControllerTEProc"]

controllerTrafficEngineering(self) == ControllerTEProc(self)
                                         \/ ControllerTEEventProcessing(self)
                                         \/ ControllerTEComputeDagBasedOnTopo(self)
                                         \/ ControllerTEWaitForStaleDAGToBeRemoved(self)
                                         \/ ControllerTERemoveUnnecessaryIRs(self)
                                         \/ ConnectEdges(self)
                                         \/ ControllerUnscheduleIRsInDAG(self)
                                         \/ ControllerTESubmitNewDAG(self)

ControllerBossSeqProc(self) == /\ pc[self] = "ControllerBossSeqProc"
                               /\ Len(DAGEventQueue) > 0
                               /\ seqEvent' = Head(DAGEventQueue)
                               /\ DAGEventQueue' = Tail(DAGEventQueue)
                               /\ IF seqEvent'.type = DAG_NEW
                                     THEN /\ DAGQueue' = Append(DAGQueue, (seqEvent'.dag_obj))
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]
                                     ELSE /\ IF seqWorkerIsBusy # FALSE
                                                THEN /\ pc' = [pc EXCEPT ![self] = "WaitForRCSeqWorkerTerminate"]
                                                ELSE /\ DAGState' = [DAGState EXCEPT ![seqEvent'.id] = DAG_NONE]
                                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]

WaitForRCSeqWorkerTerminate(self) == /\ pc[self] = "WaitForRCSeqWorkerTerminate"
                                     /\ seqWorkerIsBusy = FALSE
                                     /\ DAGState' = [DAGState EXCEPT ![seqEvent.id] = DAG_NONE]
                                     /\ pc' = [pc EXCEPT ![self] = "ControllerBossSeqProc"]

controllerBossSequencer(self) == ControllerBossSeqProc(self)
                                    \/ WaitForRCSeqWorkerTerminate(self)

ControllerWorkerSeqProc(self) == /\ pc[self] = "ControllerWorkerSeqProc"
                                 /\ Len(DAGQueue) > 0
                                 /\ currDAG' = Head(DAGQueue)
                                 /\ seqWorkerIsBusy' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]

ControllerWorkerSeqScheduleDAG(self) == /\ pc[self] = "ControllerWorkerSeqScheduleDAG"
                                        /\ IF dagObjectShouldBeProcessed(currDAG)
                                              THEN /\ toBeScheduledIRs' = getSetIRsCanBeScheduledNext(currDAG.dag)
                                                   /\ toBeScheduledIRs' # {}
                                                   /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]
                                              ELSE /\ seqWorkerIsBusy' = FALSE
                                                   /\ irSet' = currDAG.dag.v
                                                   /\ IF allIRsInDAGInstalled(currDAG.dag)
                                                         THEN /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ IF toBeScheduledIRs = {} \/ isDAGStale(currDAG.id)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                  ELSE /\ nextIR' = (CHOOSE x \in toBeScheduledIRs: TRUE)
                                       /\ LET destination == getSwitchForIR(nextIR') IN
                                            /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![nextIR'] = TRUE]
                                            /\ IF getIRType(nextIR') = INSTALL_FLOW
                                                  THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR'})
                                                  ELSE /\ IRDoneSet' = IRDoneSet \ {getDualOfIR(nextIR')}
                                            /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> nextIR', sw |-> destination]), tag |-> (getIRStructTag(destination))])
                                            /\ toBeScheduledIRs' = (toBeScheduledIRs\{nextIR'})
                                       /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]

AddDeleteDAGIRDoneSet(self) == /\ pc[self] = "AddDeleteDAGIRDoneSet"
                               /\ IF Cardinality(irSet) > 0
                                     THEN /\ pickedIR' = (CHOOSE x \in irSet: TRUE)
                                          /\ IF (getIRType(pickedIR') = INSTALL_FLOW)
                                                THEN /\ IRDoneSet' = (IRDoneSet \cup {pickedIR'})
                                                ELSE /\ IRDoneSet' = IRDoneSet \ {pickedIR'}
                                          /\ irSet' = irSet \ {pickedIR'}
                                          /\ pc' = [pc EXCEPT ![self] = "AddDeleteDAGIRDoneSet"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]

RemoveDagFromQueue(self) == /\ pc[self] = "RemoveDagFromQueue"
                            /\ DAGQueue' = Tail(DAGQueue)
                            /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ AddDeleteDAGIRDoneSet(self)
                                \/ RemoveDagFromQueue(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ ExistsItemWithTag(IRQueueNIB, self)
                          /\ index' = GetFirstItemIndexWithTag(IRQueueNIB, self)
                          /\ nextIRObjectToSend' = IRQueueNIB[index'].data
                          /\ IRQueueNIB' = [IRQueueNIB EXCEPT ![index'].tag = self]
                          /\ pc' = [pc EXCEPT ![self] = "ControllerThreadSendIR"]

ControllerThreadSendIR(self) == /\ pc[self] = "ControllerThreadSendIR"
                                /\ IF isClearIR(nextIRObjectToSend.IR)
                                      THEN /\ IF isSwitchSuspended(nextIRObjectToSend.sw)
                                                 THEN /\ IF isClearIR(nextIRObjectToSend.IR)
                                                            THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                                        type |-> CLEAR_TCAM,
                                                                                                                                                                                                        flow |-> 0,
                                                                                                                                                                                                        to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                                        from |-> self[1]
                                                                                                                                                                                                    ]))]
                                                            ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                                        type |-> getIRType(nextIRObjectToSend.IR),
                                                                                                                                                                                                        flow |-> getPrimaryOfIR(nextIRObjectToSend.IR),
                                                                                                                                                                                                        to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                                        from |-> self[1]
                                                                                                                                                                                                    ]))]
                                                 ELSE /\ TRUE
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                      ELSE /\ IF getNIBIRState(nextIRObjectToSend.IR) \in {IR_NONE, IR_SENT}
                                                 THEN /\ IF isSwitchSuspended(nextIRObjectToSend.sw)
                                                            THEN /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_FAILED, IR |-> nextIRObjectToSend.IR, state |-> IR_NONE]))
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]
                                                            ELSE /\ IF (isPrimary((nextIRObjectToSend.IR)))
                                                                       THEN /\ IF IR_SENT = IR_DONE /\ NIBIRStatus[(nextIRObjectToSend.IR)].dual = IR_DONE
                                                                                  THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend.IR)] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                                  ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![(nextIRObjectToSend.IR)].primary = IR_SENT]
                                                                       ELSE /\ LET primary == getPrimaryOfIR((nextIRObjectToSend.IR)) IN
                                                                                 IF IR_SENT = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                                                    THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                                    ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_SENT]
                                                                 /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> nextIRObjectToSend.IR, state |-> IR_SENT]))
                                                                 /\ pc' = [pc EXCEPT ![self] = "ControllerThreadForwardIR"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]

ControllerThreadForwardIR(self) == /\ pc[self] = "ControllerThreadForwardIR"
                                   /\ IF isClearIR(nextIRObjectToSend.IR)
                                         THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                     type |-> CLEAR_TCAM,
                                                                                                                                                                                     flow |-> 0,
                                                                                                                                                                                     to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                     from |-> self[1]
                                                                                                                                                                                 ]))]
                                         ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![(nextIRObjectToSend.sw)] = Append(controller2Switch[(nextIRObjectToSend.sw)], ([
                                                                                                                                                                                     type |-> getIRType(nextIRObjectToSend.IR),
                                                                                                                                                                                     flow |-> getPrimaryOfIR(nextIRObjectToSend.IR),
                                                                                                                                                                                     to |-> nextIRObjectToSend.sw,
                                                                                                                                                                                     from |-> self[1]
                                                                                                                                                                                 ]))]
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerThreadRemoveIRFromQueue"]

ControllerThreadRemoveIRFromQueue(self) == /\ pc[self] = "ControllerThreadRemoveIRFromQueue"
                                           /\ index' = GetFirstItemIndexWithTag(IRQueueNIB, self)
                                           /\ IRQueueNIB' = RemoveFromSequenceByIndex(IRQueueNIB, index')
                                           /\ pc' = [pc EXCEPT ![self] = "ControllerThread"]

controllerWorkerThreads(self) == ControllerThread(self)
                                    \/ ControllerThreadSendIR(self)
                                    \/ ControllerThreadForwardIR(self)
                                    \/ ControllerThreadRemoveIRFromQueue(self)

ControllerEventHandlerProc(self) == /\ pc[self] = "ControllerEventHandlerProc"
                                    /\ Len(swSeqChangedStatus) > 0
                                    /\ monitoringEvent' = Head(swSeqChangedStatus)
                                    /\ IF shouldSuspendRunningSw(monitoringEvent')
                                          THEN /\ pc' = [pc EXCEPT ![self] = "ControllerSuspendSW"]
                                          ELSE /\ IF shouldClearSuspendedSw(monitoringEvent')
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "ControllerRequestTCAMClear"]
                                                     ELSE /\ IF shouldFreeSuspendedSw(monitoringEvent')
                                                                THEN /\ pc' = [pc EXCEPT ![self] = "ControllerCheckIfThisIsLastEvent"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]

ControllerEvenHanlderRemoveEventFromQueue(self) == /\ pc[self] = "ControllerEvenHanlderRemoveEventFromQueue"
                                                   /\ swSeqChangedStatus' = Tail(swSeqChangedStatus)
                                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEventHandlerProc"]

ControllerSuspendSW(self) == /\ pc[self] = "ControllerSuspendSW"
                             /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent.swID] = SW_SUSPEND]
                             /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_SUSPEND]))
                             /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]

ControllerRequestTCAMClear(self) == /\ pc[self] = "ControllerRequestTCAMClear"
                                    /\ IF ~existsMonitoringEventHigherNum(monitoringEvent)
                                          THEN /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> 0, sw |-> monitoringEvent.swID]), tag |-> (getIRStructTag(monitoringEvent.swID))])
                                          ELSE /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]

ControllerCheckIfThisIsLastEvent(self) == /\ pc[self] = "ControllerCheckIfThisIsLastEvent"
                                          /\ IF ~existsMonitoringEventHigherNum(monitoringEvent)
                                                THEN /\ pc' = [pc EXCEPT ![self] = "getIRsToBeChecked"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]

getIRsToBeChecked(self) == /\ pc[self] = "getIRsToBeChecked"
                           /\ setIRsToReset' = getIRSetToReset(monitoringEvent.swID)
                           /\ IF (setIRsToReset' = {})
                                 THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]

ResetAllIRs(self) == /\ pc[self] = "ResetAllIRs"
                     /\ resetIR' = (CHOOSE x \in setIRsToReset: TRUE)
                     /\ setIRsToReset' = setIRsToReset \ {resetIR'}
                     /\ IF (isPrimary(resetIR'))
                           THEN /\ IF IR_NONE = IR_DONE /\ NIBIRStatus[resetIR'].dual = IR_DONE
                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                      ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![resetIR'].primary = IR_NONE]
                           ELSE /\ LET primary == getPrimaryOfIR(resetIR') IN
                                     IF IR_NONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                        THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                        ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_NONE]
                     /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> resetIR', state |-> IR_NONE]))
                     /\ IF setIRsToReset' = {}
                           THEN /\ pc' = [pc EXCEPT ![self] = "ControllerFreeSuspendedSW"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ResetAllIRs"]

ControllerFreeSuspendedSW(self) == /\ pc[self] = "ControllerFreeSuspendedSW"
                                   /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![monitoringEvent.swID] = SW_RUN]
                                   /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> TOPO_MOD, sw |-> monitoringEvent.swID, state |-> SW_RUN]))
                                   /\ pc' = [pc EXCEPT ![self] = "ControllerEvenHanlderRemoveEventFromQueue"]

controllerEventHandler(self) == ControllerEventHandlerProc(self)
                                   \/ ControllerEvenHanlderRemoveEventFromQueue(self)
                                   \/ ControllerSuspendSW(self)
                                   \/ ControllerRequestTCAMClear(self)
                                   \/ ControllerCheckIfThisIsLastEvent(self)
                                   \/ getIRsToBeChecked(self)
                                   \/ ResetAllIRs(self)
                                   \/ ControllerFreeSuspendedSW(self)

ControllerMonitorCheckIfMastr(self) == /\ pc[self] = "ControllerMonitorCheckIfMastr"
                                       /\ Len(switch2Controller) > 0
                                       /\ msg' = Head(switch2Controller)
                                       /\ IF msg'.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                                             THEN /\ pc' = [pc EXCEPT ![self] = "ControllerProcessIRMod"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "ForwardToEH"]

MonitoringServerRemoveFromQueue(self) == /\ pc[self] = "MonitoringServerRemoveFromQueue"
                                         /\ switch2Controller' = Tail(switch2Controller)
                                         /\ pc' = [pc EXCEPT ![self] = "ControllerMonitorCheckIfMastr"]

ControllerProcessIRMod(self) == /\ pc[self] = "ControllerProcessIRMod"
                                /\ currentIRID' = getIRIDForFlow(msg.flow, msg.type)
                                /\ IF (isPrimary(currentIRID'))
                                      THEN /\ IF IR_DONE = IR_DONE /\ NIBIRStatus[currentIRID'].dual = IR_DONE
                                                 THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIRID'] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                 ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIRID'].primary = IR_DONE]
                                      ELSE /\ LET primary == getPrimaryOfIR(currentIRID') IN
                                                IF IR_DONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                   THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                   ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_DONE]
                                /\ RCNIBEventQueue' = Append(RCNIBEventQueue, ([type |-> IR_MOD, IR |-> currentIRID', state |-> IR_DONE]))
                                /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]

ForwardToEH(self) == /\ pc[self] = "ForwardToEH"
                     /\ swSeqChangedStatus' = Append(swSeqChangedStatus, msg)
                     /\ pc' = [pc EXCEPT ![self] = "MonitoringServerRemoveFromQueue"]

controllerMonitoringServer(self) == ControllerMonitorCheckIfMastr(self)
                                       \/ MonitoringServerRemoveFromQueue(self)
                                       \/ ControllerProcessIRMod(self)
                                       \/ ForwardToEH(self)
====
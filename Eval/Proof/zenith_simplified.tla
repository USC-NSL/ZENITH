---- MODULE zenith_simplified ----
EXTENDS TLC

VARIABLES sw_fail_ordering_var, switchStatus, installedIRs, TCAM, 
          controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, 
          switchObject, statusResolveMsg, swSeqChangedStatus, 
          controller2Switch, switch2Controller, TEEventQueue, DAGEventQueue, 
          DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, 
          RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, 
          ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, 
          currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, 
          setRemovableIRs, irsToUnschedule, unschedule, seqEvent, 
          toBeScheduledIRs, nextIR, currDAG, IRDoneSet, nextIRObjectToSend, 
          index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, 
          pc

(* define statement *)
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]

swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed
swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed

existMatchingEntryTCAM(swID, flowID) == flowID \in TCAM[swID]
swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed

returnSwitchElementsNotFailed(sw) == {
    x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                   /\ x = "nicAsic"
}
returnSwitchFailedElements(sw) == {
    x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                   /\ \/ switchStatus[sw].cpu = NotFailed
                                      \/ x \notin {"ofa", "installer"}
}
getInstallerStatus(stat) == IF stat = NotFailed
                            THEN INSTALLER_UP
                            ELSE INSTALLER_DOWN

isPrimary(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN TRUE ELSE FALSE
getDualOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN IntegerAsNadirID(NadirIDAsInteger(ir) + MaxNumIRs)
                                                          ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
getPrimaryOfIR(ir) == IF NadirIDAsInteger(ir) \leq MaxNumIRs THEN ir
                                                             ELSE IntegerAsNadirID(NadirIDAsInteger(ir) - MaxNumIRs)
getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
isClearIR(idID) == IF NadirIDAsInteger(idID) = 0 THEN TRUE ELSE FALSE
getIRType(irID) == IF NadirIDAsInteger(irID) \leq MaxNumIRs THEN INSTALL_FLOW
                                          ELSE DELETE_FLOW
getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID
                                                                     ELSE IntegerAsNadirID(NadirIDAsInteger(flowID) + MaxNumIRs)

getNIBIRState(irID) == IF isPrimary(irID) THEN NIBIRStatus[irID].primary
                                          ELSE NIBIRStatus[getPrimaryOfIR(irID)].dual
getRCIRState(irID) == IF isPrimary(irID) THEN RCIRStatus[irID].primary
                                         ELSE RCIRStatus[getPrimaryOfIR(irID)].dual

getSetUnschedulableIRs(nxtDAGV) == {x \in nxtDAGV: getRCIRState(x) # IR_NONE}
getSetRemovableIRs(swSet, nxtDAGV) == {x \in 1..MaxNumIRs: /\ \/ getRCIRState(x) # IR_NONE
                                                              \/ ScheduledIRs[x] = TRUE
                                                           /\ x \notin nxtDAGV
                                                           /\ getSwitchForIR(x) \in swSet}
getSetIRsForSwitchInDAG(swID, nxtDAGV) == {x \in nxtDAGV: getSwitchForIR(x) = swID}
isDependencySatisfied(DAG, ir) == ~\E y \in DAG.v: /\ <<y, ir>> \in DAG.e
                                                   /\ getRCIRState(y) # IR_DONE
getSetIRsCanBeScheduledNext(DAG)  == {x \in DAG.v: /\ getRCIRState(x) = IR_NONE
                                                   /\ isDependencySatisfied(DAG, x)
                                                   /\ RCSwSuspensionStatus[getSwitchForIR(x)] = SW_RUN
                                                   /\ ScheduledIRs[x] = FALSE}
allIRsInDAGInstalled(DAG) == ~\E y \in DAG.v: getRCIRState(y) # IR_DONE
isDAGStale(id) == DAGState[id] # DAG_SUBMIT
isSwitchSuspended(sw) == SwSuspensionStatus[sw] = SW_SUSPEND
existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN swSeqChangedStatus: /\ swSeqChangedStatus[x].swID = monEvent.swID
                                                                                /\ swSeqChangedStatus[x].num > monEvent.num
                                                                                /\ swSeqChangedStatus[x].type # CLEARED_TCAM_SUCCESSFULLY

shouldSuspendRunningSw(monEvent) == /\ \/ monEvent.type = OFA_DOWN
                                       \/ monEvent.type = NIC_ASIC_DOWN
                                       \/ /\ monEvent.type = KEEP_ALIVE
                                          /\ monEvent.installerStatus = INSTALLER_DOWN
                                    /\ SwSuspensionStatus[monEvent.swID] = SW_RUN

shouldClearSuspendedSw(monEvent) == /\ monEvent.type = KEEP_ALIVE
                                    /\ monEvent.installerStatus = INSTALLER_UP
                                    /\ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND

shouldFreeSuspendedSw(monEvent) == /\ monEvent.type = CLEARED_TCAM_SUCCESSFULLY
                                   /\ monEvent.installerStatus = INSTALLER_UP
                                   /\ SwSuspensionStatus[monEvent.swID] = SW_SUSPEND

getIRSetToReset(SID) == {x \in 1..MaxNumIRs: /\ getSwitchForIR(x) = SID
                                             /\ getNIBIRState(x) # IR_NONE}

isFinished == \A x \in 1..MaxNumIRs: getNIBIRState(x) = IR_DONE
allIRsInDAGAreStable(DAG) == ~\E y \in DAG.v: /\ getRCIRState(y) = IR_DONE
                                              /\ \/ getRCIRState(getDualOfIR(y)) # IR_NONE
                                                 \/ ScheduledIRs[getDualOfIR(y)] = TRUE
dagObjectShouldBeProcessed(dagObject) == \/ /\ ~allIRsInDAGInstalled(dagObject.dag)
                                            /\ ~isDAGStale(dagObject.id)
                                         \/ ~allIRsInDAGAreStable(dagObject.dag)

RECURSIVE AddDeleteDAGIRDoneSet(_, _)
AddDeleteDAGIRDoneSet(irSet, doneSet) ==
    IF Cardinality(irSet) = 0
        THEN doneSet
        ELSE LET pickedIR == CHOOSE x \in irSet: TRUE
             IN IF getIRType(pickedIR) = INSTALL_FLOW
                    THEN AddDeleteDAGIRDoneSet(irSet \ {pickedIR}, doneSet \cup {pickedIR})
                    ELSE AddDeleteDAGIRDoneSet(irSet \ {pickedIR}, doneSet \ {pickedIR})

RECURSIVE _GetDependencyEdges(_, _, _)
_GetDependencyEdges(irToRemove, irsToConnect, edges) ==
    IF Cardinality(irsToConnect) = 0
        THEN edges
        ELSE LET irToConnect == CHOOSE x \in irsToConnect: TRUE
             IN _GetDependencyEdges(irToRemove, irsToConnect \ {irToConnect}, edges \cup {<<getDualOfIR(irToRemove), irToConnect>>})

GetDependencyEdges(irToRemove, irsToConnect) == _GetDependencyEdges(irToRemove, irsToConnect, {})

RECURSIVE CreateTEDAG(_, _)
CreateTEDAG(irsToRemove, dag) ==
    IF Cardinality(irsToRemove) = 0
        THEN dag
        ELSE
            LET irToRemove == CHOOSE x \in irsToRemove: TRUE
            IN CreateTEDAG(
                    irsToRemove \ {irToRemove},
                    [
                        v |-> (dag.v \cup {getDualOfIR(irToRemove)}),
                        e |-> (dag.e \cup GetDependencyEdges(
                            irToRemove,
                            getSetIRsForSwitchInDAG(getSwitchForIR(irToRemove), dag.v)
                        ))
                    ])


vars == << sw_fail_ordering_var, switchStatus, installedIRs, TCAM, 
           controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, 
           switchObject, statusResolveMsg, swSeqChangedStatus, 
           controller2Switch, switch2Controller, TEEventQueue, DAGEventQueue, 
           DAGQueue, IRQueueNIB, RCNIBEventQueue, DAGState, 
           RCSwSuspensionStatus, RCIRStatus, NIBIRStatus, SwSuspensionStatus, 
           ScheduledIRs, seqWorkerIsBusy, nibEvent, topoChangeEvent, 
           currSetDownSw, prev_dag_id, init, DAGID, nxtDAG, nxtDAGVertices, 
           setRemovableIRs, irsToUnschedule, unschedule, seqEvent, 
           toBeScheduledIRs, nextIR, currDAG, IRDoneSet, nextIRObjectToSend, 
           index, monitoringEvent, setIRsToReset, resetIR, msg, currentIRID, 
           pc >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup (({ofc0} \X {CONT_MONITOR}))

Init == (* Global variables *)
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ switchStatus =                [
                              x \in SW |-> [
                                  cpu |-> NotFailed,
                                  nicAsic |-> NotFailed,
                                  ofa |-> NotFailed,
                                  installer |-> NotFailed
                              ]
                          ]
        /\ installedIRs = <<>>
        /\ TCAM = [x \in SW |-> {}]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
        /\ ingressPkt = NADIR_NULL
        /\ statusMsg = NADIR_NULL
        /\ switchObject = NADIR_NULL
        /\ statusResolveMsg = NADIR_NULL
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ TEEventQueue = <<>>
        /\ DAGEventQueue = <<>>
        /\ DAGQueue = <<>>
        /\ IRQueueNIB = <<>>
        /\ RCNIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ ScheduledIRs = [x \in 1..2*MaxNumIRs |-> FALSE]
        /\ seqWorkerIsBusy = FALSE
        /\ nibEvent = NADIR_NULL
        /\ topoChangeEvent = NADIR_NULL
        /\ currSetDownSw = {}
        /\ prev_dag_id = NADIR_NULL
        /\ init = TRUE
        /\ DAGID = NADIR_NULL
        /\ nxtDAG = NADIR_NULL
        /\ nxtDAGVertices = {}
        /\ setRemovableIRs = {}
        /\ irsToUnschedule = {}
        /\ unschedule = NADIR_NULL
        /\ seqEvent = NADIR_NULL
        /\ toBeScheduledIRs = {}
        /\ nextIR = NADIR_NULL
        /\ currDAG = NADIR_NULL
        /\ IRDoneSet = {}
        /\ nextIRObjectToSend = NADIR_NULL
        /\ index = 0
        /\ monitoringEvent = NADIR_NULL
        /\ setIRsToReset = {}
        /\ resetIR = NADIR_NULL
        /\ msg = NADIR_NULL
        /\ currentIRID = NADIR_NULL
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

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
                                                         ELSE TRUE
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
                                          /\ nxtDAG' = [nxtDAG EXCEPT !.dag = CreateTEDAG(setRemovableIRs, nxtDAG.dag)]
                                          /\ irsToUnschedule' = nxtDAG'.dag.v
                                          /\ pc' = [pc EXCEPT ![self] = "ControllerUnscheduleIRsInDAG"]

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
                                                   /\ IF allIRsInDAGInstalled(currDAG.dag)
                                                         THEN /\ IRDoneSet' = AddDeleteDAGIRDoneSet(currDAG.dag.v, IRDoneSet)
                                                         ELSE /\ TRUE
                                                   /\ pc' = [pc EXCEPT ![self] = "RemoveDagFromQueue"]

SchedulerMechanism(self) == /\ pc[self] = "SchedulerMechanism"
                            /\ IF toBeScheduledIRs = {} \/ isDAGStale(currDAG.id)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqScheduleDAG"]
                                  ELSE /\ nextIR' = (CHOOSE x \in toBeScheduledIRs: TRUE)
                                       /\ LET destination == getSwitchForIR(nextIR') IN
                                            /\ ScheduledIRs' = [ScheduledIRs EXCEPT ![nextIR'] = TRUE]
                                            /\ IF getIRType(nextIR') = INSTALL_FLOW
                                                  THEN /\ IRDoneSet' = (IRDoneSet \cup {nextIR'})
                                                  ELSE /\ IRDoneSet' = IRDoneSet \ {getDualOfIR(nextIR')}
                                            /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> nextIR', sw |-> destination]), tag |-> NADIR_NULL])
                                            /\ toBeScheduledIRs' = (toBeScheduledIRs\{nextIR'})
                                       /\ pc' = [pc EXCEPT ![self] = "SchedulerMechanism"]

RemoveDagFromQueue(self) == /\ pc[self] = "RemoveDagFromQueue"
                            /\ DAGQueue' = Tail(DAGQueue)
                            /\ pc' = [pc EXCEPT ![self] = "ControllerWorkerSeqProc"]

controllerSequencer(self) == ControllerWorkerSeqProc(self)
                                \/ ControllerWorkerSeqScheduleDAG(self)
                                \/ SchedulerMechanism(self)
                                \/ RemoveDagFromQueue(self)

ControllerThread(self) == /\ pc[self] = "ControllerThread"
                          /\ ExistsItemWithTag(IRQueueNIB, NADIR_NULL) \/ ExistsItemWithTag(IRQueueNIB, self)
                          /\ index' = GetItemIndexWithTag(IRQueueNIB, self)
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
                                          THEN /\ IRQueueNIB' = Append(IRQueueNIB, [data |-> ([IR |-> 0, sw |-> monitoringEvent.swID]), tag |-> NADIR_NULL])
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

Next == (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
           \/ (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
           \/ (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
           \/ (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): rcNibEventHandler(self))
           \/ (\E self \in ({rc0} \X {CONT_TE}): controllerTrafficEngineering(self))
           \/ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): controllerBossSequencer(self))
           \/ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
           \/ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
           \/ (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
           \/ (\E self \in ({ofc0} \X {CONT_MONITOR}): controllerMonitoringServer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(swProcess(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(swResolveFailure(self))
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_vars(rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_vars(controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_vars(controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_vars(controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_vars(controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_vars(controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_vars(controllerMonitoringServer(self))

====
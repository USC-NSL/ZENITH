---- MODULE AbstractCore ----
EXTENDS Integers, Sequences, FiniteSets, TLC, NadirTypes, graph, dag

CONSTANTS SW
CONSTANTS core0
CONSTANTS CORE_SERVICER, CORE_HANDLER
CONSTANTS IR_NONE, IR_SENT, IR_DONE, IR_FAILED
CONSTANTS SW_RUN, SW_SUSPEND
CONSTANTS DAG_STALE, DAG_NEW, DAG_SUBMIT, DAG_NONE
CONSTANTS TOPO_MOD, IR_MOD
CONSTANTS INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM, INSTALLED_SUCCESSFULLY, DELETED_SUCCESSFULLY, CLEARED_TCAM_SUCCESSFULLY, KEEP_ALIVE
CONSTANTS NIC_ASIC_DOWN, OFA_DOWN, INSTALLER_DOWN, INSTALLER_UP
CONSTANTS MaxDAGID, MaxNumIRs
CONSTANTS IR2SW

CONSTANTS NO_LOCK, SW_SIMPLE_ID


(*--fair algorithm abstractCore
    variables 
        controllerLock = <<NO_LOCK, NO_LOCK>>,
        switchLock = <<NO_LOCK, NO_LOCK>>,

        FirstInstall = [x \in 1..2*MaxNumIRs |-> 0],

        \* The edges of the DAG to push into the network
        dependencies \in generateConnectedDAG(1..MaxNumIRs),
        DAG = [v |-> 1..MaxNumIRs, e |-> dependencies],
        
        \* Fanout queue from the controller to the switches
        controller2Switch = [x \in SW |-> <<>>],
        \* Queue of switch messages to the controller
        switch2Controller = <<>>,
        \* Queue of DAGs from applications to the controller
        DAGEventQueue = <<[dag |-> DAG, id |-> 1]>>,
        \* Queue of network updates from the controller
        NIBEventQueue = <<>>,
        
        \* Table of DAG states
        DAGState = [x \in 1..MaxDAGID |-> DAG_NONE],
        \* Table of IR states
        NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]],
        \* Table of switch states
        SwSuspensionStatus = [x \in SW |-> SW_RUN]
    define
        isPrimary(ir) == IF ir \leq MaxNumIRs THEN TRUE ELSE FALSE
        getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN ir + MaxNumIRs ELSE ir - MaxNumIRs
        getPrimaryOfIR(ir) == IF ir \leq MaxNumIRs THEN ir ELSE ir - MaxNumIRs
        getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
        isClearIR(idID) == IF idID = 0 THEN TRUE ELSE FALSE
        getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW ELSE DELETE_FLOW
        getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID ELSE flowID + MaxNumIRs
        
        getNIBIRState(irID) == IF isPrimary(irID) THEN NIBIRStatus[irID].primary
                                                  ELSE NIBIRStatus[getPrimaryOfIR(irID)].dual
        
        irListIsDone(irList) == \A index \in DOMAIN irList: (getNIBIRState(irList[index]) = IR_DONE)

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

        existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN switch2Controller: /\ switch2Controller[x].type \notin {CLEARED_TCAM_SUCCESSFULLY, INSTALL_FLOW, DELETED_SUCCESSFULLY}
                                                                                       /\ switch2Controller[x].swID = monEvent.swID
                                                                                       /\ switch2Controller[x].num > monEvent.numd
    end define

    macro controllerWaitForLockFree()
    begin
        await controllerLock \in {self, <<NO_LOCK, NO_LOCK>>};
        await switchLock = <<NO_LOCK, NO_LOCK>>;
    end macro

    macro controllerAcquireLock()
    begin
        controllerWaitForLockFree();
        controllerLock := self;
    end macro    

    macro controllerReleaseLock()
    begin
        controllerWaitForLockFree();
        controllerLock := <<NO_LOCK, NO_LOCK>>;
    end macro

    macro NadirFIFOPut(queue, object)
    begin
        queue := Append(queue, object);
    end macro;

    macro NadirFIFOGet(queue, message)
    begin
        await Len(queue) > 0;
        message := Head(queue);
        queue := Tail(queue);
    end macro;

    macro NadirFanoutFIFOPut(queue, branch, object)
    begin
        queue[branch] := Append(queue[branch], object);
    end macro;

    macro setNIBIRState(irID, state) begin
        if (isPrimary(irID)) then
            if state = IR_DONE /\ NIBIRStatus[irID].dual = IR_DONE then
                NIBIRStatus[irID] := [primary |-> IR_DONE, dual |-> IR_NONE]
            else
                NIBIRStatus[irID].primary := state
            end if;
        else
            with primary = getPrimaryOfIR(irID) do
                if state = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE then
                    NIBIRStatus[primary] := [primary |-> IR_NONE, dual |-> IR_DONE]
                else
                    NIBIRStatus[primary].dual := state
                end if;
            end with;
        end if;
    end macro;

    macro controllerSendIR(irID)
    begin
        with destination = IR2SW[irID] do
            if isClearIR(irID) then
                NadirFanoutFIFOPut(
                    controller2Switch,
                    destination,
                    [type |-> CLEAR_TCAM, flow |-> 0, to |-> destination, from |-> self[1]]);
            else
                NadirFanoutFIFOPut(
                    controller2Switch,
                    destination,
                    [type |-> getIRType(irID), flow |-> getPrimaryOfIR(irID), to |-> destination, from |-> self[1]]);
            end if;
            switchLock := <<SW_SIMPLE_ID, destination>>;
        end with;
    end macro;

    macro controllerResetSwitch(swID)
    begin
        NadirFanoutFIFOPut(
            controller2Switch,
            swID,
            [type |-> CLEAR_TCAM, flow |-> 0, to |-> swID, from |-> self[1]]
        );
        switchLock := <<SW_SIMPLE_ID, swID>>;
    end macro;

    (* Pick a DAG from the queue, get all the IRs in the correct order and send them *)
    fair process coreServicer \in ({core0} \X {CORE_SERVICER})
    variables currentDAGObject = NADIR_NULL, levels = NADIR_NULL, irListToSend = NADIR_NULL;
    begin
    CoreService:
    while TRUE do
        NadirFIFOGet(DAGEventQueue, currentDAGObject);
        DAGState[currentDAGObject.id] := DAG_SUBMIT;
        levels := GetDAGScheduleLevels(currentDAGObject.dag.v, currentDAGObject.dag.e);
        CoreSendLevels:
        while DAGState[currentDAGObject.id] # DAG_STALE /\ Len(levels) > 0 do
            irListToSend := Head(levels);
            CoreSendIRs:
            while Len(irListToSend) > 0 do
                with currentIR = Head(irListToSend) do
                    if isClearIR(currentIR) then
                        controllerSendIR(currentIR);
                    else
                        if getNIBIRState(currentIR) # IR_DONE then
                            setNIBIRState(currentIR, IR_SENT);
                            controllerSendIR(currentIR);
                        end if;
                    end if;
                    irListToSend := Tail(irListToSend);
                end with;
            end while;
            await irListIsDone(Head(levels));
            levels := Tail(levels);
        end while;
    end while;
    end process;

    (* Handle switch messages and report events to applications *)
    fair process coreHandler \in ({core0} \X {CORE_HANDLER})
    variables msg = NADIR_NULL, irSetToReset = {};
    begin
    CoreHandler:
    while TRUE do
        controllerWaitForLockFree();
        NadirFIFOGet(switch2Controller, msg);
        if msg.type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY} then
            with irID = getIRIDForFlow(msg.flow, msg.type) do
                FirstInstall[irID] := 1;
                setNIBIRState(irID, IR_DONE);
                NadirFIFOPut(
                    NIBEventQueue,
                    [type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]
                );
            end with;
        else
            if shouldSuspendRunningSw(msg) then
                SwSuspensionStatus[msg.swID] := SW_SUSPEND;
                NadirFIFOPut(
                    NIBEventQueue,
                    [type |-> TOPO_MOD, sw |-> msg.swID, state |-> SW_SUSPEND]
                );
            elsif shouldClearSuspendedSw(msg) then
                if ~existsMonitoringEventHigherNum(msg) then
                    controllerResetSwitch(msg.swID);
                end if;
            elsif shouldFreeSuspendedSw(msg) then
                if ~existsMonitoringEventHigherNum(msg) then
                    irSetToReset := getIRSetToReset(msg.swID);
                    controllerAcquireLock();
                    CoreResetIRs:
                    while Cardinality(irSetToReset) > 0 do
                        with currentIR = CHOOSE ir \in irSetToReset: TRUE do
                            setNIBIRState(currentIR, IR_NONE);
                            NadirFIFOPut(
                                NIBEventQueue,
                                [type |-> IR_MOD, IR |-> currentIR, state |-> IR_NONE]
                            );
                            irSetToReset := irSetToReset \ {currentIR};
                        end with;
                    end while;
                    SwSuspensionStatus[msg.swID] := SW_RUN;
                    NadirFIFOPut(
                        NIBEventQueue,
                        [type |-> TOPO_MOD, sw |-> msg.swID, state |-> SW_RUN]
                    );
                    controllerReleaseLock();
                end if;
            end if;
        end if;
    end while;
    end process;
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "5496985c" /\ chksum(tla) = "de49a5b4")
VARIABLES controllerLock, switchLock, FirstInstall, dependencies, DAG, 
          controller2Switch, switch2Controller, DAGEventQueue, NIBEventQueue, 
          DAGState, NIBIRStatus, SwSuspensionStatus, pc

(* define statement *)
isPrimary(ir) == IF ir \leq MaxNumIRs THEN TRUE ELSE FALSE
getDualOfIR(ir) == IF ir \leq MaxNumIRs THEN ir + MaxNumIRs ELSE ir - MaxNumIRs
getPrimaryOfIR(ir) == IF ir \leq MaxNumIRs THEN ir ELSE ir - MaxNumIRs
getSwitchForIR(ir) == IR2SW[getPrimaryOfIR(ir)]
isClearIR(idID) == IF idID = 0 THEN TRUE ELSE FALSE
getIRType(irID) == IF irID \leq MaxNumIRs THEN INSTALL_FLOW ELSE DELETE_FLOW
getIRIDForFlow(flowID, irType) == IF irType = INSTALLED_SUCCESSFULLY THEN flowID ELSE flowID + MaxNumIRs

getNIBIRState(irID) == IF isPrimary(irID) THEN NIBIRStatus[irID].primary
                                          ELSE NIBIRStatus[getPrimaryOfIR(irID)].dual

irListIsDone(irList) == \A index \in DOMAIN irList: (getNIBIRState(irList[index]) = IR_DONE)

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

existsMonitoringEventHigherNum(monEvent) == \E x \in DOMAIN switch2Controller: /\ switch2Controller[x].type \notin {CLEARED_TCAM_SUCCESSFULLY, INSTALL_FLOW, DELETED_SUCCESSFULLY}
                                                                               /\ switch2Controller[x].swID = monEvent.swID
                                                                               /\ switch2Controller[x].num > monEvent.numd

VARIABLES currentDAGObject, levels, irListToSend, msg, irSetToReset

vars == << controllerLock, switchLock, FirstInstall, dependencies, DAG, 
           controller2Switch, switch2Controller, DAGEventQueue, NIBEventQueue, 
           DAGState, NIBIRStatus, SwSuspensionStatus, pc, currentDAGObject, 
           levels, irListToSend, msg, irSetToReset >>

ProcSet == (({core0} \X {CORE_SERVICER})) \cup (({core0} \X {CORE_HANDLER}))

Init == (* Global variables *)
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ FirstInstall = [x \in 1..2*MaxNumIRs |-> 0]
        /\ dependencies \in generateConnectedDAG(1..MaxNumIRs)
        /\ DAG = [v |-> 1..MaxNumIRs, e |-> dependencies]
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ DAGEventQueue = <<[dag |-> DAG, id |-> 1]>>
        /\ NIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        (* Process coreServicer *)
        /\ currentDAGObject = [self \in ({core0} \X {CORE_SERVICER}) |-> NADIR_NULL]
        /\ levels = [self \in ({core0} \X {CORE_SERVICER}) |-> NADIR_NULL]
        /\ irListToSend = [self \in ({core0} \X {CORE_SERVICER}) |-> NADIR_NULL]
        (* Process coreHandler *)
        /\ msg = [self \in ({core0} \X {CORE_HANDLER}) |-> NADIR_NULL]
        /\ irSetToReset = [self \in ({core0} \X {CORE_HANDLER}) |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in ({core0} \X {CORE_SERVICER}) -> "CoreService"
                                        [] self \in ({core0} \X {CORE_HANDLER}) -> "CoreHandler"]

CoreService(self) == /\ pc[self] = "CoreService"
                     /\ Len(DAGEventQueue) > 0
                     /\ currentDAGObject' = [currentDAGObject EXCEPT ![self] = Head(DAGEventQueue)]
                     /\ DAGEventQueue' = Tail(DAGEventQueue)
                     /\ DAGState' = [DAGState EXCEPT ![currentDAGObject'[self].id] = DAG_SUBMIT]
                     /\ levels' = [levels EXCEPT ![self] = GetDAGScheduleLevels(currentDAGObject'[self].dag.v, currentDAGObject'[self].dag.e)]
                     /\ pc' = [pc EXCEPT ![self] = "CoreSendLevels"]
                     /\ UNCHANGED << controllerLock, switchLock, FirstInstall, 
                                     dependencies, DAG, controller2Switch, 
                                     switch2Controller, NIBEventQueue, 
                                     NIBIRStatus, SwSuspensionStatus, 
                                     irListToSend, msg, irSetToReset >>

CoreSendLevels(self) == /\ pc[self] = "CoreSendLevels"
                        /\ IF DAGState[currentDAGObject[self].id] # DAG_STALE /\ Len(levels[self]) > 0
                              THEN /\ irListToSend' = [irListToSend EXCEPT ![self] = Head(levels[self])]
                                   /\ pc' = [pc EXCEPT ![self] = "CoreSendIRs"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "CoreService"]
                                   /\ UNCHANGED irListToSend
                        /\ UNCHANGED << controllerLock, switchLock, 
                                        FirstInstall, dependencies, DAG, 
                                        controller2Switch, switch2Controller, 
                                        DAGEventQueue, NIBEventQueue, DAGState, 
                                        NIBIRStatus, SwSuspensionStatus, 
                                        currentDAGObject, levels, msg, 
                                        irSetToReset >>

CoreSendIRs(self) == /\ pc[self] = "CoreSendIRs"
                     /\ IF Len(irListToSend[self]) > 0
                           THEN /\ LET currentIR == Head(irListToSend[self]) IN
                                     /\ IF isClearIR(currentIR)
                                           THEN /\ LET destination == IR2SW[currentIR] IN
                                                     /\ IF isClearIR(currentIR)
                                                           THEN /\ controller2Switch' = [controller2Switch EXCEPT ![destination] = Append(controller2Switch[destination], ([type |-> CLEAR_TCAM, flow |-> 0, to |-> destination, from |-> self[1]]))]
                                                           ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![destination] = Append(controller2Switch[destination], ([type |-> getIRType(currentIR), flow |-> getPrimaryOfIR(currentIR), to |-> destination, from |-> self[1]]))]
                                                     /\ switchLock' = <<SW_SIMPLE_ID, destination>>
                                                /\ UNCHANGED NIBIRStatus
                                           ELSE /\ IF getNIBIRState(currentIR) # IR_DONE
                                                      THEN /\ IF (isPrimary(currentIR))
                                                                 THEN /\ IF IR_SENT = IR_DONE /\ NIBIRStatus[currentIR].dual = IR_DONE
                                                                            THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIR] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                                            ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIR].primary = IR_SENT]
                                                                 ELSE /\ LET primary == getPrimaryOfIR(currentIR) IN
                                                                           IF IR_SENT = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                                              THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                                              ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_SENT]
                                                           /\ LET destination == IR2SW[currentIR] IN
                                                                /\ IF isClearIR(currentIR)
                                                                      THEN /\ controller2Switch' = [controller2Switch EXCEPT ![destination] = Append(controller2Switch[destination], ([type |-> CLEAR_TCAM, flow |-> 0, to |-> destination, from |-> self[1]]))]
                                                                      ELSE /\ controller2Switch' = [controller2Switch EXCEPT ![destination] = Append(controller2Switch[destination], ([type |-> getIRType(currentIR), flow |-> getPrimaryOfIR(currentIR), to |-> destination, from |-> self[1]]))]
                                                                /\ switchLock' = <<SW_SIMPLE_ID, destination>>
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED << switchLock, 
                                                                           controller2Switch, 
                                                                           NIBIRStatus >>
                                     /\ irListToSend' = [irListToSend EXCEPT ![self] = Tail(irListToSend[self])]
                                /\ pc' = [pc EXCEPT ![self] = "CoreSendIRs"]
                                /\ UNCHANGED levels
                           ELSE /\ irListIsDone(Head(levels[self]))
                                /\ levels' = [levels EXCEPT ![self] = Tail(levels[self])]
                                /\ pc' = [pc EXCEPT ![self] = "CoreSendLevels"]
                                /\ UNCHANGED << switchLock, controller2Switch, 
                                                NIBIRStatus, irListToSend >>
                     /\ UNCHANGED << controllerLock, FirstInstall, 
                                     dependencies, DAG, switch2Controller, 
                                     DAGEventQueue, NIBEventQueue, DAGState, 
                                     SwSuspensionStatus, currentDAGObject, msg, 
                                     irSetToReset >>

coreServicer(self) == CoreService(self) \/ CoreSendLevels(self)
                         \/ CoreSendIRs(self)

CoreHandler(self) == /\ pc[self] = "CoreHandler"
                     /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                     /\ switchLock = <<NO_LOCK, NO_LOCK>>
                     /\ Len(switch2Controller) > 0
                     /\ msg' = [msg EXCEPT ![self] = Head(switch2Controller)]
                     /\ switch2Controller' = Tail(switch2Controller)
                     /\ IF msg'[self].type \in {DELETED_SUCCESSFULLY, INSTALLED_SUCCESSFULLY}
                           THEN /\ LET irID == getIRIDForFlow(msg'[self].flow, msg'[self].type) IN
                                     /\ FirstInstall' = [FirstInstall EXCEPT ![irID] = 1]
                                     /\ IF (isPrimary(irID))
                                           THEN /\ IF IR_DONE = IR_DONE /\ NIBIRStatus[irID].dual = IR_DONE
                                                      THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                      ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![irID].primary = IR_DONE]
                                           ELSE /\ LET primary == getPrimaryOfIR(irID) IN
                                                     IF IR_DONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                        THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                        ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_DONE]
                                     /\ NIBEventQueue' = Append(NIBEventQueue, ([type |-> IR_MOD, IR |-> irID, state |-> IR_DONE]))
                                /\ pc' = [pc EXCEPT ![self] = "CoreHandler"]
                                /\ UNCHANGED << controllerLock, switchLock, 
                                                controller2Switch, 
                                                SwSuspensionStatus, 
                                                irSetToReset >>
                           ELSE /\ IF shouldSuspendRunningSw(msg'[self])
                                      THEN /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![msg'[self].swID] = SW_SUSPEND]
                                           /\ NIBEventQueue' = Append(NIBEventQueue, ([type |-> TOPO_MOD, sw |-> msg'[self].swID, state |-> SW_SUSPEND]))
                                           /\ pc' = [pc EXCEPT ![self] = "CoreHandler"]
                                           /\ UNCHANGED << controllerLock, 
                                                           switchLock, 
                                                           controller2Switch, 
                                                           irSetToReset >>
                                      ELSE /\ IF shouldClearSuspendedSw(msg'[self])
                                                 THEN /\ IF ~existsMonitoringEventHigherNum(msg'[self])
                                                            THEN /\ controller2Switch' = [controller2Switch EXCEPT ![(msg'[self].swID)] = Append(controller2Switch[(msg'[self].swID)], ([type |-> CLEAR_TCAM, flow |-> 0, to |-> (msg'[self].swID), from |-> self[1]]))]
                                                                 /\ switchLock' = <<SW_SIMPLE_ID, (msg'[self].swID)>>
                                                            ELSE /\ TRUE
                                                                 /\ UNCHANGED << switchLock, 
                                                                                 controller2Switch >>
                                                      /\ pc' = [pc EXCEPT ![self] = "CoreHandler"]
                                                      /\ UNCHANGED << controllerLock, 
                                                                      irSetToReset >>
                                                 ELSE /\ IF shouldFreeSuspendedSw(msg'[self])
                                                            THEN /\ IF ~existsMonitoringEventHigherNum(msg'[self])
                                                                       THEN /\ irSetToReset' = [irSetToReset EXCEPT ![self] = getIRSetToReset(msg'[self].swID)]
                                                                            /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                                                            /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                                                            /\ controllerLock' = self
                                                                            /\ pc' = [pc EXCEPT ![self] = "CoreResetIRs"]
                                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "CoreHandler"]
                                                                            /\ UNCHANGED << controllerLock, 
                                                                                            irSetToReset >>
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "CoreHandler"]
                                                                 /\ UNCHANGED << controllerLock, 
                                                                                 irSetToReset >>
                                                      /\ UNCHANGED << switchLock, 
                                                                      controller2Switch >>
                                           /\ UNCHANGED << NIBEventQueue, 
                                                           SwSuspensionStatus >>
                                /\ UNCHANGED << FirstInstall, NIBIRStatus >>
                     /\ UNCHANGED << dependencies, DAG, DAGEventQueue, 
                                     DAGState, currentDAGObject, levels, 
                                     irListToSend >>

CoreResetIRs(self) == /\ pc[self] = "CoreResetIRs"
                      /\ IF Cardinality(irSetToReset[self]) > 0
                            THEN /\ LET currentIR == CHOOSE ir \in irSetToReset[self]: TRUE IN
                                      /\ IF (isPrimary(currentIR))
                                            THEN /\ IF IR_NONE = IR_DONE /\ NIBIRStatus[currentIR].dual = IR_DONE
                                                       THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIR] = [primary |-> IR_DONE, dual |-> IR_NONE]]
                                                       ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![currentIR].primary = IR_NONE]
                                            ELSE /\ LET primary == getPrimaryOfIR(currentIR) IN
                                                      IF IR_NONE = IR_DONE /\ NIBIRStatus[primary].primary = IR_DONE
                                                         THEN /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary] = [primary |-> IR_NONE, dual |-> IR_DONE]]
                                                         ELSE /\ NIBIRStatus' = [NIBIRStatus EXCEPT ![primary].dual = IR_NONE]
                                      /\ NIBEventQueue' = Append(NIBEventQueue, ([type |-> IR_MOD, IR |-> currentIR, state |-> IR_NONE]))
                                      /\ irSetToReset' = [irSetToReset EXCEPT ![self] = irSetToReset[self] \ {currentIR}]
                                 /\ pc' = [pc EXCEPT ![self] = "CoreResetIRs"]
                                 /\ UNCHANGED << controllerLock, 
                                                 SwSuspensionStatus >>
                            ELSE /\ SwSuspensionStatus' = [SwSuspensionStatus EXCEPT ![msg[self].swID] = SW_RUN]
                                 /\ NIBEventQueue' = Append(NIBEventQueue, ([type |-> TOPO_MOD, sw |-> msg[self].swID, state |-> SW_RUN]))
                                 /\ controllerLock \in {self, <<NO_LOCK, NO_LOCK>>}
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                                 /\ controllerLock' = <<NO_LOCK, NO_LOCK>>
                                 /\ pc' = [pc EXCEPT ![self] = "CoreHandler"]
                                 /\ UNCHANGED << NIBIRStatus, irSetToReset >>
                      /\ UNCHANGED << switchLock, FirstInstall, dependencies, 
                                      DAG, controller2Switch, 
                                      switch2Controller, DAGEventQueue, 
                                      DAGState, currentDAGObject, levels, 
                                      irListToSend, msg >>

coreHandler(self) == CoreHandler(self) \/ CoreResetIRs(self)

Next == (\E self \in ({core0} \X {CORE_SERVICER}): coreServicer(self))
           \/ (\E self \in ({core0} \X {CORE_HANDLER}): coreHandler(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({core0} \X {CORE_SERVICER}) : WF_vars(coreServicer(self))
        /\ \A self \in ({core0} \X {CORE_HANDLER}) : WF_vars(coreHandler(self))

\* END TRANSLATION 

====

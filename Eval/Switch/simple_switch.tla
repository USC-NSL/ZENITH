------------------- MODULE simple_switch -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants

(*--fair algorithm switch
    variables 
        switchLock = <<NO_LOCK, NO_LOCK>>,
        controllerLock = <<NO_LOCK, NO_LOCK>>,
        sw_fail_ordering_var = SW_FAIL_ORDERING,
        SwProcSet = (({SW_SIMPLE_ID} \X SW)) \cup 
                    (({SW_FAILURE_PROC} \X SW)) \cup 
                    (({SW_RESOLVE_PROC} \X SW)),
        
        \* swSeqChangedStatus = <<>>,
        controller2Switch = [x \in SW |-> <<>>],
        switch2Controller = <<>>, 
        switchStatus = [
            x \in SW |-> [
                cpu |-> NotFailed, 
                nicAsic |-> NotFailed, 
                ofa |-> NotFailed, 
                installer |-> NotFailed
            ]
        ],  
        installedIRs = <<>>,

        TCAM = [x \in SW |-> <<>>], 

        controlMsgCounter = [x \in SW |-> 0],
        RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
    
    define
        indexInSeq(seq, val) == CHOOSE i \in DOMAIN seq: seq[i] = val
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
        
        swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed 
        swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                                  /\ switchStatus[sw].ofa = NotFailed
        
        existMatchingEntryTCAM(swID, flowID) == \E x \in rangeSeq(TCAM[swID]): x = flowID
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
        
        returnSwitchElementsNotFailed(sw) == {
            x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                           /\ \/ /\ WHICH_SWITCH_MODEL[x] = SW_COMPLEX_MODEL
                                                 /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1
                                              \/ /\ WHICH_SWITCH_MODEL[x] = SW_SIMPLE_MODEL
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
    end define
    
    (*******************************************************************)
    (*                       Utils (Macros)                            *)
    (*******************************************************************)
    macro removeFromSeqSet(SeqSet, obj)
    begin
        assert obj \in Head(SeqSet);
        if Cardinality(Head(SeqSet)) = 1 then
            SeqSet := Tail(SeqSet);
        else
            SeqSet := <<(Head(SeqSet)\{obj})>> \o Tail(SeqSet);
        end if; 
    end macro
    
    (*******************************************************************)
    (*                     Switches (Macros)                           *)
    (*******************************************************************)
    macro completeFailure()
    begin
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusMsg := [type |-> NIC_ASIC_DOWN, 
                            swID |-> self[2],
                            num |-> controlMsgCounter[self[2]]];
            \* swSeqChangedStatus := Append(swSeqChangedStatus, statusMsg);
            switch2Controller := Append(switch2Controller, statusMsg);
        end if;
        
        switchStatus[self[2]] := [cpu |-> Failed, nicAsic |-> Failed, 
                                    ofa |-> Failed, installer |-> Failed];
        TCAM[self[2]] := <<>>;
        controller2Switch[self[2]] := <<>>;    
    end macro;

    macro resolveCompleteFailure()
    begin
        assert switchStatus[self[2]].cpu = Failed;
        assert switchStatus[self[2]].nicAsic = Failed;
        assert switchStatus[self[2]].ofa = Failed;
        assert switchStatus[self[2]].installer = Failed;
        
        switchStatus[self[2]] := [cpu |-> NotFailed, nicAsic |-> NotFailed, 
                                    ofa |-> NotFailed, installer |-> NotFailed];
        TCAM[self[2]] := <<>>;
        controller2Switch[self[2]] := <<>>;
        
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
        statusResolveMsg := [
            type |-> KEEP_ALIVE, 
            swID |-> self[2],
            num |-> controlMsgCounter[self[2]],
            installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
        ];  
        \* swSeqChangedStatus := Append(swSeqChangedStatus, statusResolveMsg);
        switch2Controller := Append(switch2Controller, statusResolveMsg);
    end macro;

    macro installToTCAM(newFlow)
    begin
        installedIRs := Append(installedIRs, newFlow);
        TCAM[self[2]] := Append(TCAM[self[2]], newFlow);
    end macro

    macro removeFromTCAM(flowID)
    begin
        if flowID \in rangeSeq(TCAM[self[2]]) then
            TCAM[self[2]] := removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], flowID));
        end if;
    end macro

    macro clearTCAM() begin
        TCAM[self[2]] := <<>>;
    end macro;

    macro switchSend(msg)
    begin
        assert WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL;
        switch2Controller := Append(switch2Controller, msg);
    end macro

    macro sendConfirmation(controllerID, flowID, statusType)
    begin
        switchSend([
            type |-> statusType, 
            from |-> self[2], 
            to |-> controllerID,
            flow |-> flowID
        ]);
    end macro

    \* macro sendClearConfirmation() begin
    \*     controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
    \*     swSeqChangedStatus := Append(
    \*         swSeqChangedStatus, 
    \*         [
    \*             type |-> CLEARED_TCAM_SUCCESSFULLY, 
    \*             swID |-> self[2],
    \*             num |-> controlMsgCounter[self[2]],
    \*             installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
    \*         ]
    \*     );
    \* end macro;

    macro sendClearConfirmation() begin
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
        switch2Controller := Append(
            switch2Controller, 
            [
                type |-> CLEARED_TCAM_SUCCESSFULLY, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]],
                installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
            ]
        );
    end macro;

    \* macro sendClearConfirmation(controllerID) begin
    \*     controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
    \*     switchSend([
    \*         type |-> CLEARED_TCAM_SUCCESSFULLY, 
    \*         from |-> self[2], 
    \*         to |-> controllerID,
    \*         flow |-> controlMsgCounter[self[2]]
    \*     ]);
    \* end macro;

    macro sendFlowStatReplyNotFound(controllerID, flowID)
    begin
        switchSend([
            type |-> FLOW_STAT_REPLY, 
            from |-> self[2], 
            to |-> controllerID, 
            status |-> NO_ENTRY
        ]);
    end macro

    macro sendFlowStatReplyEntryFound(controllerID, flowID)
    begin
        switchSend([
            type |-> FLOW_STAT_REPLY, 
            from |-> self[2], 
            to |-> controllerID,
            status |-> ENTRY_FOUND
        ]); 
    end macro

    macro sendFlowStatReplyAllEntries(controllerID)
    begin 
        switchSend([
            type |-> FLOW_STAT_REPLY, 
            from |-> self[2], 
            to |-> controllerID,
            flows |-> rangeSeq(TCAM[self[2]])
        ]);
    end macro
    
    (*******************************************************************)
    (*                     LOCK System (Macros)                        *)
    (*******************************************************************)

    macro switchWaitForLock()
    begin     
        await controllerLock = <<NO_LOCK, NO_LOCK>>; 
        await switchLock \in {<<NO_LOCK, NO_LOCK>>, self};
    end macro;

    macro switchAcquireLock()
    begin
        switchWaitForLock();
        switchLock := self;
    end macro;

    macro acquireAndChangeLock(nextLockHolder)
    begin
        switchWaitForLock();
        switchLock := nextLockHolder;
    end macro;

    macro releaseLock(prevLockHolder)
    begin
        assert \/ switchLock[2] = prevLockHolder[2]
               \/ switchLock[2] = NO_LOCK;
        switchLock := <<NO_LOCK, NO_LOCK>>;
    end macro;
        
    (*******************************************************************)
    (*                     Switches SIMPLE Model                       *)
    (*******************************************************************)

    fair process swProcess \in ({SW_SIMPLE_ID} \X SW)
    variables ingressPkt = [type |-> 0]
    begin
    SwitchSimpleProcess:
    while TRUE do
        assert whichSwitchModel(self[2]) = SW_SIMPLE_MODEL;
        await swCanReceivePackets(self[2]);         
        await Len(controller2Switch[self[2]]) > 0;
        switchWaitForLock();
        ingressPkt := Head(controller2Switch[self[2]]);
        assert ingressPkt.type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ, CLEAR_TCAM};
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        if ingressPkt.type = INSTALL_FLOW then
            installToTCAM(ingressPkt.flow);
            sendConfirmation(ingressPkt.from, ingressPkt.flow, INSTALLED_SUCCESSFULLY);
        elsif ingressPkt.type = DELETE_FLOW then
            removeFromTCAM(ingressPkt.flow);
            \* TODO: Should we just send all updates for EH through MS?
            sendConfirmation(ingressPkt.from, ingressPkt.flow, DELETED_SUCCESSFULLY);
        elsif ingressPkt.type = CLEAR_TCAM then
            clearTCAM();
            sendClearConfirmation();
            \* sendClearConfirmation(ingressPkt.from);
        elsif ingressPkt.type = FLOW_STAT_REQ then
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
  
    fair process swFailureProc \in ({SW_FAILURE_PROC} \X SW)
    variable statusMsg = <<>>, obj = [type |-> 0];
    begin
    SwitchFailure:
    while TRUE do
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                 \/ switchLock[2] = self[2];
        await sw_fail_ordering_var # <<>>;
        await \E x \in Head(sw_fail_ordering_var): x.sw = self[2];
        obj := CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2];
        RecoveryStatus[self[2]].transient := obj.transient || RecoveryStatus[self[2]].partial := obj.partial;
        removeFromSeqSet(sw_fail_ordering_var, obj);
        
        assert obj.partial = 0;
        completeFailure();
    end while
    end process

    fair process swResolveFailure \in ({SW_RESOLVE_PROC} \X SW)
    variable statusResolveMsg = <<>>;
    begin
    SwitchResolveFailure:
    while TRUE do
        await RecoveryStatus[self[2]].transient = 1;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ switchLock = <<NO_LOCK, NO_LOCK>>;

        assert RecoveryStatus[self[2]].partial = 0;
        resolveCompleteFailure();  
        RecoveryStatus[self[2]] := [transient |-> 0, partial |-> 0];
    end while
    end process

    fair process ghostUnlockProcess \in ({GHOST_UNLOCK_PROC} \X SW)
    begin
    ghostProc:
    while TRUE do
        await /\ switchLock # <<NO_LOCK, NO_LOCK>>
              /\ switchLock[2] = self[2]
              /\ controllerLock = <<NO_LOCK, NO_LOCK>>;
        await switchStatus[switchLock[2]].nicAsic = Failed;
        releaseLock(switchLock);
    end while
    end process
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "598be4df" /\ chksum(tla) = "12734517")
VARIABLES switchLock, controllerLock, sw_fail_ordering_var, SwProcSet, 
          controller2Switch, switch2Controller, switchStatus, installedIRs, 
          TCAM, controlMsgCounter, RecoveryStatus

(* define statement *)
indexInSeq(seq, val) == CHOOSE i \in DOMAIN seq: seq[i] = val
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]

swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed
swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed

existMatchingEntryTCAM(swID, flowID) == \E x \in rangeSeq(TCAM[swID]): x = flowID
swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed

returnSwitchElementsNotFailed(sw) == {
    x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                   /\ \/ /\ WHICH_SWITCH_MODEL[x] = SW_COMPLEX_MODEL
                                         /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1
                                      \/ /\ WHICH_SWITCH_MODEL[x] = SW_SIMPLE_MODEL
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

VARIABLES ingressPkt, statusMsg, obj, statusResolveMsg

vars == << switchLock, controllerLock, sw_fail_ordering_var, SwProcSet, 
           controller2Switch, switch2Controller, switchStatus, installedIRs, 
           TCAM, controlMsgCounter, RecoveryStatus, ingressPkt, statusMsg, 
           obj, statusResolveMsg >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ SwProcSet = ((({SW_SIMPLE_ID} \X SW)) \cup
                        (({SW_FAILURE_PROC} \X SW)) \cup
                        (({SW_RESOLVE_PROC} \X SW)))
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ switchStatus =                [
                              x \in SW |-> [
                                  cpu |-> NotFailed,
                                  nicAsic |-> NotFailed,
                                  ofa |-> NotFailed,
                                  installer |-> NotFailed
                              ]
                          ]
        /\ installedIRs = <<>>
        /\ TCAM = [x \in SW |-> <<>>]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
        (* Process swProcess *)
        /\ ingressPkt = [self \in ({SW_SIMPLE_ID} \X SW) |-> [type |-> 0]]
        (* Process swFailureProc *)
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> <<>>]
        /\ obj = [self \in ({SW_FAILURE_PROC} \X SW) |-> [type |-> 0]]
        (* Process swResolveFailure *)
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> <<>>]

swProcess(self) == /\ Assert(whichSwitchModel(self[2]) = SW_SIMPLE_MODEL, 
                             "Failure of assertion at line 254, column 9.")
                   /\ swCanReceivePackets(self[2])
                   /\ Len(controller2Switch[self[2]]) > 0
                   /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                   /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                   /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                   /\ Assert(ingressPkt'[self].type \in {INSTALL_FLOW, DELETE_FLOW, FLOW_STAT_REQ, CLEAR_TCAM}, 
                             "Failure of assertion at line 259, column 9.")
                   /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                   /\ IF ingressPkt'[self].type = INSTALL_FLOW
                         THEN /\ installedIRs' = Append(installedIRs, (ingressPkt'[self].flow))
                              /\ TCAM' = [TCAM EXCEPT ![self[2]] = Append(TCAM[self[2]], (ingressPkt'[self].flow))]
                              /\ Assert(WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL, 
                                        "Failure of assertion at line 136, column 9 of macro called at line 263, column 13.")
                              /\ switch2Controller' = Append(switch2Controller, (           [
                                                          type |-> INSTALLED_SUCCESSFULLY,
                                                          from |-> self[2],
                                                          to |-> (ingressPkt'[self].from),
                                                          flow |-> (ingressPkt'[self].flow)
                                                      ]))
                              /\ UNCHANGED controlMsgCounter
                         ELSE /\ IF ingressPkt'[self].type = DELETE_FLOW
                                    THEN /\ IF (ingressPkt'[self].flow) \in rangeSeq(TCAM[self[2]])
                                               THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = removeFromSeq(TCAM[self[2]], indexInSeq(TCAM[self[2]], (ingressPkt'[self].flow)))]
                                               ELSE /\ TRUE
                                                    /\ TCAM' = TCAM
                                         /\ Assert(WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL, 
                                                   "Failure of assertion at line 136, column 9 of macro called at line 267, column 13.")
                                         /\ switch2Controller' = Append(switch2Controller, (           [
                                                                     type |-> DELETED_SUCCESSFULLY,
                                                                     from |-> self[2],
                                                                     to |-> (ingressPkt'[self].from),
                                                                     flow |-> (ingressPkt'[self].flow)
                                                                 ]))
                                         /\ UNCHANGED controlMsgCounter
                                    ELSE /\ IF ingressPkt'[self].type = CLEAR_TCAM
                                               THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = <<>>]
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
                                               ELSE /\ IF ingressPkt'[self].type = FLOW_STAT_REQ
                                                          THEN /\ IF ingressPkt'[self].flow = ALL_FLOW
                                                                     THEN /\ Assert(WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL, 
                                                                                    "Failure of assertion at line 136, column 9 of macro called at line 274, column 17.")
                                                                          /\ switch2Controller' = Append(switch2Controller, (           [
                                                                                                      type |-> FLOW_STAT_REPLY,
                                                                                                      from |-> self[2],
                                                                                                      to |-> (ingressPkt'[self].from),
                                                                                                      flows |-> rangeSeq(TCAM[self[2]])
                                                                                                  ]))
                                                                     ELSE /\ IF existMatchingEntryTCAM(self[2], ingressPkt'[self].flow)
                                                                                THEN /\ Assert(WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL, 
                                                                                               "Failure of assertion at line 136, column 9 of macro called at line 276, column 17.")
                                                                                     /\ switch2Controller' = Append(switch2Controller, (           [
                                                                                                                 type |-> FLOW_STAT_REPLY,
                                                                                                                 from |-> self[2],
                                                                                                                 to |-> (ingressPkt'[self].from),
                                                                                                                 status |-> ENTRY_FOUND
                                                                                                             ]))
                                                                                ELSE /\ Assert(WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL, 
                                                                                               "Failure of assertion at line 136, column 9 of macro called at line 278, column 17.")
                                                                                     /\ switch2Controller' = Append(switch2Controller, (           [
                                                                                                                 type |-> FLOW_STAT_REPLY,
                                                                                                                 from |-> self[2],
                                                                                                                 to |-> (ingressPkt'[self].from),
                                                                                                                 status |-> NO_ENTRY
                                                                                                             ]))
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED switch2Controller
                                                    /\ UNCHANGED << TCAM, 
                                                                    controlMsgCounter >>
                              /\ UNCHANGED installedIRs
                   /\ Assert(\/ switchLock[2] = self[2]
                             \/ switchLock[2] = NO_LOCK, 
                             "Failure of assertion at line 240, column 9 of macro called at line 281, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ UNCHANGED << controllerLock, sw_fail_ordering_var, 
                                   SwProcSet, switchStatus, RecoveryStatus, 
                                   statusMsg, obj, statusResolveMsg >>

swFailureProc(self) == /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                             \/ switchLock[2] = self[2]
                       /\ sw_fail_ordering_var # <<>>
                       /\ \E x \in Head(sw_fail_ordering_var): x.sw = self[2]
                       /\ obj' = [obj EXCEPT ![self] = CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2]]
                       /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]].transient = obj'[self].transient,
                                                                   ![self[2]].partial = obj'[self].partial]
                       /\ Assert(obj'[self] \in Head(sw_fail_ordering_var), 
                                 "Failure of assertion at line 66, column 9 of macro called at line 297, column 9.")
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{obj'[self]})>> \o Tail(sw_fail_ordering_var)
                       /\ Assert(obj'[self].partial = 0, 
                                 "Failure of assertion at line 299, column 9.")
                       /\ IF switchStatus[self[2]].nicAsic = NotFailed
                             THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                  /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                 swID |-> self[2],
                                                                                 num |-> controlMsgCounter'[self[2]]]]
                                  /\ switch2Controller' = Append(switch2Controller, statusMsg'[self])
                             ELSE /\ TRUE
                                  /\ UNCHANGED << switch2Controller, 
                                                  controlMsgCounter, statusMsg >>
                       /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> Failed, nicAsic |-> Failed,
                                                                               ofa |-> Failed, installer |-> Failed]]
                       /\ TCAM' = [TCAM EXCEPT ![self[2]] = <<>>]
                       /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                       /\ UNCHANGED << switchLock, controllerLock, SwProcSet, 
                                       installedIRs, ingressPkt, 
                                       statusResolveMsg >>

swResolveFailure(self) == /\ RecoveryStatus[self[2]].transient = 1
                          /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock = <<NO_LOCK, NO_LOCK>>
                          /\ Assert(RecoveryStatus[self[2]].partial = 0, 
                                    "Failure of assertion at line 313, column 9.")
                          /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                    "Failure of assertion at line 96, column 9 of macro called at line 314, column 9.")
                          /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                    "Failure of assertion at line 97, column 9 of macro called at line 314, column 9.")
                          /\ Assert(switchStatus[self[2]].ofa = Failed, 
                                    "Failure of assertion at line 98, column 9 of macro called at line 314, column 9.")
                          /\ Assert(switchStatus[self[2]].installer = Failed, 
                                    "Failure of assertion at line 99, column 9 of macro called at line 314, column 9.")
                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> NotFailed, nicAsic |-> NotFailed,
                                                                                  ofa |-> NotFailed, installer |-> NotFailed]]
                          /\ TCAM' = [TCAM EXCEPT ![self[2]] = <<>>]
                          /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                          /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                          /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] =                     [
                                                                                        type |-> KEEP_ALIVE,
                                                                                        swID |-> self[2],
                                                                                        num |-> controlMsgCounter'[self[2]],
                                                                                        installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                                                    ]]
                          /\ switch2Controller' = Append(switch2Controller, statusResolveMsg'[self])
                          /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]] = [transient |-> 0, partial |-> 0]]
                          /\ UNCHANGED << switchLock, controllerLock, 
                                          sw_fail_ordering_var, SwProcSet, 
                                          installedIRs, ingressPkt, statusMsg, 
                                          obj >>

ghostUnlockProcess(self) == /\ /\ switchLock # <<NO_LOCK, NO_LOCK>>
                               /\ switchLock[2] = self[2]
                               /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                            /\ switchStatus[switchLock[2]].nicAsic = Failed
                            /\ Assert(\/ switchLock[2] = switchLock[2]
                                      \/ switchLock[2] = NO_LOCK, 
                                      "Failure of assertion at line 240, column 9 of macro called at line 327, column 9.")
                            /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                            /\ UNCHANGED << controllerLock, 
                                            sw_fail_ordering_var, SwProcSet, 
                                            controller2Switch, 
                                            switch2Controller, switchStatus, 
                                            installedIRs, TCAM, 
                                            controlMsgCounter, RecoveryStatus, 
                                            ingressPkt, statusMsg, obj, 
                                            statusResolveMsg >>

Next == (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
           \/ (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
           \/ (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
           \/ (\E self \in ({GHOST_UNLOCK_PROC} \X SW): ghostUnlockProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(swProcess(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(swResolveFailure(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_vars(ghostUnlockProcess(self))

\* END TRANSLATION 
=============================================================================

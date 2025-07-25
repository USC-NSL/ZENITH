------------------- MODULE drain -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS SW,
          DRAINER,
          UPGRADER,
          EXPANDER,
          NIB,
          RE,
          OFC,
          SW_SIMPLE_ID,
          SW_MANAGE_PROC
         
         
CONSTANTS CONT_EVENT_HANDLER,
          CONT_WORKER,
          CONT_SW_MANAGEMENT
(************************ Management Operations ************************)
CONSTANTS DRAIN_SW,
          UNDRAIN_SW,
          DOWN_SW,
          UP_SW
(************************ Switch States ************************)
CONSTANTS SW_DRAINED,
          SW_UNDRAINED,
          SW_DOWN,
          SW_UP
          
(************************ Messag Types************************)
CONSTANTS MSG_SW_STATUS_CHANGE
          
CONSTANTS UPGRADER_REQUEST_QUEUE,
          EXPANDER_REQUEST_QUEUE
CONSTANTS NULL

(*--fair algorithm stateConsistency
(************************* variables ***************************************)
    variables (*************** Some Auxiliary Vars ***********************)
        (***************************** State Vars ***********************)
        SwStatusNIB = [x \in SW |-> SW_UNDRAINED],
        SwStatusUpgrader = [x \in SW |-> SW_UNDRAINED],
        SwStatusExpander = [x \in SW |-> SW_UNDRAINED],
        SwStatusRE = [x \in SW |-> SW_UNDRAINED],
        SwStatusOFC = [x \in SW |-> SW_UNDRAINED],
        SwStatus = [x \in SW |-> SW_UNDRAINED],
        (***************************** Queue Vars ***********************)
        UpgraderRequestQueue = UPGRADER_REQUEST_QUEUE,
        ExpanderRequestQueue = EXPANDER_REQUEST_QUEUE,
        \* Handle SW_DOWN <--> SW_DRAINED requests
        \* SWManagementQueue = Upgrader2NIB
        SWManagementQueue = <<>>,
        \* Handle SW_UNDRAINED <--> SW_DRAINED requests
        DrainRequestQueue = <<>>,
        (***************************** Message Queue Vars ****************)
        Upgrader2NIB = <<>>,
        NIB2Upgrader = <<>>,
        Expander2NIB = <<>>,
        NIB2Expander = <<>>,
        RE2SW = [x\in SW |-> <<>>],
        SW2RE = <<>>,
        OFC2SW = [x\in SW |-> <<>>],
        SW2OFC = <<>>,
        RE2NIB = <<>>,
        OFC2NIB = <<>>,
    
define
        (********************* Auxiliary functions **********************)
        max(set) == CHOOSE x \in set: \A y \in set: x \geq y
        min(set) == CHOOSE x \in set: \A y \in set: x \leq y 
        
end define
    (*******************************************************************)
    (*                            Upgrader                             *)
    (*******************************************************************)
    
    \* ============ Upgrader Worker ====================================
    \* ============ Use blocking mode for design =======================
    fair process upgraderWorkerProcess \in ({UPGRADER} \X {CONT_WORKER})
    variables opRequest = [type |-> 0], 
              transaction = <<>>,
              sw_status = NULL,
              sw = NULL;
    begin
    UpgraderThread:
    while TRUE do
        await UpgraderRequestQueue # <<>>;
        opRequest := Head(UpgraderRequestQueue);
        sw := opRequest.sw;
        assert opRequest.type \in {DOWN_SW, UP_SW, DRAIN_SW, UNDRAIN_SW};
        
        if opRequest.type = DOWN_SW then \* target state is SW_DOWN
            \* Read NIB to check the switch status
            sw_status := SwStatusUpgrader[sw];      
            if sw_status = SW_DRAINED then
                \* SW_DRAINED->SW_DOWN
                 SWManagementQueue := Append(SWManagementQueue, [type |-> DOWN_SW, 
                                                                sw |-> sw,
                                                                value |-> SW_DOWN]);
                 \* await switch turned to be SW_DOWN -> dequeue request
                 UpgraderAwaitSwDown1:
                    await SwStatusUpgrader[sw] = SW_DOWN;
                    goto DequeueManagementRequest;
            elsif sw_status = SW_DOWN then
                 \* skip since target status is reached -> dequeue request
                 goto DequeueManagementRequest;
            elsif sw_status = SW_UNDRAINED then
                 \* SW_UNDRAINED->SW_DRAINED
                 DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                 \* SW_DRAINED->SW_DOWN
                 UpgraderAwaitSwDrained1:
                    if SwStatusUpgrader[sw] = SW_DOWN then
                        goto DequeueManagementRequest;
                    else
                        await SwStatusUpgrader[sw] = SW_DRAINED;
                        SWManagementQueue := Append(SWManagementQueue, [type |-> DOWN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DOWN]);
                    end if;
                 \* SW_DOWN -> dequeue request
                 UpgraderAwaitSwDown2:
                    await SwStatusUpgrader[sw] = SW_DOWN;
                    goto DequeueManagementRequest;
            elsif sw_status = SW_UP then
                SWManagementQueue := Append(SWManagementQueue, [type |-> DOWN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DOWN]);
                UpgraderAwaitSwDown3:
                    await SwStatusUpgrader[sw] = SW_DOWN;
                    goto DequeueManagementRequest;
            else 
                assert FALSE;           
            end if;
        elsif opRequest.type = UNDRAIN_SW then \*target state is SW_UNDRAINED
            sw_status := SwStatusUpgrader[sw];
            if sw_status = SW_DRAINED then
                \* SW_DRAINED->SW_UNDRAINED
                DrainRequestQueue := Append(DrainRequestQueue, [type |-> UNDRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UNDRAINED]);
                \* SW_UNDRAINED -> dequeue request
                UpgraderWaitSWUndrained1:
                    await SwStatusUpgrader[sw] = SW_UNDRAINED;
                    goto DequeueManagementRequest;
            elsif sw_status = SW_DOWN then
                SWManagementQueue := Append(SWManagementQueue, [type |-> UP_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UP]);
                UpgraderDrainSW1:
                    await SwStatusUpgrader[sw] = SW_UP;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                
                UpgraderUndrainSW1:
                    await SwStatusUpgrader[sw] = SW_DRAINED;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> UNDRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UNDRAINED]);
                \* SW_UNDRAINED -> dequeue request
                UpgraderWaitSWUndrained:
                    await SwStatusUpgrader[sw] = SW_UNDRAINED;
                    goto DequeueManagementRequest;
                
            elsif sw_status = SW_UP then
                DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                
                UpgraderUndrainSW2:
                    await SwStatusUpgrader[sw] = SW_DRAINED;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> UNDRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UNDRAINED]);
                \* SW_UNDRAINED -> dequeue request
                UpgraderWaitSWUndrained2:
                    await SwStatusUpgrader[sw] = SW_UNDRAINED;
                    goto DequeueManagementRequest;
            elsif sw_status = SW_UNDRAINED then
                \* target state reached
                skip;
            else
                assert FALSE;
            end if;
        elsif opRequest.type = DRAIN_SW then \*target state is SW_DRAINED
            sw_status := SwStatusUpgrader[sw];
            if sw_status = SW_DRAINED then
                goto DequeueManagementRequest;
            elsif sw_status = SW_DOWN then
                SWManagementQueue := Append(SWManagementQueue, [type |-> UP_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UP]);
                UpgraderDrainSW2:
                    await SwStatusUpgrader[sw] = SW_UP;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                UpgraderWaitSWUndrained3:
                    await SwStatusUpgrader[sw] = SW_DRAINED;
                    goto DequeueManagementRequest;    
            elsif sw_status \in {SW_UNDRAINED, SW_UP} then
                DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                UpgraderWaitSWUndrained4:
                    await SwStatusUpgrader[sw] = SW_DRAINED;
                    goto DequeueManagementRequest;                                                  
            else
                assert FALSE;
            end if; 
        else
            assert FALSE;
        end if;
        DequeueManagementRequest:
            assert FALSE;
            UpgraderRequestQueue := Tail(UpgraderRequestQueue);
    end while;
    end process;
    
    \* ============ Upgrader NIB Event Handler =================
    \* ============ Assumption: update is always for a single object, such as IR/SW_STATUS
    fair process upgraderEventHandlerProcess \in ({UPGRADER} \X {CONT_EVENT_HANDLER})
    variables sw_status_update = [type |-> NULL]
    begin
    UpgraderNIBEventHandlerProc:
        while TRUE do 
            await NIB2Upgrader # <<>>;
            sw_status_update := Head(NIB2Upgrader);
            NIB2Upgrader :=  Tail(NIB2Upgrader);
            SwStatusUpgrader[sw_status_update.sw] := sw_status_update.value;
        end while;

    end process;
    
    
    
    (*******************************************************************)
    (********************** Network Information Base *******************)
    (*******************************************************************)
    fair process NIBEventHandlerForRE \in ({NIB} \X {CONT_EVENT_HANDLER})
    variables sw_status_update = [type |-> NULL]
    begin
    NIBEventHandlerForREProc:
        while TRUE do
            await RE2NIB # <<>>;
            sw_status_update := Head(RE2NIB);
            RE2NIB :=  Tail(RE2NIB);
            SwStatusNIB[sw_status_update.sw] := sw_status_update.value;
            NIB2Upgrader := Append(NIB2Upgrader, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw_status_update.sw, 
                       value|-> sw_status_update.value
                       ]);
            NIB2Expander := Append(NIB2Expander, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw_status_update.sw, 
                       value|-> sw_status_update.value
                       ]);
        end while;
    end process;
    
    fair process NIBEventHandlerForOFC \in ({NIB} \X {CONT_EVENT_HANDLER})
    begin
    NIBEventHandlerForREProc:
        while TRUE do
            await OFC2NIB # <<>>;
            sw_status_update := Head(OFC2NIB);
            OFC2NIB :=  Tail(OFC2NIB);
            SwStatusNIB[sw_status_update.sw] := sw_status_update.value;
            NIB2Upgrader := Append(NIB2Upgrader, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw_status_update.sw, 
                       value|-> sw_status_update.value
                       ]);
            NIB2Expander := Append(NIB2Upgrader, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw_status_update.sw, 
                       value|-> sw_status_update.value
                       ]);
        end while;
    end process;
    (*******************************************************************)
    (*                            Drainer                              *)
    (*******************************************************************)
\*    fair process drainerProcess \in ({DRAINER} \X {CONT_EVENT_HANDLER})
\*    variables req = []
\*    begin
\*    DrainerProc:
\*        while TRUE do
\*            await DrainRequestQueue # <<>>;
\*            req := Head(RC2NIB);
\*            DrainRequestQueue := Tail(DrainRequestQueue);
\*            
\*        end while;
\*    
\*    end process;
\*    
    (*******************************************************************)
    (*                               RE                              *)
    (*******************************************************************)
    \*---------------------- RE worker---------------------------------
    fair process REWorkerProcess \in ({RE} \X {CONT_WORKER})
    variables req = [type |-> NULL]
    begin
    REWorkerProc:
        while TRUE do
            await DrainRequestQueue # <<>>;
            req := Head(DrainRequestQueue);
            DrainRequestQueue := Tail(DrainRequestQueue);
            RE2SW[req.sw] := Append(RE2SW[req.sw], req);
        end while;
    end process;
    
    \*---------------------- RE SW handler------------------------------
    \* In practice, a drain request should go through the following path:
    \* RE --> NIB --> OFC --> SW --> OFC --> NIB --> RE
    \* Since we do not focus on failures, we assume RE talks to SW directly
    fair process RESWEventHandlerProcess \in ({RE} \X {CONT_EVENT_HANDLER})
    variables sw_status_update = [type |-> NULL]
    begin
    RESWEventHandlerProc:
        while TRUE do
            await SW2RE # <<>>;
            sw_status_update := Head(SW2RE);
            SW2RE :=  Tail(SW2RE);
            SwStatusRE[sw_status_update.sw] := sw_status_update.value;
            RE2NIB := Append(RE2NIB, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw_status_update.sw, 
                       value|-> sw_status_update.value
                       ]);
        end while;
    end process;
    
    (*******************************************************************)
    (*                               OFC                              *)
    (*******************************************************************)
    \* OFC worker
    fair process OFCSwitchManagementProcess \in ({OFC} \X {CONT_SW_MANAGEMENT})
    variables req = [type |-> NULL]
    begin
    DrainerProc:
        while TRUE do
            await SWManagementQueue # <<>>;
            req := Head(SWManagementQueue);
            SWManagementQueue := Tail(SWManagementQueue);
            OFC2SW[req.sw] := Append(OFC2SW[req.sw], req);
        end while;
    end process;
    
    \* OFC SW event handler
    fair process OFCSWEventHandlerProcess \in ({OFC} \X {CONT_EVENT_HANDLER})
    variables sw_status_update = [type |-> NULL]
    begin
    OFCSWEventHandlingProc:
        while TRUE do
            await SW2OFC # <<>>;
            sw_status_update := Head(SW2OFC);
            SW2OFC :=  Tail(SW2OFC);
            SwStatusOFC[sw_status_update.sw] := sw_status_update.value;
            OFC2NIB := Append(OFC2NIB, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw_status_update.sw, 
                       value|-> sw_status_update.value
                       ]);
        end while;
    end process;
   
    (*******************************************************************)
    (*                     Switches Management Process                 *)
    (*******************************************************************)
    fair process swManagementProcess \in ({SW_MANAGE_PROC} \X SW)
    variables op = [type |-> NULL], sw_id = self[2];
    begin
        SWManagementProc:
        while TRUE do
            await OFC2SW[sw_id] # <<>>;
            op := Head(OFC2SW[sw_id]);
            assert op.type = MSG_SW_STATUS_CHANGE;
            OFC2SW[sw_id] := Tail(OFC2SW[sw_id]);
            if op.value = SW_DRAINED then
                assert SwStatus[sw_id] = SW_DOWN;
                SwStatus[sw_id] := SW_DRAINED; 
            elsif op.value = SW_DOWN then
                assert SwStatus[sw_id] = SW_DRAINED;
                SwStatus[sw_id] := SW_DOWN;
            end if;
            SW2OFC := Append(SW2OFC, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw_id, 
                       value|-> SwStatus[sw_id]
                       ]);
        end while;
    end process;
    
    (*******************************************************************)
    (*                        Switches IR Process                   *)
    (*******************************************************************)
    \* Assume switches reply to RE directly after modifying IRs on switches
    fair process swIRProcess \in ({SW_SIMPLE_ID} \X SW)
    variables op = [type |-> NULL], sw = self[2];
    begin
        SWManagementProc:
        while TRUE do
            await RE2SW[sw] # <<>>;
            op := Head(RE2SW[sw]);
            assert op.sw = sw;
            assert op.type = MSG_SW_STATUS_CHANGE;
            RE2SW[sw] := Tail(RE2SW[sw]);
            if op.value = SW_DRAINED then
                if SwStatus[sw] # SW_DRAINED then
                    assert SwStatus[sw] = SW_UNDRAINED;
                    SwStatus[sw] := SW_DRAINED; 
                end if;
            elsif op.value = SW_UNDRAINED then
                if SwStatus[sw] # SW_UNDRAINED then
                    assert SwStatus[sw] = SW_DRAINED;
                    SwStatus[sw] := SW_UNDRAINED;
                end if;
            else
                assert FALSE;
            end if;
            SW2RE := Append(SW2RE, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw, 
                       value|-> SwStatus[sw]
                       ]);
        end while;
    end process;
end algorithm
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "9f9c0110" /\ chksum(tla) = "7ba0e93e")
\* Label NIBEventHandlerForREProc of process NIBEventHandlerForRE at line 244 col 9 changed to NIBEventHandlerForREProc_
\* Label SWManagementProc of process swManagementProcess at line 370 col 9 changed to SWManagementProc_
\* Process variable sw of process upgraderWorkerProcess at line 81 col 15 changed to sw_
\* Process variable sw_status_update of process upgraderEventHandlerProcess at line 223 col 15 changed to sw_status_update_
\* Process variable sw_status_update of process NIBEventHandlerForRE at line 241 col 15 changed to sw_status_update_N
\* Process variable req of process REWorkerProcess at line 299 col 15 changed to req_
\* Process variable sw_status_update of process RESWEventHandlerProcess at line 315 col 15 changed to sw_status_update_R
\* Process variable op of process swManagementProcess at line 367 col 15 changed to op_
VARIABLES SwStatusNIB, SwStatusUpgrader, SwStatusExpander, SwStatusRE, 
          SwStatusOFC, SwStatus, UpgraderRequestQueue, ExpanderRequestQueue, 
          SWManagementQueue, DrainRequestQueue, Upgrader2NIB, NIB2Upgrader, 
          Expander2NIB, NIB2Expander, RE2SW, SW2RE, OFC2SW, SW2OFC, RE2NIB, 
          OFC2NIB, pc

(* define statement *)
max(set) == CHOOSE x \in set: \A y \in set: x \geq y
min(set) == CHOOSE x \in set: \A y \in set: x \leq y

VARIABLES opRequest, transaction, sw_status, sw_, sw_status_update_, 
          sw_status_update_N, req_, sw_status_update_R, req, sw_status_update, 
          op_, sw_id, op, sw

vars == << SwStatusNIB, SwStatusUpgrader, SwStatusExpander, SwStatusRE, 
           SwStatusOFC, SwStatus, UpgraderRequestQueue, ExpanderRequestQueue, 
           SWManagementQueue, DrainRequestQueue, Upgrader2NIB, NIB2Upgrader, 
           Expander2NIB, NIB2Expander, RE2SW, SW2RE, OFC2SW, SW2OFC, RE2NIB, 
           OFC2NIB, pc, opRequest, transaction, sw_status, sw_, 
           sw_status_update_, sw_status_update_N, req_, sw_status_update_R, 
           req, sw_status_update, op_, sw_id, op, sw >>

ProcSet == (({UPGRADER} \X {CONT_WORKER})) \cup (({UPGRADER} \X {CONT_EVENT_HANDLER})) \cup (({NIB} \X {CONT_EVENT_HANDLER})) \cup (({NIB} \X {CONT_EVENT_HANDLER})) \cup (({RE} \X {CONT_WORKER})) \cup (({RE} \X {CONT_EVENT_HANDLER})) \cup (({OFC} \X {CONT_SW_MANAGEMENT})) \cup (({OFC} \X {CONT_EVENT_HANDLER})) \cup (({SW_MANAGE_PROC} \X SW)) \cup (({SW_SIMPLE_ID} \X SW))

Init == (* Global variables *)
        /\ SwStatusNIB = [x \in SW |-> SW_UNDRAINED]
        /\ SwStatusUpgrader = [x \in SW |-> SW_UNDRAINED]
        /\ SwStatusExpander = [x \in SW |-> SW_UNDRAINED]
        /\ SwStatusRE = [x \in SW |-> SW_UNDRAINED]
        /\ SwStatusOFC = [x \in SW |-> SW_UNDRAINED]
        /\ SwStatus = [x \in SW |-> SW_UNDRAINED]
        /\ UpgraderRequestQueue = UPGRADER_REQUEST_QUEUE
        /\ ExpanderRequestQueue = EXPANDER_REQUEST_QUEUE
        /\ SWManagementQueue = <<>>
        /\ DrainRequestQueue = <<>>
        /\ Upgrader2NIB = <<>>
        /\ NIB2Upgrader = <<>>
        /\ Expander2NIB = <<>>
        /\ NIB2Expander = <<>>
        /\ RE2SW = [x\in SW |-> <<>>]
        /\ SW2RE = <<>>
        /\ OFC2SW = [x\in SW |-> <<>>]
        /\ SW2OFC = <<>>
        /\ RE2NIB = <<>>
        /\ OFC2NIB = <<>>
        (* Process upgraderWorkerProcess *)
        /\ opRequest = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> [type |-> 0]]
        /\ transaction = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> <<>>]
        /\ sw_status = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> NULL]
        /\ sw_ = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> NULL]
        (* Process upgraderEventHandlerProcess *)
        /\ sw_status_update_ = [self \in ({UPGRADER} \X {CONT_EVENT_HANDLER}) |-> [type |-> NULL]]
        (* Process NIBEventHandlerForRE *)
        /\ sw_status_update_N = [self \in ({NIB} \X {CONT_EVENT_HANDLER}) |-> [type |-> NULL]]
        (* Process REWorkerProcess *)
        /\ req_ = [self \in ({RE} \X {CONT_WORKER}) |-> [type |-> NULL]]
        (* Process RESWEventHandlerProcess *)
        /\ sw_status_update_R = [self \in ({RE} \X {CONT_EVENT_HANDLER}) |-> [type |-> NULL]]
        (* Process OFCSwitchManagementProcess *)
        /\ req = [self \in ({OFC} \X {CONT_SW_MANAGEMENT}) |-> [type |-> NULL]]
        (* Process OFCSWEventHandlerProcess *)
        /\ sw_status_update = [self \in ({OFC} \X {CONT_EVENT_HANDLER}) |-> [type |-> NULL]]
        (* Process swManagementProcess *)
        /\ op_ = [self \in ({SW_MANAGE_PROC} \X SW) |-> [type |-> NULL]]
        /\ sw_id = [self \in ({SW_MANAGE_PROC} \X SW) |-> self[2]]
        (* Process swIRProcess *)
        /\ op = [self \in ({SW_SIMPLE_ID} \X SW) |-> [type |-> NULL]]
        /\ sw = [self \in ({SW_SIMPLE_ID} \X SW) |-> self[2]]
        /\ pc = [self \in ProcSet |-> CASE self \in ({UPGRADER} \X {CONT_WORKER}) -> "UpgraderThread"
                                        [] self \in ({UPGRADER} \X {CONT_EVENT_HANDLER}) -> "UpgraderNIBEventHandlerProc"
                                        [] self \in ({NIB} \X {CONT_EVENT_HANDLER}) -> "NIBEventHandlerForREProc_"
                                        [] self \in ({NIB} \X {CONT_EVENT_HANDLER}) -> "NIBEventHandlerForREProc"
                                        [] self \in ({RE} \X {CONT_WORKER}) -> "REWorkerProc"
                                        [] self \in ({RE} \X {CONT_EVENT_HANDLER}) -> "RESWEventHandlerProc"
                                        [] self \in ({OFC} \X {CONT_SW_MANAGEMENT}) -> "DrainerProc"
                                        [] self \in ({OFC} \X {CONT_EVENT_HANDLER}) -> "OFCSWEventHandlingProc"
                                        [] self \in ({SW_MANAGE_PROC} \X SW) -> "SWManagementProc_"
                                        [] self \in ({SW_SIMPLE_ID} \X SW) -> "SWManagementProc"]

UpgraderThread(self) == /\ pc[self] = "UpgraderThread"
                        /\ UpgraderRequestQueue # <<>>
                        /\ opRequest' = [opRequest EXCEPT ![self] = Head(UpgraderRequestQueue)]
                        /\ sw_' = [sw_ EXCEPT ![self] = opRequest'[self].sw]
                        /\ Assert(opRequest'[self].type \in {DOWN_SW, UP_SW, DRAIN_SW, UNDRAIN_SW}, 
                                  "Failure of assertion at line 88, column 9.")
                        /\ IF opRequest'[self].type = DOWN_SW
                              THEN /\ sw_status' = [sw_status EXCEPT ![self] = SwStatusUpgrader[sw_'[self]]]
                                   /\ IF sw_status'[self] = SW_DRAINED
                                         THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                                sw |-> sw_'[self],
                                                                                                value |-> SW_DOWN])
                                              /\ pc' = [pc EXCEPT ![self] = "UpgraderAwaitSwDown1"]
                                              /\ UNCHANGED DrainRequestQueue
                                         ELSE /\ IF sw_status'[self] = SW_DOWN
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                         /\ UNCHANGED << SWManagementQueue, 
                                                                         DrainRequestQueue >>
                                                    ELSE /\ IF sw_status'[self] = SW_UNDRAINED
                                                               THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                       sw |-> sw_'[self],
                                                                                                                       value |-> SW_DRAINED])
                                                                    /\ pc' = [pc EXCEPT ![self] = "UpgraderAwaitSwDrained1"]
                                                                    /\ UNCHANGED SWManagementQueue
                                                               ELSE /\ IF sw_status'[self] = SW_UP
                                                                          THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                                                                   sw |-> sw_'[self],
                                                                                                                                   value |-> SW_DOWN])
                                                                               /\ pc' = [pc EXCEPT ![self] = "UpgraderAwaitSwDown3"]
                                                                          ELSE /\ Assert(FALSE, 
                                                                                         "Failure of assertion at line 132, column 17.")
                                                                               /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                               /\ UNCHANGED SWManagementQueue
                                                                    /\ UNCHANGED DrainRequestQueue
                              ELSE /\ IF opRequest'[self].type = UNDRAIN_SW
                                         THEN /\ sw_status' = [sw_status EXCEPT ![self] = SwStatusUpgrader[sw_'[self]]]
                                              /\ IF sw_status'[self] = SW_DRAINED
                                                    THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> UNDRAIN_SW,
                                                                                                             sw |-> sw_'[self],
                                                                                                             value |-> SW_UNDRAINED])
                                                         /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWUndrained1"]
                                                         /\ UNCHANGED SWManagementQueue
                                                    ELSE /\ IF sw_status'[self] = SW_DOWN
                                                               THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> UP_SW,
                                                                                                                        sw |-> sw_'[self],
                                                                                                                        value |-> SW_UP])
                                                                    /\ pc' = [pc EXCEPT ![self] = "UpgraderDrainSW1"]
                                                                    /\ UNCHANGED DrainRequestQueue
                                                               ELSE /\ IF sw_status'[self] = SW_UP
                                                                          THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                                   sw |-> sw_'[self],
                                                                                                                                   value |-> SW_DRAINED])
                                                                               /\ pc' = [pc EXCEPT ![self] = "UpgraderUndrainSW2"]
                                                                          ELSE /\ IF sw_status'[self] = SW_UNDRAINED
                                                                                     THEN /\ TRUE
                                                                                     ELSE /\ Assert(FALSE, 
                                                                                                    "Failure of assertion at line 183, column 17.")
                                                                               /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                               /\ UNCHANGED DrainRequestQueue
                                                                    /\ UNCHANGED SWManagementQueue
                                         ELSE /\ IF opRequest'[self].type = DRAIN_SW
                                                    THEN /\ sw_status' = [sw_status EXCEPT ![self] = SwStatusUpgrader[sw_'[self]]]
                                                         /\ IF sw_status'[self] = SW_DRAINED
                                                               THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                    /\ UNCHANGED << SWManagementQueue, 
                                                                                    DrainRequestQueue >>
                                                               ELSE /\ IF sw_status'[self] = SW_DOWN
                                                                          THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> UP_SW,
                                                                                                                                   sw |-> sw_'[self],
                                                                                                                                   value |-> SW_UP])
                                                                               /\ pc' = [pc EXCEPT ![self] = "UpgraderDrainSW2"]
                                                                               /\ UNCHANGED DrainRequestQueue
                                                                          ELSE /\ IF sw_status'[self] \in {SW_UNDRAINED, SW_UP}
                                                                                     THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                                              sw |-> sw_'[self],
                                                                                                                                              value |-> SW_DRAINED])
                                                                                          /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWUndrained4"]
                                                                                     ELSE /\ Assert(FALSE, 
                                                                                                    "Failure of assertion at line 209, column 17.")
                                                                                          /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                                          /\ UNCHANGED DrainRequestQueue
                                                                               /\ UNCHANGED SWManagementQueue
                                                    ELSE /\ Assert(FALSE, 
                                                                   "Failure of assertion at line 212, column 13.")
                                                         /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                         /\ UNCHANGED << SWManagementQueue, 
                                                                         DrainRequestQueue, 
                                                                         sw_status >>
                        /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                        SwStatusExpander, SwStatusRE, 
                                        SwStatusOFC, SwStatus, 
                                        UpgraderRequestQueue, 
                                        ExpanderRequestQueue, Upgrader2NIB, 
                                        NIB2Upgrader, Expander2NIB, 
                                        NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                        SW2OFC, RE2NIB, OFC2NIB, transaction, 
                                        sw_status_update_, sw_status_update_N, 
                                        req_, sw_status_update_R, req, 
                                        sw_status_update, op_, sw_id, op, sw >>

DequeueManagementRequest(self) == /\ pc[self] = "DequeueManagementRequest"
                                  /\ Assert(FALSE, 
                                            "Failure of assertion at line 215, column 13.")
                                  /\ UpgraderRequestQueue' = Tail(UpgraderRequestQueue)
                                  /\ pc' = [pc EXCEPT ![self] = "UpgraderThread"]
                                  /\ UNCHANGED << SwStatusNIB, 
                                                  SwStatusUpgrader, 
                                                  SwStatusExpander, SwStatusRE, 
                                                  SwStatusOFC, SwStatus, 
                                                  ExpanderRequestQueue, 
                                                  SWManagementQueue, 
                                                  DrainRequestQueue, 
                                                  Upgrader2NIB, NIB2Upgrader, 
                                                  Expander2NIB, NIB2Expander, 
                                                  RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                  RE2NIB, OFC2NIB, opRequest, 
                                                  transaction, sw_status, sw_, 
                                                  sw_status_update_, 
                                                  sw_status_update_N, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_id, 
                                                  op, sw >>

UpgraderAwaitSwDown1(self) == /\ pc[self] = "UpgraderAwaitSwDown1"
                              /\ SwStatusUpgrader[sw_[self]] = SW_DOWN
                              /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                              /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                              SwStatusExpander, SwStatusRE, 
                                              SwStatusOFC, SwStatus, 
                                              UpgraderRequestQueue, 
                                              ExpanderRequestQueue, 
                                              SWManagementQueue, 
                                              DrainRequestQueue, Upgrader2NIB, 
                                              NIB2Upgrader, Expander2NIB, 
                                              NIB2Expander, RE2SW, SW2RE, 
                                              OFC2SW, SW2OFC, RE2NIB, OFC2NIB, 
                                              opRequest, transaction, 
                                              sw_status, sw_, 
                                              sw_status_update_, 
                                              sw_status_update_N, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_id, op, 
                                              sw >>

UpgraderAwaitSwDrained1(self) == /\ pc[self] = "UpgraderAwaitSwDrained1"
                                 /\ IF SwStatusUpgrader[sw_[self]] = SW_DOWN
                                       THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                            /\ UNCHANGED SWManagementQueue
                                       ELSE /\ SwStatusUpgrader[sw_[self]] = SW_DRAINED
                                            /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                        sw |-> sw_[self],
                                                                                        value |-> SW_DOWN])
                                            /\ pc' = [pc EXCEPT ![self] = "UpgraderAwaitSwDown2"]
                                 /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                                 SwStatusExpander, SwStatusRE, 
                                                 SwStatusOFC, SwStatus, 
                                                 UpgraderRequestQueue, 
                                                 ExpanderRequestQueue, 
                                                 DrainRequestQueue, 
                                                 Upgrader2NIB, NIB2Upgrader, 
                                                 Expander2NIB, NIB2Expander, 
                                                 RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                 RE2NIB, OFC2NIB, opRequest, 
                                                 transaction, sw_status, sw_, 
                                                 sw_status_update_, 
                                                 sw_status_update_N, req_, 
                                                 sw_status_update_R, req, 
                                                 sw_status_update, op_, sw_id, 
                                                 op, sw >>

UpgraderAwaitSwDown2(self) == /\ pc[self] = "UpgraderAwaitSwDown2"
                              /\ SwStatusUpgrader[sw_[self]] = SW_DOWN
                              /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                              /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                              SwStatusExpander, SwStatusRE, 
                                              SwStatusOFC, SwStatus, 
                                              UpgraderRequestQueue, 
                                              ExpanderRequestQueue, 
                                              SWManagementQueue, 
                                              DrainRequestQueue, Upgrader2NIB, 
                                              NIB2Upgrader, Expander2NIB, 
                                              NIB2Expander, RE2SW, SW2RE, 
                                              OFC2SW, SW2OFC, RE2NIB, OFC2NIB, 
                                              opRequest, transaction, 
                                              sw_status, sw_, 
                                              sw_status_update_, 
                                              sw_status_update_N, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_id, op, 
                                              sw >>

UpgraderAwaitSwDown3(self) == /\ pc[self] = "UpgraderAwaitSwDown3"
                              /\ SwStatusUpgrader[sw_[self]] = SW_DOWN
                              /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                              /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                              SwStatusExpander, SwStatusRE, 
                                              SwStatusOFC, SwStatus, 
                                              UpgraderRequestQueue, 
                                              ExpanderRequestQueue, 
                                              SWManagementQueue, 
                                              DrainRequestQueue, Upgrader2NIB, 
                                              NIB2Upgrader, Expander2NIB, 
                                              NIB2Expander, RE2SW, SW2RE, 
                                              OFC2SW, SW2OFC, RE2NIB, OFC2NIB, 
                                              opRequest, transaction, 
                                              sw_status, sw_, 
                                              sw_status_update_, 
                                              sw_status_update_N, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_id, op, 
                                              sw >>

UpgraderWaitSWUndrained1(self) == /\ pc[self] = "UpgraderWaitSWUndrained1"
                                  /\ SwStatusUpgrader[sw_[self]] = SW_UNDRAINED
                                  /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                  /\ UNCHANGED << SwStatusNIB, 
                                                  SwStatusUpgrader, 
                                                  SwStatusExpander, SwStatusRE, 
                                                  SwStatusOFC, SwStatus, 
                                                  UpgraderRequestQueue, 
                                                  ExpanderRequestQueue, 
                                                  SWManagementQueue, 
                                                  DrainRequestQueue, 
                                                  Upgrader2NIB, NIB2Upgrader, 
                                                  Expander2NIB, NIB2Expander, 
                                                  RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                  RE2NIB, OFC2NIB, opRequest, 
                                                  transaction, sw_status, sw_, 
                                                  sw_status_update_, 
                                                  sw_status_update_N, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_id, 
                                                  op, sw >>

UpgraderDrainSW1(self) == /\ pc[self] = "UpgraderDrainSW1"
                          /\ SwStatusUpgrader[sw_[self]] = SW_UP
                          /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                          sw |-> sw_[self],
                                                                          value |-> SW_DRAINED])
                          /\ pc' = [pc EXCEPT ![self] = "UpgraderUndrainSW1"]
                          /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                          SwStatusExpander, SwStatusRE, 
                                          SwStatusOFC, SwStatus, 
                                          UpgraderRequestQueue, 
                                          ExpanderRequestQueue, 
                                          SWManagementQueue, Upgrader2NIB, 
                                          NIB2Upgrader, Expander2NIB, 
                                          NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                          SW2OFC, RE2NIB, OFC2NIB, opRequest, 
                                          transaction, sw_status, sw_, 
                                          sw_status_update_, 
                                          sw_status_update_N, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, op_, sw_id, op, sw >>

UpgraderUndrainSW1(self) == /\ pc[self] = "UpgraderUndrainSW1"
                            /\ SwStatusUpgrader[sw_[self]] = SW_DRAINED
                            /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> UNDRAIN_SW,
                                                                            sw |-> sw_[self],
                                                                            value |-> SW_UNDRAINED])
                            /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWUndrained"]
                            /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                            SwStatusExpander, SwStatusRE, 
                                            SwStatusOFC, SwStatus, 
                                            UpgraderRequestQueue, 
                                            ExpanderRequestQueue, 
                                            SWManagementQueue, Upgrader2NIB, 
                                            NIB2Upgrader, Expander2NIB, 
                                            NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                            SW2OFC, RE2NIB, OFC2NIB, opRequest, 
                                            transaction, sw_status, sw_, 
                                            sw_status_update_, 
                                            sw_status_update_N, req_, 
                                            sw_status_update_R, req, 
                                            sw_status_update, op_, sw_id, op, 
                                            sw >>

UpgraderWaitSWUndrained(self) == /\ pc[self] = "UpgraderWaitSWUndrained"
                                 /\ SwStatusUpgrader[sw_[self]] = SW_UNDRAINED
                                 /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                 /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                                 SwStatusExpander, SwStatusRE, 
                                                 SwStatusOFC, SwStatus, 
                                                 UpgraderRequestQueue, 
                                                 ExpanderRequestQueue, 
                                                 SWManagementQueue, 
                                                 DrainRequestQueue, 
                                                 Upgrader2NIB, NIB2Upgrader, 
                                                 Expander2NIB, NIB2Expander, 
                                                 RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                 RE2NIB, OFC2NIB, opRequest, 
                                                 transaction, sw_status, sw_, 
                                                 sw_status_update_, 
                                                 sw_status_update_N, req_, 
                                                 sw_status_update_R, req, 
                                                 sw_status_update, op_, sw_id, 
                                                 op, sw >>

UpgraderUndrainSW2(self) == /\ pc[self] = "UpgraderUndrainSW2"
                            /\ SwStatusUpgrader[sw_[self]] = SW_DRAINED
                            /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> UNDRAIN_SW,
                                                                            sw |-> sw_[self],
                                                                            value |-> SW_UNDRAINED])
                            /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWUndrained2"]
                            /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                            SwStatusExpander, SwStatusRE, 
                                            SwStatusOFC, SwStatus, 
                                            UpgraderRequestQueue, 
                                            ExpanderRequestQueue, 
                                            SWManagementQueue, Upgrader2NIB, 
                                            NIB2Upgrader, Expander2NIB, 
                                            NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                            SW2OFC, RE2NIB, OFC2NIB, opRequest, 
                                            transaction, sw_status, sw_, 
                                            sw_status_update_, 
                                            sw_status_update_N, req_, 
                                            sw_status_update_R, req, 
                                            sw_status_update, op_, sw_id, op, 
                                            sw >>

UpgraderWaitSWUndrained2(self) == /\ pc[self] = "UpgraderWaitSWUndrained2"
                                  /\ SwStatusUpgrader[sw_[self]] = SW_UNDRAINED
                                  /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                  /\ UNCHANGED << SwStatusNIB, 
                                                  SwStatusUpgrader, 
                                                  SwStatusExpander, SwStatusRE, 
                                                  SwStatusOFC, SwStatus, 
                                                  UpgraderRequestQueue, 
                                                  ExpanderRequestQueue, 
                                                  SWManagementQueue, 
                                                  DrainRequestQueue, 
                                                  Upgrader2NIB, NIB2Upgrader, 
                                                  Expander2NIB, NIB2Expander, 
                                                  RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                  RE2NIB, OFC2NIB, opRequest, 
                                                  transaction, sw_status, sw_, 
                                                  sw_status_update_, 
                                                  sw_status_update_N, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_id, 
                                                  op, sw >>

UpgraderDrainSW2(self) == /\ pc[self] = "UpgraderDrainSW2"
                          /\ SwStatusUpgrader[sw_[self]] = SW_UP
                          /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                          sw |-> sw_[self],
                                                                          value |-> SW_DRAINED])
                          /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWUndrained3"]
                          /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                          SwStatusExpander, SwStatusRE, 
                                          SwStatusOFC, SwStatus, 
                                          UpgraderRequestQueue, 
                                          ExpanderRequestQueue, 
                                          SWManagementQueue, Upgrader2NIB, 
                                          NIB2Upgrader, Expander2NIB, 
                                          NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                          SW2OFC, RE2NIB, OFC2NIB, opRequest, 
                                          transaction, sw_status, sw_, 
                                          sw_status_update_, 
                                          sw_status_update_N, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, op_, sw_id, op, sw >>

UpgraderWaitSWUndrained3(self) == /\ pc[self] = "UpgraderWaitSWUndrained3"
                                  /\ SwStatusUpgrader[sw_[self]] = SW_DRAINED
                                  /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                  /\ UNCHANGED << SwStatusNIB, 
                                                  SwStatusUpgrader, 
                                                  SwStatusExpander, SwStatusRE, 
                                                  SwStatusOFC, SwStatus, 
                                                  UpgraderRequestQueue, 
                                                  ExpanderRequestQueue, 
                                                  SWManagementQueue, 
                                                  DrainRequestQueue, 
                                                  Upgrader2NIB, NIB2Upgrader, 
                                                  Expander2NIB, NIB2Expander, 
                                                  RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                  RE2NIB, OFC2NIB, opRequest, 
                                                  transaction, sw_status, sw_, 
                                                  sw_status_update_, 
                                                  sw_status_update_N, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_id, 
                                                  op, sw >>

UpgraderWaitSWUndrained4(self) == /\ pc[self] = "UpgraderWaitSWUndrained4"
                                  /\ SwStatusUpgrader[sw_[self]] = SW_DRAINED
                                  /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                  /\ UNCHANGED << SwStatusNIB, 
                                                  SwStatusUpgrader, 
                                                  SwStatusExpander, SwStatusRE, 
                                                  SwStatusOFC, SwStatus, 
                                                  UpgraderRequestQueue, 
                                                  ExpanderRequestQueue, 
                                                  SWManagementQueue, 
                                                  DrainRequestQueue, 
                                                  Upgrader2NIB, NIB2Upgrader, 
                                                  Expander2NIB, NIB2Expander, 
                                                  RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                  RE2NIB, OFC2NIB, opRequest, 
                                                  transaction, sw_status, sw_, 
                                                  sw_status_update_, 
                                                  sw_status_update_N, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_id, 
                                                  op, sw >>

upgraderWorkerProcess(self) == UpgraderThread(self)
                                  \/ DequeueManagementRequest(self)
                                  \/ UpgraderAwaitSwDown1(self)
                                  \/ UpgraderAwaitSwDrained1(self)
                                  \/ UpgraderAwaitSwDown2(self)
                                  \/ UpgraderAwaitSwDown3(self)
                                  \/ UpgraderWaitSWUndrained1(self)
                                  \/ UpgraderDrainSW1(self)
                                  \/ UpgraderUndrainSW1(self)
                                  \/ UpgraderWaitSWUndrained(self)
                                  \/ UpgraderUndrainSW2(self)
                                  \/ UpgraderWaitSWUndrained2(self)
                                  \/ UpgraderDrainSW2(self)
                                  \/ UpgraderWaitSWUndrained3(self)
                                  \/ UpgraderWaitSWUndrained4(self)

UpgraderNIBEventHandlerProc(self) == /\ pc[self] = "UpgraderNIBEventHandlerProc"
                                     /\ NIB2Upgrader # <<>>
                                     /\ sw_status_update_' = [sw_status_update_ EXCEPT ![self] = Head(NIB2Upgrader)]
                                     /\ NIB2Upgrader' = Tail(NIB2Upgrader)
                                     /\ SwStatusUpgrader' = [SwStatusUpgrader EXCEPT ![sw_status_update_'[self].sw] = sw_status_update_'[self].value]
                                     /\ pc' = [pc EXCEPT ![self] = "UpgraderNIBEventHandlerProc"]
                                     /\ UNCHANGED << SwStatusNIB, 
                                                     SwStatusExpander, 
                                                     SwStatusRE, SwStatusOFC, 
                                                     SwStatus, 
                                                     UpgraderRequestQueue, 
                                                     ExpanderRequestQueue, 
                                                     SWManagementQueue, 
                                                     DrainRequestQueue, 
                                                     Upgrader2NIB, 
                                                     Expander2NIB, 
                                                     NIB2Expander, RE2SW, 
                                                     SW2RE, OFC2SW, SW2OFC, 
                                                     RE2NIB, OFC2NIB, 
                                                     opRequest, transaction, 
                                                     sw_status, sw_, 
                                                     sw_status_update_N, req_, 
                                                     sw_status_update_R, req, 
                                                     sw_status_update, op_, 
                                                     sw_id, op, sw >>

upgraderEventHandlerProcess(self) == UpgraderNIBEventHandlerProc(self)

NIBEventHandlerForREProc_(self) == /\ pc[self] = "NIBEventHandlerForREProc_"
                                   /\ RE2NIB # <<>>
                                   /\ sw_status_update_N' = [sw_status_update_N EXCEPT ![self] = Head(RE2NIB)]
                                   /\ RE2NIB' = Tail(RE2NIB)
                                   /\ SwStatusNIB' = [SwStatusNIB EXCEPT ![sw_status_update_N'[self].sw] = sw_status_update_N'[self].value]
                                   /\ NIB2Upgrader' =      Append(NIB2Upgrader, [type |-> MSG_SW_STATUS_CHANGE,
                                                      sw |-> sw_status_update_N'[self].sw,
                                                      value|-> sw_status_update_N'[self].value
                                                      ])
                                   /\ NIB2Expander' =      Append(NIB2Expander, [type |-> MSG_SW_STATUS_CHANGE,
                                                      sw |-> sw_status_update_N'[self].sw,
                                                      value|-> sw_status_update_N'[self].value
                                                      ])
                                   /\ pc' = [pc EXCEPT ![self] = "NIBEventHandlerForREProc_"]
                                   /\ UNCHANGED << SwStatusUpgrader, 
                                                   SwStatusExpander, 
                                                   SwStatusRE, SwStatusOFC, 
                                                   SwStatus, 
                                                   UpgraderRequestQueue, 
                                                   ExpanderRequestQueue, 
                                                   SWManagementQueue, 
                                                   DrainRequestQueue, 
                                                   Upgrader2NIB, Expander2NIB, 
                                                   RE2SW, SW2RE, OFC2SW, 
                                                   SW2OFC, OFC2NIB, opRequest, 
                                                   transaction, sw_status, sw_, 
                                                   sw_status_update_, req_, 
                                                   sw_status_update_R, req, 
                                                   sw_status_update, op_, 
                                                   sw_id, op, sw >>

NIBEventHandlerForRE(self) == NIBEventHandlerForREProc_(self)

NIBEventHandlerForREProc(self) == /\ pc[self] = "NIBEventHandlerForREProc"
                                  /\ OFC2NIB # <<>>
                                  /\ sw_status_update' = [sw_status_update EXCEPT ![self] = Head(OFC2NIB)]
                                  /\ OFC2NIB' = Tail(OFC2NIB)
                                  /\ SwStatusNIB' = [SwStatusNIB EXCEPT ![sw_status_update'[self].sw] = sw_status_update'[self].value]
                                  /\ NIB2Upgrader' =      Append(NIB2Upgrader, [type |-> MSG_SW_STATUS_CHANGE,
                                                     sw |-> sw_status_update'[self].sw,
                                                     value|-> sw_status_update'[self].value
                                                     ])
                                  /\ NIB2Expander' =      Append(NIB2Upgrader', [type |-> MSG_SW_STATUS_CHANGE,
                                                     sw |-> sw_status_update'[self].sw,
                                                     value|-> sw_status_update'[self].value
                                                     ])
                                  /\ pc' = [pc EXCEPT ![self] = "NIBEventHandlerForREProc"]
                                  /\ UNCHANGED << SwStatusUpgrader, 
                                                  SwStatusExpander, SwStatusRE, 
                                                  SwStatusOFC, SwStatus, 
                                                  UpgraderRequestQueue, 
                                                  ExpanderRequestQueue, 
                                                  SWManagementQueue, 
                                                  DrainRequestQueue, 
                                                  Upgrader2NIB, Expander2NIB, 
                                                  RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                  RE2NIB, opRequest, 
                                                  transaction, sw_status, sw_, 
                                                  sw_status_update_, 
                                                  sw_status_update_N, req_, 
                                                  sw_status_update_R, req, op_, 
                                                  sw_id, op, sw >>

NIBEventHandlerForOFC(self) == NIBEventHandlerForREProc(self)

REWorkerProc(self) == /\ pc[self] = "REWorkerProc"
                      /\ DrainRequestQueue # <<>>
                      /\ req_' = [req_ EXCEPT ![self] = Head(DrainRequestQueue)]
                      /\ DrainRequestQueue' = Tail(DrainRequestQueue)
                      /\ RE2SW' = [RE2SW EXCEPT ![req_'[self].sw] = Append(RE2SW[req_'[self].sw], req_'[self])]
                      /\ pc' = [pc EXCEPT ![self] = "REWorkerProc"]
                      /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                      SwStatusExpander, SwStatusRE, 
                                      SwStatusOFC, SwStatus, 
                                      UpgraderRequestQueue, 
                                      ExpanderRequestQueue, SWManagementQueue, 
                                      Upgrader2NIB, NIB2Upgrader, Expander2NIB, 
                                      NIB2Expander, SW2RE, OFC2SW, SW2OFC, 
                                      RE2NIB, OFC2NIB, opRequest, transaction, 
                                      sw_status, sw_, sw_status_update_, 
                                      sw_status_update_N, sw_status_update_R, 
                                      req, sw_status_update, op_, sw_id, op, 
                                      sw >>

REWorkerProcess(self) == REWorkerProc(self)

RESWEventHandlerProc(self) == /\ pc[self] = "RESWEventHandlerProc"
                              /\ SW2RE # <<>>
                              /\ sw_status_update_R' = [sw_status_update_R EXCEPT ![self] = Head(SW2RE)]
                              /\ SW2RE' = Tail(SW2RE)
                              /\ SwStatusRE' = [SwStatusRE EXCEPT ![sw_status_update_R'[self].sw] = sw_status_update_R'[self].value]
                              /\ RE2NIB' = Append(RE2NIB, [type |-> MSG_SW_STATUS_CHANGE,
                                            sw |-> sw_status_update_R'[self].sw,
                                            value|-> sw_status_update_R'[self].value
                                            ])
                              /\ pc' = [pc EXCEPT ![self] = "RESWEventHandlerProc"]
                              /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                              SwStatusExpander, SwStatusOFC, 
                                              SwStatus, UpgraderRequestQueue, 
                                              ExpanderRequestQueue, 
                                              SWManagementQueue, 
                                              DrainRequestQueue, Upgrader2NIB, 
                                              NIB2Upgrader, Expander2NIB, 
                                              NIB2Expander, RE2SW, OFC2SW, 
                                              SW2OFC, OFC2NIB, opRequest, 
                                              transaction, sw_status, sw_, 
                                              sw_status_update_, 
                                              sw_status_update_N, req_, req, 
                                              sw_status_update, op_, sw_id, op, 
                                              sw >>

RESWEventHandlerProcess(self) == RESWEventHandlerProc(self)

DrainerProc(self) == /\ pc[self] = "DrainerProc"
                     /\ SWManagementQueue # <<>>
                     /\ req' = [req EXCEPT ![self] = Head(SWManagementQueue)]
                     /\ SWManagementQueue' = Tail(SWManagementQueue)
                     /\ OFC2SW' = [OFC2SW EXCEPT ![req'[self].sw] = Append(OFC2SW[req'[self].sw], req'[self])]
                     /\ pc' = [pc EXCEPT ![self] = "DrainerProc"]
                     /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                     SwStatusExpander, SwStatusRE, SwStatusOFC, 
                                     SwStatus, UpgraderRequestQueue, 
                                     ExpanderRequestQueue, DrainRequestQueue, 
                                     Upgrader2NIB, NIB2Upgrader, Expander2NIB, 
                                     NIB2Expander, RE2SW, SW2RE, SW2OFC, 
                                     RE2NIB, OFC2NIB, opRequest, transaction, 
                                     sw_status, sw_, sw_status_update_, 
                                     sw_status_update_N, req_, 
                                     sw_status_update_R, sw_status_update, op_, 
                                     sw_id, op, sw >>

OFCSwitchManagementProcess(self) == DrainerProc(self)

OFCSWEventHandlingProc(self) == /\ pc[self] = "OFCSWEventHandlingProc"
                                /\ SW2OFC # <<>>
                                /\ sw_status_update' = [sw_status_update EXCEPT ![self] = Head(SW2OFC)]
                                /\ SW2OFC' = Tail(SW2OFC)
                                /\ SwStatusOFC' = [SwStatusOFC EXCEPT ![sw_status_update'[self].sw] = sw_status_update'[self].value]
                                /\ OFC2NIB' = Append(OFC2NIB, [type |-> MSG_SW_STATUS_CHANGE,
                                              sw |-> sw_status_update'[self].sw,
                                              value|-> sw_status_update'[self].value
                                              ])
                                /\ pc' = [pc EXCEPT ![self] = "OFCSWEventHandlingProc"]
                                /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                                SwStatusExpander, SwStatusRE, 
                                                SwStatus, UpgraderRequestQueue, 
                                                ExpanderRequestQueue, 
                                                SWManagementQueue, 
                                                DrainRequestQueue, 
                                                Upgrader2NIB, NIB2Upgrader, 
                                                Expander2NIB, NIB2Expander, 
                                                RE2SW, SW2RE, OFC2SW, RE2NIB, 
                                                opRequest, transaction, 
                                                sw_status, sw_, 
                                                sw_status_update_, 
                                                sw_status_update_N, req_, 
                                                sw_status_update_R, req, op_, 
                                                sw_id, op, sw >>

OFCSWEventHandlerProcess(self) == OFCSWEventHandlingProc(self)

SWManagementProc_(self) == /\ pc[self] = "SWManagementProc_"
                           /\ OFC2SW[sw_id[self]] # <<>>
                           /\ op_' = [op_ EXCEPT ![self] = Head(OFC2SW[sw_id[self]])]
                           /\ Assert(op_'[self].type = MSG_SW_STATUS_CHANGE, 
                                     "Failure of assertion at line 373, column 13.")
                           /\ OFC2SW' = [OFC2SW EXCEPT ![sw_id[self]] = Tail(OFC2SW[sw_id[self]])]
                           /\ IF op_'[self].value = SW_DRAINED
                                 THEN /\ Assert(SwStatus[sw_id[self]] = SW_DOWN, 
                                                "Failure of assertion at line 376, column 17.")
                                      /\ SwStatus' = [SwStatus EXCEPT ![sw_id[self]] = SW_DRAINED]
                                 ELSE /\ IF op_'[self].value = SW_DOWN
                                            THEN /\ Assert(SwStatus[sw_id[self]] = SW_DRAINED, 
                                                           "Failure of assertion at line 379, column 17.")
                                                 /\ SwStatus' = [SwStatus EXCEPT ![sw_id[self]] = SW_DOWN]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED SwStatus
                           /\ SW2OFC' = Append(SW2OFC, [type |-> MSG_SW_STATUS_CHANGE,
                                         sw |-> sw_id[self],
                                         value|-> SwStatus'[sw_id[self]]
                                         ])
                           /\ pc' = [pc EXCEPT ![self] = "SWManagementProc_"]
                           /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                           SwStatusExpander, SwStatusRE, 
                                           SwStatusOFC, UpgraderRequestQueue, 
                                           ExpanderRequestQueue, 
                                           SWManagementQueue, 
                                           DrainRequestQueue, Upgrader2NIB, 
                                           NIB2Upgrader, Expander2NIB, 
                                           NIB2Expander, RE2SW, SW2RE, RE2NIB, 
                                           OFC2NIB, opRequest, transaction, 
                                           sw_status, sw_, sw_status_update_, 
                                           sw_status_update_N, req_, 
                                           sw_status_update_R, req, 
                                           sw_status_update, sw_id, op, sw >>

swManagementProcess(self) == SWManagementProc_(self)

SWManagementProc(self) == /\ pc[self] = "SWManagementProc"
                          /\ RE2SW[sw[self]] # <<>>
                          /\ op' = [op EXCEPT ![self] = Head(RE2SW[sw[self]])]
                          /\ Assert(op'[self].sw = sw[self], 
                                    "Failure of assertion at line 400, column 13.")
                          /\ Assert(op'[self].type = MSG_SW_STATUS_CHANGE, 
                                    "Failure of assertion at line 401, column 13.")
                          /\ RE2SW' = [RE2SW EXCEPT ![sw[self]] = Tail(RE2SW[sw[self]])]
                          /\ IF op'[self].value = SW_DRAINED
                                THEN /\ IF SwStatus[sw[self]] # SW_DRAINED
                                           THEN /\ Assert(SwStatus[sw[self]] = SW_UNDRAINED, 
                                                          "Failure of assertion at line 405, column 21.")
                                                /\ SwStatus' = [SwStatus EXCEPT ![sw[self]] = SW_DRAINED]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED SwStatus
                                ELSE /\ IF op'[self].value = SW_UNDRAINED
                                           THEN /\ IF SwStatus[sw[self]] # SW_UNDRAINED
                                                      THEN /\ Assert(SwStatus[sw[self]] = SW_DRAINED, 
                                                                     "Failure of assertion at line 410, column 21.")
                                                           /\ SwStatus' = [SwStatus EXCEPT ![sw[self]] = SW_UNDRAINED]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED SwStatus
                                           ELSE /\ Assert(FALSE, 
                                                          "Failure of assertion at line 414, column 17.")
                                                /\ UNCHANGED SwStatus
                          /\ SW2RE' = Append(SW2RE, [type |-> MSG_SW_STATUS_CHANGE,
                                        sw |-> sw[self],
                                        value|-> SwStatus'[sw[self]]
                                        ])
                          /\ pc' = [pc EXCEPT ![self] = "SWManagementProc"]
                          /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                          SwStatusExpander, SwStatusRE, 
                                          SwStatusOFC, UpgraderRequestQueue, 
                                          ExpanderRequestQueue, 
                                          SWManagementQueue, DrainRequestQueue, 
                                          Upgrader2NIB, NIB2Upgrader, 
                                          Expander2NIB, NIB2Expander, OFC2SW, 
                                          SW2OFC, RE2NIB, OFC2NIB, opRequest, 
                                          transaction, sw_status, sw_, 
                                          sw_status_update_, 
                                          sw_status_update_N, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, op_, sw_id, sw >>

swIRProcess(self) == SWManagementProc(self)

Next == (\E self \in ({UPGRADER} \X {CONT_WORKER}): upgraderWorkerProcess(self))
           \/ (\E self \in ({UPGRADER} \X {CONT_EVENT_HANDLER}): upgraderEventHandlerProcess(self))
           \/ (\E self \in ({NIB} \X {CONT_EVENT_HANDLER}): NIBEventHandlerForRE(self))
           \/ (\E self \in ({NIB} \X {CONT_EVENT_HANDLER}): NIBEventHandlerForOFC(self))
           \/ (\E self \in ({RE} \X {CONT_WORKER}): REWorkerProcess(self))
           \/ (\E self \in ({RE} \X {CONT_EVENT_HANDLER}): RESWEventHandlerProcess(self))
           \/ (\E self \in ({OFC} \X {CONT_SW_MANAGEMENT}): OFCSwitchManagementProcess(self))
           \/ (\E self \in ({OFC} \X {CONT_EVENT_HANDLER}): OFCSWEventHandlerProcess(self))
           \/ (\E self \in ({SW_MANAGE_PROC} \X SW): swManagementProcess(self))
           \/ (\E self \in ({SW_SIMPLE_ID} \X SW): swIRProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({UPGRADER} \X {CONT_WORKER}) : WF_vars(upgraderWorkerProcess(self))
        /\ \A self \in ({UPGRADER} \X {CONT_EVENT_HANDLER}) : WF_vars(upgraderEventHandlerProcess(self))
        /\ \A self \in ({NIB} \X {CONT_EVENT_HANDLER}) : WF_vars(NIBEventHandlerForRE(self))
        /\ \A self \in ({NIB} \X {CONT_EVENT_HANDLER}) : WF_vars(NIBEventHandlerForOFC(self))
        /\ \A self \in ({RE} \X {CONT_WORKER}) : WF_vars(REWorkerProcess(self))
        /\ \A self \in ({RE} \X {CONT_EVENT_HANDLER}) : WF_vars(RESWEventHandlerProcess(self))
        /\ \A self \in ({OFC} \X {CONT_SW_MANAGEMENT}) : WF_vars(OFCSwitchManagementProcess(self))
        /\ \A self \in ({OFC} \X {CONT_EVENT_HANDLER}) : WF_vars(OFCSWEventHandlerProcess(self))
        /\ \A self \in ({SW_MANAGE_PROC} \X SW) : WF_vars(swManagementProcess(self))
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(swIRProcess(self))

\* END TRANSLATION 
DrainLivenessProp == <>[] (/\ UpgraderRequestQueue = <<>>
                           /\ ExpanderRequestQueue = <<>>)
    
=============================================================================
    

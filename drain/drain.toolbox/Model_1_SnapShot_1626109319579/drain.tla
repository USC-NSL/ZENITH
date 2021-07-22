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
          CONT_EVENT_HANDLER_NIB_FOR_RE,
          CONT_EVENT_HANDLER_NIB_FOR_OFC,
\*          CONT_EVENT_HANDLER_NIB_FOR_DRAINER,
          CONT_WORKER,
          CONT_SW_MANAGEMENT
\*          CONT_DRAIN_WORKER,
\*          CONT_UPDOWN_WORKER
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
                UpgraderWaitSWDrained3:
                    await SwStatusUpgrader[sw] = SW_DRAINED;
                    goto DequeueManagementRequest;    
            elsif sw_status \in {SW_UNDRAINED, SW_UP} then
                DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                UpgraderWaitSWDrained4:
                    await SwStatusUpgrader[sw] = SW_DRAINED;
                    goto DequeueManagementRequest;                                                  
            else
                assert FALSE;
            end if; 
        else
            assert FALSE;
        end if;
        DequeueManagementRequest:
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
    (*                            Expander                             *)
    (*******************************************************************)
    
    \* ============ Upgrader Worker ====================================
    \* ============ Use blocking mode for design =======================
    fair process expanderWorkerProcess \in ({EXPANDER} \X {CONT_WORKER})
    variables opRequest = [type |-> 0], 
              transaction = <<>>,
              sw_status = NULL,
              sw = NULL;
    begin
    ExpanderThread:
    while TRUE do
        await ExpanderRequestQueue # <<>>;
        opRequest := Head(ExpanderRequestQueue);
        sw := opRequest.sw;
        assert opRequest.type \in {DOWN_SW, UP_SW, DRAIN_SW, UNDRAIN_SW};
        
        if opRequest.type = DOWN_SW then \* target state is SW_DOWN
            \* Read NIB to check the switch status
            sw_status := SwStatusExpander[sw];      
            if sw_status = SW_DRAINED then
                \* SW_DRAINED->SW_DOWN
                 SWManagementQueue := Append(SWManagementQueue, [type |-> DOWN_SW, 
                                                                sw |-> sw,
                                                                value |-> SW_DOWN]);
                 \* await switch turned to be SW_DOWN -> dequeue request
                 ExpanderAwaitSwDown1:
                    await SwStatusExpander[sw] = SW_DOWN;
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
                 ExpanderAwaitSwDrained1:
                    if SwStatusExpander[sw] = SW_DOWN then
                        goto DequeueManagementRequest;
                    else
                        await SwStatusExpander[sw] = SW_DRAINED;
                        SWManagementQueue := Append(SWManagementQueue, [type |-> DOWN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DOWN]);
                    end if;
                 \* SW_DOWN -> dequeue request
                 ExpanderAwaitSwDown2:
                    await SwStatusExpander[sw] = SW_DOWN;
                    goto DequeueManagementRequest;
            elsif sw_status = SW_UP then
                SWManagementQueue := Append(SWManagementQueue, [type |-> DOWN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DOWN]);
                ExpanderAwaitSwDown3:
                    await SwStatusExpander[sw] = SW_DOWN;
                    goto DequeueManagementRequest;
            else 
                assert FALSE;           
            end if;
        elsif opRequest.type = UNDRAIN_SW then \*target state is SW_UNDRAINED
            sw_status := SwStatusExpander[sw];
            if sw_status = SW_DRAINED then
                \* SW_DRAINED->SW_UNDRAINED
                DrainRequestQueue := Append(DrainRequestQueue, [type |-> UNDRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UNDRAINED]);
                \* SW_UNDRAINED -> dequeue request
                ExpanderWaitSWUndrained1:
                    await SwStatusExpander[sw] = SW_UNDRAINED;
                    goto DequeueManagementRequest;
            elsif sw_status = SW_DOWN then
                SWManagementQueue := Append(SWManagementQueue, [type |-> UP_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UP]);
                ExpanderDrainSW1:
                    await SwStatusExpander[sw] = SW_UP;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                
                ExpanderUndrainSW1:
                    await SwStatusExpander[sw] = SW_DRAINED;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> UNDRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UNDRAINED]);
                \* SW_UNDRAINED -> dequeue request
                ExpanderWaitSWUndrained:
                    await SwStatusExpander[sw] = SW_UNDRAINED;
                    goto DequeueManagementRequest;
                
            elsif sw_status = SW_UP then
                DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                
                ExpanderUndrainSW2:
                    await SwStatusExpander[sw] = SW_DRAINED;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> UNDRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UNDRAINED]);
                \* SW_UNDRAINED -> dequeue request
                ExpanderWaitSWUndrained2:
                    await SwStatusExpander[sw] = SW_UNDRAINED;
                    goto DequeueManagementRequest;
            elsif sw_status = SW_UNDRAINED then
                \* target state reached
                skip;
            else
                assert FALSE;
            end if;
        elsif opRequest.type = DRAIN_SW then \*target state is SW_DRAINED
            sw_status := SwStatusExpander[sw];
            if sw_status = SW_DRAINED then
                goto DequeueManagementRequest;
            elsif sw_status = SW_DOWN then
                SWManagementQueue := Append(SWManagementQueue, [type |-> UP_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_UP]);
                ExpanderDrainSW2:
                    await SwStatusExpander[sw] = SW_UP;
                    DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                ExpanderWaitSWUndrained3:
                    await SwStatusExpander[sw] = SW_DRAINED;
                    goto DequeueManagementRequest;    
            elsif sw_status \in {SW_UNDRAINED, SW_UP} then
                DrainRequestQueue := Append(DrainRequestQueue, [type |-> DRAIN_SW, 
                                                                 sw |-> sw,
                                                                 value |-> SW_DRAINED]);
                ExpanderWaitSWUndrained4:
                    await SwStatusExpander[sw] = SW_DRAINED;
                    goto DequeueManagementRequest;                                                  
            else
                assert FALSE;
            end if; 
        else
            assert FALSE;
        end if;
        DequeueManagementRequest:
            ExpanderRequestQueue := Tail(ExpanderRequestQueue);
    end while;
    end process;
    
    \* ============ Expander NIB Event Handler =================
    \* ============ Assumption: update is always for a single object, such as IR/SW_STATUS
    fair process expanderEventHandlerProcess \in ({EXPANDER} \X {CONT_EVENT_HANDLER})
    variables sw_status_update = [type |-> NULL]
    begin
    ExpanderNIBEventHandlerProc:
        while TRUE do 
            await NIB2Expander # <<>>;
            sw_status_update := Head(NIB2Expander);
            NIB2Expander :=  Tail(NIB2Expander);
            SwStatusExpander[sw_status_update.sw] := sw_status_update.value;
        end while;

    end process;
    
    
    (*******************************************************************)
    (********************** Network Information Base *******************)
    (*******************************************************************)
    fair process NIBEventHandlerForRE \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_RE})
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
    
    fair process NIBEventHandlerForOFC \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_OFC})
    variables sw_status_update = [type |-> NULL]
    begin
    NIBEventHandlerForOFCProc:
        while TRUE do
            await OFC2NIB # <<>>;
            sw_status_update := Head(OFC2NIB);
            OFC2NIB :=  Tail(OFC2NIB);
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
    
\*    fair process NIBEventHandlerForDrainer \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_DRAINER})
\*    variables sw_status_update = [type |-> NULL]
\*    begin
\*    NIBEventHandlerForDrainerProc:
\*        while TRUE do
\*            await Drainer2NIB # <<>>;
\*            sw_status_update := Head(Drainer2NIB);
\*            Drainer2NIB :=  Tail(Drainer2NIB);
\*            SwStatusNIB[sw_status_update.sw] := sw_status_update.value;
\*            NIB2RE := Append(NIB2RE, [type |-> MSG_SW_STATUS_CHANGE,
\*                       sw |-> sw_status_update.sw, 
\*                       value|-> sw_status_update.value
\*                       ]);
\*            NIB2Expander := Append(NIB2Expander, [type |-> MSG_SW_STATUS_CHANGE,
\*                       sw |-> sw_status_update.sw, 
\*                       value|-> sw_status_update.value
\*                       ]);
\*        end while;
\*    end process;
 
\*    (*******************************************************************)
\*    (*                               Drainer                              *)
\*    (*******************************************************************)
\*    \*---------------- Drainer worker for drain request--------------------------
\*    fair process DrainerDrainWorkerProcess \in ({DRAINER} \X {CONT_DRAIN_WORKER})
\*    variables req = [type |-> NULL]
\*    begin
\*    REWorkerProc:
\*        while TRUE do
\*            await DrainRequestQueue # <<>>;
\*            req := Head(DrainRequestQueue);
\*            DrainRequestQueue := Tail(DrainRequestQueue);
\*            Drainer2NIB[req.sw] := Append(Drainer2NIB[req.sw], req);
\*        end while;
\*    end process;
\*    
\*    \*---------------- Drainer worker for sw_updown request--------------------------
\*    fair process DrainerUpDownWorkerProcess \in ({DRAINER} \X {CONT_UPDOWN_WORKER})
\*    variables req = [type |-> NULL]
\*    begin
\*    REWorkerProc:
\*        while TRUE do
\*            await SWManagementQueue # <<>>;
\*            req := Head(SWManagementQueue);
\*            SWManagementQueue := Tail(SWManagementQueue);
\*            Drainer2NIB[req.sw] := Append(Drainer2NIB[req.sw], req);
\*        end while;
\*    end process;
\* 
\*    \*---------------------- Drainer NIB Event Handler-----------------------------
\*    fair process DrainerNIBEventHandlerProcess \in ({DRAINER} \X {CONT_EVENT_HANDLER})
\*    variables nib_update = [type |-> NULL]
\*    begin
\*    RESWEventHandlerProc:
\*        while TRUE do
\*            await NIB2Drainer # <<>>;
\*            nib_update := Head(NIB2Drainer);
\*            \* Requests from applications. 
\*            \* Forward those to RE/OFC if legal (ie, state machine is respected)
\*            if nib_update.type \in {UP_SW, DOWN_SW, DRAIN_SW, UNDRAIN_SW} then
\*                
\*                
\*            elsif nib_update.type = MSG_SW_STATUS_CHANGE then  \* Switch status update
\*                
\*            
\*            else 
\*                assert FALSE;
\*            end if;
\*            
\*            SW2RE :=  Tail(SW2RE);
\*            SwStatusRE[sw_status_update.sw] := sw_status_update.value;
\*            RE2NIB := Append(RE2NIB, [type |-> MSG_SW_STATUS_CHANGE,
\*                       sw |-> sw_status_update.sw, 
\*                       value|-> sw_status_update.value
\*                       ]);
\*        end while;
\*    end process;
 
    (***********************************************************************)
    (*                                 RE/Drainer                          *)
    (*In this spec, we merge RE/Drainer into a single module for simplicity*)
    (***********************************************************************)
    \*---------------------- RE worker---------------------------------
    fair process REWorkerProcess \in ({RE} \X {CONT_WORKER})
    variables req = [type |-> NULL]
    begin
    REWorkerProc:
        while TRUE do
            await DrainRequestQueue # <<>>;
            req := Head(DrainRequestQueue);
            assert req.type \in {DRAIN_SW, UNDRAIN_SW};
            DrainRequestQueue := Tail(DrainRequestQueue);
\*            if SwStatusRE[req.sw] \notin {UP_ONGO, DOWN_ONGO, DRAIN_ONGO, UNDRAIN_ONGO} then
\*                if req.type = DRAIN_SW then
\*                    
\*                elsif req.type = UNDRAIN_SW then
\*                    
\*                end if;
\*            else
\*            end if;
            
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
    OFCProc:
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
    variables op = [type |-> NULL], sw = self[2];
    begin
        SWManagementProc:
        while TRUE do
            await OFC2SW[sw] # <<>>;
            op := Head(OFC2SW[sw]);
            assert op.type \in {UP_SW, DOWN_SW};
            OFC2SW[sw] := Tail(OFC2SW[sw]);
            if op.value = SW_DRAINED then
                SwStatus[sw] := SW_DRAINED; 
            elsif op.value = SW_DOWN then
                assert SwStatus[sw] # SW_UNDRAINED;
                SwStatus[sw] := SW_DOWN;
            elsif op.value = SW_UP then
                SwStatus[sw] := SW_UP;
            end if;
            SW2OFC := Append(SW2OFC, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw, 
                       value|-> SwStatus[sw]
                       ]);
            SW2RE := Append(SW2RE, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw, 
                       value|-> SwStatus[sw]
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
        SWIRProc:
        while TRUE do
            await RE2SW[sw] # <<>>;
            op := Head(RE2SW[sw]);
            assert op.sw = sw;
            assert op.type \in {DRAIN_SW, UNDRAIN_SW};
            RE2SW[sw] := Tail(RE2SW[sw]);
            if op.value = SW_DRAINED then
                SwStatus[sw] := SW_DRAINED; 
            elsif op.value = SW_UNDRAINED then
                SwStatus[sw] := SW_UNDRAINED; 
            else
                assert FALSE;
            end if;
            SW2RE := Append(SW2RE, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw, 
                       value|-> SwStatus[sw]
                       ]);
            SW2OFC := Append(SW2OFC, [type |-> MSG_SW_STATUS_CHANGE,
                       sw |-> sw, 
                       value|-> SwStatus[sw]
                       ]);
        end while;
    end process;
end algorithm
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "c112a4e7" /\ chksum(tla) = "79e26c83")
\* Label DequeueManagementRequest of process upgraderWorkerProcess at line 220 col 13 changed to DequeueManagementRequest_
\* Process variable opRequest of process upgraderWorkerProcess at line 83 col 15 changed to opRequest_
\* Process variable transaction of process upgraderWorkerProcess at line 84 col 15 changed to transaction_
\* Process variable sw_status of process upgraderWorkerProcess at line 85 col 15 changed to sw_status_
\* Process variable sw of process upgraderWorkerProcess at line 86 col 15 changed to sw_
\* Process variable sw_status_update of process upgraderEventHandlerProcess at line 227 col 15 changed to sw_status_update_
\* Process variable sw of process expanderWorkerProcess at line 250 col 15 changed to sw_e
\* Process variable sw_status_update of process expanderEventHandlerProcess at line 391 col 15 changed to sw_status_update_e
\* Process variable sw_status_update of process NIBEventHandlerForRE at line 408 col 15 changed to sw_status_update_N
\* Process variable sw_status_update of process NIBEventHandlerForOFC at line 428 col 15 changed to sw_status_update_NI
\* Process variable req of process REWorkerProcess at line 531 col 15 changed to req_
\* Process variable sw_status_update of process RESWEventHandlerProcess at line 557 col 15 changed to sw_status_update_R
\* Process variable op of process swManagementProcess at line 609 col 15 changed to op_
\* Process variable sw of process swManagementProcess at line 609 col 37 changed to sw_s
VARIABLES SwStatusNIB, SwStatusUpgrader, SwStatusExpander, SwStatusRE, 
          SwStatusOFC, SwStatus, UpgraderRequestQueue, ExpanderRequestQueue, 
          SWManagementQueue, DrainRequestQueue, Upgrader2NIB, NIB2Upgrader, 
          Expander2NIB, NIB2Expander, RE2SW, SW2RE, OFC2SW, SW2OFC, RE2NIB, 
          OFC2NIB, pc

(* define statement *)
max(set) == CHOOSE x \in set: \A y \in set: x \geq y
min(set) == CHOOSE x \in set: \A y \in set: x \leq y

VARIABLES opRequest_, transaction_, sw_status_, sw_, sw_status_update_, 
          opRequest, transaction, sw_status, sw_e, sw_status_update_e, 
          sw_status_update_N, sw_status_update_NI, req_, sw_status_update_R, 
          req, sw_status_update, op_, sw_s, op, sw

vars == << SwStatusNIB, SwStatusUpgrader, SwStatusExpander, SwStatusRE, 
           SwStatusOFC, SwStatus, UpgraderRequestQueue, ExpanderRequestQueue, 
           SWManagementQueue, DrainRequestQueue, Upgrader2NIB, NIB2Upgrader, 
           Expander2NIB, NIB2Expander, RE2SW, SW2RE, OFC2SW, SW2OFC, RE2NIB, 
           OFC2NIB, pc, opRequest_, transaction_, sw_status_, sw_, 
           sw_status_update_, opRequest, transaction, sw_status, sw_e, 
           sw_status_update_e, sw_status_update_N, sw_status_update_NI, req_, 
           sw_status_update_R, req, sw_status_update, op_, sw_s, op, sw >>

ProcSet == (({UPGRADER} \X {CONT_WORKER})) \cup (({UPGRADER} \X {CONT_EVENT_HANDLER})) \cup (({EXPANDER} \X {CONT_WORKER})) \cup (({EXPANDER} \X {CONT_EVENT_HANDLER})) \cup (({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_RE})) \cup (({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_OFC})) \cup (({RE} \X {CONT_WORKER})) \cup (({RE} \X {CONT_EVENT_HANDLER})) \cup (({OFC} \X {CONT_SW_MANAGEMENT})) \cup (({OFC} \X {CONT_EVENT_HANDLER})) \cup (({SW_MANAGE_PROC} \X SW)) \cup (({SW_SIMPLE_ID} \X SW))

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
        /\ opRequest_ = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> [type |-> 0]]
        /\ transaction_ = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> <<>>]
        /\ sw_status_ = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> NULL]
        /\ sw_ = [self \in ({UPGRADER} \X {CONT_WORKER}) |-> NULL]
        (* Process upgraderEventHandlerProcess *)
        /\ sw_status_update_ = [self \in ({UPGRADER} \X {CONT_EVENT_HANDLER}) |-> [type |-> NULL]]
        (* Process expanderWorkerProcess *)
        /\ opRequest = [self \in ({EXPANDER} \X {CONT_WORKER}) |-> [type |-> 0]]
        /\ transaction = [self \in ({EXPANDER} \X {CONT_WORKER}) |-> <<>>]
        /\ sw_status = [self \in ({EXPANDER} \X {CONT_WORKER}) |-> NULL]
        /\ sw_e = [self \in ({EXPANDER} \X {CONT_WORKER}) |-> NULL]
        (* Process expanderEventHandlerProcess *)
        /\ sw_status_update_e = [self \in ({EXPANDER} \X {CONT_EVENT_HANDLER}) |-> [type |-> NULL]]
        (* Process NIBEventHandlerForRE *)
        /\ sw_status_update_N = [self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_RE}) |-> [type |-> NULL]]
        (* Process NIBEventHandlerForOFC *)
        /\ sw_status_update_NI = [self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_OFC}) |-> [type |-> NULL]]
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
        /\ sw_s = [self \in ({SW_MANAGE_PROC} \X SW) |-> self[2]]
        (* Process swIRProcess *)
        /\ op = [self \in ({SW_SIMPLE_ID} \X SW) |-> [type |-> NULL]]
        /\ sw = [self \in ({SW_SIMPLE_ID} \X SW) |-> self[2]]
        /\ pc = [self \in ProcSet |-> CASE self \in ({UPGRADER} \X {CONT_WORKER}) -> "UpgraderThread"
                                        [] self \in ({UPGRADER} \X {CONT_EVENT_HANDLER}) -> "UpgraderNIBEventHandlerProc"
                                        [] self \in ({EXPANDER} \X {CONT_WORKER}) -> "ExpanderThread"
                                        [] self \in ({EXPANDER} \X {CONT_EVENT_HANDLER}) -> "ExpanderNIBEventHandlerProc"
                                        [] self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_RE}) -> "NIBEventHandlerForREProc"
                                        [] self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_OFC}) -> "NIBEventHandlerForOFCProc"
                                        [] self \in ({RE} \X {CONT_WORKER}) -> "REWorkerProc"
                                        [] self \in ({RE} \X {CONT_EVENT_HANDLER}) -> "RESWEventHandlerProc"
                                        [] self \in ({OFC} \X {CONT_SW_MANAGEMENT}) -> "OFCProc"
                                        [] self \in ({OFC} \X {CONT_EVENT_HANDLER}) -> "OFCSWEventHandlingProc"
                                        [] self \in ({SW_MANAGE_PROC} \X SW) -> "SWManagementProc"
                                        [] self \in ({SW_SIMPLE_ID} \X SW) -> "SWIRProc"]

UpgraderThread(self) == /\ pc[self] = "UpgraderThread"
                        /\ UpgraderRequestQueue # <<>>
                        /\ opRequest_' = [opRequest_ EXCEPT ![self] = Head(UpgraderRequestQueue)]
                        /\ sw_' = [sw_ EXCEPT ![self] = opRequest_'[self].sw]
                        /\ Assert(opRequest_'[self].type \in {DOWN_SW, UP_SW, DRAIN_SW, UNDRAIN_SW}, 
                                  "Failure of assertion at line 93, column 9.")
                        /\ IF opRequest_'[self].type = DOWN_SW
                              THEN /\ sw_status_' = [sw_status_ EXCEPT ![self] = SwStatusUpgrader[sw_'[self]]]
                                   /\ IF sw_status_'[self] = SW_DRAINED
                                         THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                                sw |-> sw_'[self],
                                                                                                value |-> SW_DOWN])
                                              /\ pc' = [pc EXCEPT ![self] = "UpgraderAwaitSwDown1"]
                                              /\ UNCHANGED DrainRequestQueue
                                         ELSE /\ IF sw_status_'[self] = SW_DOWN
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
                                                         /\ UNCHANGED << SWManagementQueue, 
                                                                         DrainRequestQueue >>
                                                    ELSE /\ IF sw_status_'[self] = SW_UNDRAINED
                                                               THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                       sw |-> sw_'[self],
                                                                                                                       value |-> SW_DRAINED])
                                                                    /\ pc' = [pc EXCEPT ![self] = "UpgraderAwaitSwDrained1"]
                                                                    /\ UNCHANGED SWManagementQueue
                                                               ELSE /\ IF sw_status_'[self] = SW_UP
                                                                          THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                                                                   sw |-> sw_'[self],
                                                                                                                                   value |-> SW_DOWN])
                                                                               /\ pc' = [pc EXCEPT ![self] = "UpgraderAwaitSwDown3"]
                                                                          ELSE /\ Assert(FALSE, 
                                                                                         "Failure of assertion at line 137, column 17.")
                                                                               /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
                                                                               /\ UNCHANGED SWManagementQueue
                                                                    /\ UNCHANGED DrainRequestQueue
                              ELSE /\ IF opRequest_'[self].type = UNDRAIN_SW
                                         THEN /\ sw_status_' = [sw_status_ EXCEPT ![self] = SwStatusUpgrader[sw_'[self]]]
                                              /\ IF sw_status_'[self] = SW_DRAINED
                                                    THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> UNDRAIN_SW,
                                                                                                             sw |-> sw_'[self],
                                                                                                             value |-> SW_UNDRAINED])
                                                         /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWUndrained1"]
                                                         /\ UNCHANGED SWManagementQueue
                                                    ELSE /\ IF sw_status_'[self] = SW_DOWN
                                                               THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> UP_SW,
                                                                                                                        sw |-> sw_'[self],
                                                                                                                        value |-> SW_UP])
                                                                    /\ pc' = [pc EXCEPT ![self] = "UpgraderDrainSW1"]
                                                                    /\ UNCHANGED DrainRequestQueue
                                                               ELSE /\ IF sw_status_'[self] = SW_UP
                                                                          THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                                   sw |-> sw_'[self],
                                                                                                                                   value |-> SW_DRAINED])
                                                                               /\ pc' = [pc EXCEPT ![self] = "UpgraderUndrainSW2"]
                                                                          ELSE /\ IF sw_status_'[self] = SW_UNDRAINED
                                                                                     THEN /\ TRUE
                                                                                     ELSE /\ Assert(FALSE, 
                                                                                                    "Failure of assertion at line 188, column 17.")
                                                                               /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
                                                                               /\ UNCHANGED DrainRequestQueue
                                                                    /\ UNCHANGED SWManagementQueue
                                         ELSE /\ IF opRequest_'[self].type = DRAIN_SW
                                                    THEN /\ sw_status_' = [sw_status_ EXCEPT ![self] = SwStatusUpgrader[sw_'[self]]]
                                                         /\ IF sw_status_'[self] = SW_DRAINED
                                                               THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
                                                                    /\ UNCHANGED << SWManagementQueue, 
                                                                                    DrainRequestQueue >>
                                                               ELSE /\ IF sw_status_'[self] = SW_DOWN
                                                                          THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> UP_SW,
                                                                                                                                   sw |-> sw_'[self],
                                                                                                                                   value |-> SW_UP])
                                                                               /\ pc' = [pc EXCEPT ![self] = "UpgraderDrainSW2"]
                                                                               /\ UNCHANGED DrainRequestQueue
                                                                          ELSE /\ IF sw_status_'[self] \in {SW_UNDRAINED, SW_UP}
                                                                                     THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                                              sw |-> sw_'[self],
                                                                                                                                              value |-> SW_DRAINED])
                                                                                          /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWDrained4"]
                                                                                     ELSE /\ Assert(FALSE, 
                                                                                                    "Failure of assertion at line 214, column 17.")
                                                                                          /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
                                                                                          /\ UNCHANGED DrainRequestQueue
                                                                               /\ UNCHANGED SWManagementQueue
                                                    ELSE /\ Assert(FALSE, 
                                                                   "Failure of assertion at line 217, column 13.")
                                                         /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
                                                         /\ UNCHANGED << SWManagementQueue, 
                                                                         DrainRequestQueue, 
                                                                         sw_status_ >>
                        /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                        SwStatusExpander, SwStatusRE, 
                                        SwStatusOFC, SwStatus, 
                                        UpgraderRequestQueue, 
                                        ExpanderRequestQueue, Upgrader2NIB, 
                                        NIB2Upgrader, Expander2NIB, 
                                        NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                        SW2OFC, RE2NIB, OFC2NIB, transaction_, 
                                        sw_status_update_, opRequest, 
                                        transaction, sw_status, sw_e, 
                                        sw_status_update_e, sw_status_update_N, 
                                        sw_status_update_NI, req_, 
                                        sw_status_update_R, req, 
                                        sw_status_update, op_, sw_s, op, sw >>

DequeueManagementRequest_(self) == /\ pc[self] = "DequeueManagementRequest_"
                                   /\ UpgraderRequestQueue' = Tail(UpgraderRequestQueue)
                                   /\ pc' = [pc EXCEPT ![self] = "UpgraderThread"]
                                   /\ UNCHANGED << SwStatusNIB, 
                                                   SwStatusUpgrader, 
                                                   SwStatusExpander, 
                                                   SwStatusRE, SwStatusOFC, 
                                                   SwStatus, 
                                                   ExpanderRequestQueue, 
                                                   SWManagementQueue, 
                                                   DrainRequestQueue, 
                                                   Upgrader2NIB, NIB2Upgrader, 
                                                   Expander2NIB, NIB2Expander, 
                                                   RE2SW, SW2RE, OFC2SW, 
                                                   SW2OFC, RE2NIB, OFC2NIB, 
                                                   opRequest_, transaction_, 
                                                   sw_status_, sw_, 
                                                   sw_status_update_, 
                                                   opRequest, transaction, 
                                                   sw_status, sw_e, 
                                                   sw_status_update_e, 
                                                   sw_status_update_N, 
                                                   sw_status_update_NI, req_, 
                                                   sw_status_update_R, req, 
                                                   sw_status_update, op_, sw_s, 
                                                   op, sw >>

UpgraderAwaitSwDown1(self) == /\ pc[self] = "UpgraderAwaitSwDown1"
                              /\ SwStatusUpgrader[sw_[self]] = SW_DOWN
                              /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                              opRequest_, transaction_, 
                                              sw_status_, sw_, 
                                              sw_status_update_, opRequest, 
                                              transaction, sw_status, sw_e, 
                                              sw_status_update_e, 
                                              sw_status_update_N, 
                                              sw_status_update_NI, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_s, op, 
                                              sw >>

UpgraderAwaitSwDrained1(self) == /\ pc[self] = "UpgraderAwaitSwDrained1"
                                 /\ IF SwStatusUpgrader[sw_[self]] = SW_DOWN
                                       THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                                 RE2NIB, OFC2NIB, opRequest_, 
                                                 transaction_, sw_status_, sw_, 
                                                 sw_status_update_, opRequest, 
                                                 transaction, sw_status, sw_e, 
                                                 sw_status_update_e, 
                                                 sw_status_update_N, 
                                                 sw_status_update_NI, req_, 
                                                 sw_status_update_R, req, 
                                                 sw_status_update, op_, sw_s, 
                                                 op, sw >>

UpgraderAwaitSwDown2(self) == /\ pc[self] = "UpgraderAwaitSwDown2"
                              /\ SwStatusUpgrader[sw_[self]] = SW_DOWN
                              /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                              opRequest_, transaction_, 
                                              sw_status_, sw_, 
                                              sw_status_update_, opRequest, 
                                              transaction, sw_status, sw_e, 
                                              sw_status_update_e, 
                                              sw_status_update_N, 
                                              sw_status_update_NI, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_s, op, 
                                              sw >>

UpgraderAwaitSwDown3(self) == /\ pc[self] = "UpgraderAwaitSwDown3"
                              /\ SwStatusUpgrader[sw_[self]] = SW_DOWN
                              /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                              opRequest_, transaction_, 
                                              sw_status_, sw_, 
                                              sw_status_update_, opRequest, 
                                              transaction, sw_status, sw_e, 
                                              sw_status_update_e, 
                                              sw_status_update_N, 
                                              sw_status_update_NI, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_s, op, 
                                              sw >>

UpgraderWaitSWUndrained1(self) == /\ pc[self] = "UpgraderWaitSWUndrained1"
                                  /\ SwStatusUpgrader[sw_[self]] = SW_UNDRAINED
                                  /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                                  RE2NIB, OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_N, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
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
                                          SW2OFC, RE2NIB, OFC2NIB, opRequest_, 
                                          transaction_, sw_status_, sw_, 
                                          sw_status_update_, opRequest, 
                                          transaction, sw_status, sw_e, 
                                          sw_status_update_e, 
                                          sw_status_update_N, 
                                          sw_status_update_NI, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, op_, sw_s, op, sw >>

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
                                            SW2OFC, RE2NIB, OFC2NIB, 
                                            opRequest_, transaction_, 
                                            sw_status_, sw_, sw_status_update_, 
                                            opRequest, transaction, sw_status, 
                                            sw_e, sw_status_update_e, 
                                            sw_status_update_N, 
                                            sw_status_update_NI, req_, 
                                            sw_status_update_R, req, 
                                            sw_status_update, op_, sw_s, op, 
                                            sw >>

UpgraderWaitSWUndrained(self) == /\ pc[self] = "UpgraderWaitSWUndrained"
                                 /\ SwStatusUpgrader[sw_[self]] = SW_UNDRAINED
                                 /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                                 RE2NIB, OFC2NIB, opRequest_, 
                                                 transaction_, sw_status_, sw_, 
                                                 sw_status_update_, opRequest, 
                                                 transaction, sw_status, sw_e, 
                                                 sw_status_update_e, 
                                                 sw_status_update_N, 
                                                 sw_status_update_NI, req_, 
                                                 sw_status_update_R, req, 
                                                 sw_status_update, op_, sw_s, 
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
                                            SW2OFC, RE2NIB, OFC2NIB, 
                                            opRequest_, transaction_, 
                                            sw_status_, sw_, sw_status_update_, 
                                            opRequest, transaction, sw_status, 
                                            sw_e, sw_status_update_e, 
                                            sw_status_update_N, 
                                            sw_status_update_NI, req_, 
                                            sw_status_update_R, req, 
                                            sw_status_update, op_, sw_s, op, 
                                            sw >>

UpgraderWaitSWUndrained2(self) == /\ pc[self] = "UpgraderWaitSWUndrained2"
                                  /\ SwStatusUpgrader[sw_[self]] = SW_UNDRAINED
                                  /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                                  RE2NIB, OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_N, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
                                                  op, sw >>

UpgraderDrainSW2(self) == /\ pc[self] = "UpgraderDrainSW2"
                          /\ SwStatusUpgrader[sw_[self]] = SW_UP
                          /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                          sw |-> sw_[self],
                                                                          value |-> SW_DRAINED])
                          /\ pc' = [pc EXCEPT ![self] = "UpgraderWaitSWDrained3"]
                          /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                          SwStatusExpander, SwStatusRE, 
                                          SwStatusOFC, SwStatus, 
                                          UpgraderRequestQueue, 
                                          ExpanderRequestQueue, 
                                          SWManagementQueue, Upgrader2NIB, 
                                          NIB2Upgrader, Expander2NIB, 
                                          NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                          SW2OFC, RE2NIB, OFC2NIB, opRequest_, 
                                          transaction_, sw_status_, sw_, 
                                          sw_status_update_, opRequest, 
                                          transaction, sw_status, sw_e, 
                                          sw_status_update_e, 
                                          sw_status_update_N, 
                                          sw_status_update_NI, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, op_, sw_s, op, sw >>

UpgraderWaitSWDrained3(self) == /\ pc[self] = "UpgraderWaitSWDrained3"
                                /\ SwStatusUpgrader[sw_[self]] = SW_DRAINED
                                /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                                RE2NIB, OFC2NIB, opRequest_, 
                                                transaction_, sw_status_, sw_, 
                                                sw_status_update_, opRequest, 
                                                transaction, sw_status, sw_e, 
                                                sw_status_update_e, 
                                                sw_status_update_N, 
                                                sw_status_update_NI, req_, 
                                                sw_status_update_R, req, 
                                                sw_status_update, op_, sw_s, 
                                                op, sw >>

UpgraderWaitSWDrained4(self) == /\ pc[self] = "UpgraderWaitSWDrained4"
                                /\ SwStatusUpgrader[sw_[self]] = SW_DRAINED
                                /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest_"]
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
                                                RE2NIB, OFC2NIB, opRequest_, 
                                                transaction_, sw_status_, sw_, 
                                                sw_status_update_, opRequest, 
                                                transaction, sw_status, sw_e, 
                                                sw_status_update_e, 
                                                sw_status_update_N, 
                                                sw_status_update_NI, req_, 
                                                sw_status_update_R, req, 
                                                sw_status_update, op_, sw_s, 
                                                op, sw >>

upgraderWorkerProcess(self) == UpgraderThread(self)
                                  \/ DequeueManagementRequest_(self)
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
                                  \/ UpgraderWaitSWDrained3(self)
                                  \/ UpgraderWaitSWDrained4(self)

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
                                                     opRequest_, transaction_, 
                                                     sw_status_, sw_, 
                                                     opRequest, transaction, 
                                                     sw_status, sw_e, 
                                                     sw_status_update_e, 
                                                     sw_status_update_N, 
                                                     sw_status_update_NI, req_, 
                                                     sw_status_update_R, req, 
                                                     sw_status_update, op_, 
                                                     sw_s, op, sw >>

upgraderEventHandlerProcess(self) == UpgraderNIBEventHandlerProc(self)

ExpanderThread(self) == /\ pc[self] = "ExpanderThread"
                        /\ ExpanderRequestQueue # <<>>
                        /\ opRequest' = [opRequest EXCEPT ![self] = Head(ExpanderRequestQueue)]
                        /\ sw_e' = [sw_e EXCEPT ![self] = opRequest'[self].sw]
                        /\ Assert(opRequest'[self].type \in {DOWN_SW, UP_SW, DRAIN_SW, UNDRAIN_SW}, 
                                  "Failure of assertion at line 257, column 9.")
                        /\ IF opRequest'[self].type = DOWN_SW
                              THEN /\ sw_status' = [sw_status EXCEPT ![self] = SwStatusExpander[sw_e'[self]]]
                                   /\ IF sw_status'[self] = SW_DRAINED
                                         THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                                sw |-> sw_e'[self],
                                                                                                value |-> SW_DOWN])
                                              /\ pc' = [pc EXCEPT ![self] = "ExpanderAwaitSwDown1"]
                                              /\ UNCHANGED DrainRequestQueue
                                         ELSE /\ IF sw_status'[self] = SW_DOWN
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                         /\ UNCHANGED << SWManagementQueue, 
                                                                         DrainRequestQueue >>
                                                    ELSE /\ IF sw_status'[self] = SW_UNDRAINED
                                                               THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                       sw |-> sw_e'[self],
                                                                                                                       value |-> SW_DRAINED])
                                                                    /\ pc' = [pc EXCEPT ![self] = "ExpanderAwaitSwDrained1"]
                                                                    /\ UNCHANGED SWManagementQueue
                                                               ELSE /\ IF sw_status'[self] = SW_UP
                                                                          THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                                                                   sw |-> sw_e'[self],
                                                                                                                                   value |-> SW_DOWN])
                                                                               /\ pc' = [pc EXCEPT ![self] = "ExpanderAwaitSwDown3"]
                                                                          ELSE /\ Assert(FALSE, 
                                                                                         "Failure of assertion at line 301, column 17.")
                                                                               /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                               /\ UNCHANGED SWManagementQueue
                                                                    /\ UNCHANGED DrainRequestQueue
                              ELSE /\ IF opRequest'[self].type = UNDRAIN_SW
                                         THEN /\ sw_status' = [sw_status EXCEPT ![self] = SwStatusExpander[sw_e'[self]]]
                                              /\ IF sw_status'[self] = SW_DRAINED
                                                    THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> UNDRAIN_SW,
                                                                                                             sw |-> sw_e'[self],
                                                                                                             value |-> SW_UNDRAINED])
                                                         /\ pc' = [pc EXCEPT ![self] = "ExpanderWaitSWUndrained1"]
                                                         /\ UNCHANGED SWManagementQueue
                                                    ELSE /\ IF sw_status'[self] = SW_DOWN
                                                               THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> UP_SW,
                                                                                                                        sw |-> sw_e'[self],
                                                                                                                        value |-> SW_UP])
                                                                    /\ pc' = [pc EXCEPT ![self] = "ExpanderDrainSW1"]
                                                                    /\ UNCHANGED DrainRequestQueue
                                                               ELSE /\ IF sw_status'[self] = SW_UP
                                                                          THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                                   sw |-> sw_e'[self],
                                                                                                                                   value |-> SW_DRAINED])
                                                                               /\ pc' = [pc EXCEPT ![self] = "ExpanderUndrainSW2"]
                                                                          ELSE /\ IF sw_status'[self] = SW_UNDRAINED
                                                                                     THEN /\ TRUE
                                                                                     ELSE /\ Assert(FALSE, 
                                                                                                    "Failure of assertion at line 352, column 17.")
                                                                               /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                               /\ UNCHANGED DrainRequestQueue
                                                                    /\ UNCHANGED SWManagementQueue
                                         ELSE /\ IF opRequest'[self].type = DRAIN_SW
                                                    THEN /\ sw_status' = [sw_status EXCEPT ![self] = SwStatusExpander[sw_e'[self]]]
                                                         /\ IF sw_status'[self] = SW_DRAINED
                                                               THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                    /\ UNCHANGED << SWManagementQueue, 
                                                                                    DrainRequestQueue >>
                                                               ELSE /\ IF sw_status'[self] = SW_DOWN
                                                                          THEN /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> UP_SW,
                                                                                                                                   sw |-> sw_e'[self],
                                                                                                                                   value |-> SW_UP])
                                                                               /\ pc' = [pc EXCEPT ![self] = "ExpanderDrainSW2"]
                                                                               /\ UNCHANGED DrainRequestQueue
                                                                          ELSE /\ IF sw_status'[self] \in {SW_UNDRAINED, SW_UP}
                                                                                     THEN /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                                                                                              sw |-> sw_e'[self],
                                                                                                                                              value |-> SW_DRAINED])
                                                                                          /\ pc' = [pc EXCEPT ![self] = "ExpanderWaitSWUndrained4"]
                                                                                     ELSE /\ Assert(FALSE, 
                                                                                                    "Failure of assertion at line 378, column 17.")
                                                                                          /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                                                                          /\ UNCHANGED DrainRequestQueue
                                                                               /\ UNCHANGED SWManagementQueue
                                                    ELSE /\ Assert(FALSE, 
                                                                   "Failure of assertion at line 381, column 13.")
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
                                        SW2OFC, RE2NIB, OFC2NIB, opRequest_, 
                                        transaction_, sw_status_, sw_, 
                                        sw_status_update_, transaction, 
                                        sw_status_update_e, sw_status_update_N, 
                                        sw_status_update_NI, req_, 
                                        sw_status_update_R, req, 
                                        sw_status_update, op_, sw_s, op, sw >>

DequeueManagementRequest(self) == /\ pc[self] = "DequeueManagementRequest"
                                  /\ ExpanderRequestQueue' = Tail(ExpanderRequestQueue)
                                  /\ pc' = [pc EXCEPT ![self] = "ExpanderThread"]
                                  /\ UNCHANGED << SwStatusNIB, 
                                                  SwStatusUpgrader, 
                                                  SwStatusExpander, SwStatusRE, 
                                                  SwStatusOFC, SwStatus, 
                                                  UpgraderRequestQueue, 
                                                  SWManagementQueue, 
                                                  DrainRequestQueue, 
                                                  Upgrader2NIB, NIB2Upgrader, 
                                                  Expander2NIB, NIB2Expander, 
                                                  RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                  RE2NIB, OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_N, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
                                                  op, sw >>

ExpanderAwaitSwDown1(self) == /\ pc[self] = "ExpanderAwaitSwDown1"
                              /\ SwStatusExpander[sw_e[self]] = SW_DOWN
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
                                              opRequest_, transaction_, 
                                              sw_status_, sw_, 
                                              sw_status_update_, opRequest, 
                                              transaction, sw_status, sw_e, 
                                              sw_status_update_e, 
                                              sw_status_update_N, 
                                              sw_status_update_NI, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_s, op, 
                                              sw >>

ExpanderAwaitSwDrained1(self) == /\ pc[self] = "ExpanderAwaitSwDrained1"
                                 /\ IF SwStatusExpander[sw_e[self]] = SW_DOWN
                                       THEN /\ pc' = [pc EXCEPT ![self] = "DequeueManagementRequest"]
                                            /\ UNCHANGED SWManagementQueue
                                       ELSE /\ SwStatusExpander[sw_e[self]] = SW_DRAINED
                                            /\ SWManagementQueue' = Append(SWManagementQueue, [type |-> DOWN_SW,
                                                                                        sw |-> sw_e[self],
                                                                                        value |-> SW_DOWN])
                                            /\ pc' = [pc EXCEPT ![self] = "ExpanderAwaitSwDown2"]
                                 /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                                 SwStatusExpander, SwStatusRE, 
                                                 SwStatusOFC, SwStatus, 
                                                 UpgraderRequestQueue, 
                                                 ExpanderRequestQueue, 
                                                 DrainRequestQueue, 
                                                 Upgrader2NIB, NIB2Upgrader, 
                                                 Expander2NIB, NIB2Expander, 
                                                 RE2SW, SW2RE, OFC2SW, SW2OFC, 
                                                 RE2NIB, OFC2NIB, opRequest_, 
                                                 transaction_, sw_status_, sw_, 
                                                 sw_status_update_, opRequest, 
                                                 transaction, sw_status, sw_e, 
                                                 sw_status_update_e, 
                                                 sw_status_update_N, 
                                                 sw_status_update_NI, req_, 
                                                 sw_status_update_R, req, 
                                                 sw_status_update, op_, sw_s, 
                                                 op, sw >>

ExpanderAwaitSwDown2(self) == /\ pc[self] = "ExpanderAwaitSwDown2"
                              /\ SwStatusExpander[sw_e[self]] = SW_DOWN
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
                                              opRequest_, transaction_, 
                                              sw_status_, sw_, 
                                              sw_status_update_, opRequest, 
                                              transaction, sw_status, sw_e, 
                                              sw_status_update_e, 
                                              sw_status_update_N, 
                                              sw_status_update_NI, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_s, op, 
                                              sw >>

ExpanderAwaitSwDown3(self) == /\ pc[self] = "ExpanderAwaitSwDown3"
                              /\ SwStatusExpander[sw_e[self]] = SW_DOWN
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
                                              opRequest_, transaction_, 
                                              sw_status_, sw_, 
                                              sw_status_update_, opRequest, 
                                              transaction, sw_status, sw_e, 
                                              sw_status_update_e, 
                                              sw_status_update_N, 
                                              sw_status_update_NI, req_, 
                                              sw_status_update_R, req, 
                                              sw_status_update, op_, sw_s, op, 
                                              sw >>

ExpanderWaitSWUndrained1(self) == /\ pc[self] = "ExpanderWaitSWUndrained1"
                                  /\ SwStatusExpander[sw_e[self]] = SW_UNDRAINED
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
                                                  RE2NIB, OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_N, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
                                                  op, sw >>

ExpanderDrainSW1(self) == /\ pc[self] = "ExpanderDrainSW1"
                          /\ SwStatusExpander[sw_e[self]] = SW_UP
                          /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                          sw |-> sw_e[self],
                                                                          value |-> SW_DRAINED])
                          /\ pc' = [pc EXCEPT ![self] = "ExpanderUndrainSW1"]
                          /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                          SwStatusExpander, SwStatusRE, 
                                          SwStatusOFC, SwStatus, 
                                          UpgraderRequestQueue, 
                                          ExpanderRequestQueue, 
                                          SWManagementQueue, Upgrader2NIB, 
                                          NIB2Upgrader, Expander2NIB, 
                                          NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                          SW2OFC, RE2NIB, OFC2NIB, opRequest_, 
                                          transaction_, sw_status_, sw_, 
                                          sw_status_update_, opRequest, 
                                          transaction, sw_status, sw_e, 
                                          sw_status_update_e, 
                                          sw_status_update_N, 
                                          sw_status_update_NI, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, op_, sw_s, op, sw >>

ExpanderUndrainSW1(self) == /\ pc[self] = "ExpanderUndrainSW1"
                            /\ SwStatusExpander[sw_e[self]] = SW_DRAINED
                            /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> UNDRAIN_SW,
                                                                            sw |-> sw_e[self],
                                                                            value |-> SW_UNDRAINED])
                            /\ pc' = [pc EXCEPT ![self] = "ExpanderWaitSWUndrained"]
                            /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                            SwStatusExpander, SwStatusRE, 
                                            SwStatusOFC, SwStatus, 
                                            UpgraderRequestQueue, 
                                            ExpanderRequestQueue, 
                                            SWManagementQueue, Upgrader2NIB, 
                                            NIB2Upgrader, Expander2NIB, 
                                            NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                            SW2OFC, RE2NIB, OFC2NIB, 
                                            opRequest_, transaction_, 
                                            sw_status_, sw_, sw_status_update_, 
                                            opRequest, transaction, sw_status, 
                                            sw_e, sw_status_update_e, 
                                            sw_status_update_N, 
                                            sw_status_update_NI, req_, 
                                            sw_status_update_R, req, 
                                            sw_status_update, op_, sw_s, op, 
                                            sw >>

ExpanderWaitSWUndrained(self) == /\ pc[self] = "ExpanderWaitSWUndrained"
                                 /\ SwStatusExpander[sw_e[self]] = SW_UNDRAINED
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
                                                 RE2NIB, OFC2NIB, opRequest_, 
                                                 transaction_, sw_status_, sw_, 
                                                 sw_status_update_, opRequest, 
                                                 transaction, sw_status, sw_e, 
                                                 sw_status_update_e, 
                                                 sw_status_update_N, 
                                                 sw_status_update_NI, req_, 
                                                 sw_status_update_R, req, 
                                                 sw_status_update, op_, sw_s, 
                                                 op, sw >>

ExpanderUndrainSW2(self) == /\ pc[self] = "ExpanderUndrainSW2"
                            /\ SwStatusExpander[sw_e[self]] = SW_DRAINED
                            /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> UNDRAIN_SW,
                                                                            sw |-> sw_e[self],
                                                                            value |-> SW_UNDRAINED])
                            /\ pc' = [pc EXCEPT ![self] = "ExpanderWaitSWUndrained2"]
                            /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                            SwStatusExpander, SwStatusRE, 
                                            SwStatusOFC, SwStatus, 
                                            UpgraderRequestQueue, 
                                            ExpanderRequestQueue, 
                                            SWManagementQueue, Upgrader2NIB, 
                                            NIB2Upgrader, Expander2NIB, 
                                            NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                            SW2OFC, RE2NIB, OFC2NIB, 
                                            opRequest_, transaction_, 
                                            sw_status_, sw_, sw_status_update_, 
                                            opRequest, transaction, sw_status, 
                                            sw_e, sw_status_update_e, 
                                            sw_status_update_N, 
                                            sw_status_update_NI, req_, 
                                            sw_status_update_R, req, 
                                            sw_status_update, op_, sw_s, op, 
                                            sw >>

ExpanderWaitSWUndrained2(self) == /\ pc[self] = "ExpanderWaitSWUndrained2"
                                  /\ SwStatusExpander[sw_e[self]] = SW_UNDRAINED
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
                                                  RE2NIB, OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_N, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
                                                  op, sw >>

ExpanderDrainSW2(self) == /\ pc[self] = "ExpanderDrainSW2"
                          /\ SwStatusExpander[sw_e[self]] = SW_UP
                          /\ DrainRequestQueue' = Append(DrainRequestQueue, [type |-> DRAIN_SW,
                                                                          sw |-> sw_e[self],
                                                                          value |-> SW_DRAINED])
                          /\ pc' = [pc EXCEPT ![self] = "ExpanderWaitSWUndrained3"]
                          /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                          SwStatusExpander, SwStatusRE, 
                                          SwStatusOFC, SwStatus, 
                                          UpgraderRequestQueue, 
                                          ExpanderRequestQueue, 
                                          SWManagementQueue, Upgrader2NIB, 
                                          NIB2Upgrader, Expander2NIB, 
                                          NIB2Expander, RE2SW, SW2RE, OFC2SW, 
                                          SW2OFC, RE2NIB, OFC2NIB, opRequest_, 
                                          transaction_, sw_status_, sw_, 
                                          sw_status_update_, opRequest, 
                                          transaction, sw_status, sw_e, 
                                          sw_status_update_e, 
                                          sw_status_update_N, 
                                          sw_status_update_NI, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, op_, sw_s, op, sw >>

ExpanderWaitSWUndrained3(self) == /\ pc[self] = "ExpanderWaitSWUndrained3"
                                  /\ SwStatusExpander[sw_e[self]] = SW_DRAINED
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
                                                  RE2NIB, OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_N, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
                                                  op, sw >>

ExpanderWaitSWUndrained4(self) == /\ pc[self] = "ExpanderWaitSWUndrained4"
                                  /\ SwStatusExpander[sw_e[self]] = SW_DRAINED
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
                                                  RE2NIB, OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_N, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
                                                  op, sw >>

expanderWorkerProcess(self) == ExpanderThread(self)
                                  \/ DequeueManagementRequest(self)
                                  \/ ExpanderAwaitSwDown1(self)
                                  \/ ExpanderAwaitSwDrained1(self)
                                  \/ ExpanderAwaitSwDown2(self)
                                  \/ ExpanderAwaitSwDown3(self)
                                  \/ ExpanderWaitSWUndrained1(self)
                                  \/ ExpanderDrainSW1(self)
                                  \/ ExpanderUndrainSW1(self)
                                  \/ ExpanderWaitSWUndrained(self)
                                  \/ ExpanderUndrainSW2(self)
                                  \/ ExpanderWaitSWUndrained2(self)
                                  \/ ExpanderDrainSW2(self)
                                  \/ ExpanderWaitSWUndrained3(self)
                                  \/ ExpanderWaitSWUndrained4(self)

ExpanderNIBEventHandlerProc(self) == /\ pc[self] = "ExpanderNIBEventHandlerProc"
                                     /\ NIB2Expander # <<>>
                                     /\ sw_status_update_e' = [sw_status_update_e EXCEPT ![self] = Head(NIB2Expander)]
                                     /\ NIB2Expander' = Tail(NIB2Expander)
                                     /\ SwStatusExpander' = [SwStatusExpander EXCEPT ![sw_status_update_e'[self].sw] = sw_status_update_e'[self].value]
                                     /\ pc' = [pc EXCEPT ![self] = "ExpanderNIBEventHandlerProc"]
                                     /\ UNCHANGED << SwStatusNIB, 
                                                     SwStatusUpgrader, 
                                                     SwStatusRE, SwStatusOFC, 
                                                     SwStatus, 
                                                     UpgraderRequestQueue, 
                                                     ExpanderRequestQueue, 
                                                     SWManagementQueue, 
                                                     DrainRequestQueue, 
                                                     Upgrader2NIB, 
                                                     NIB2Upgrader, 
                                                     Expander2NIB, RE2SW, 
                                                     SW2RE, OFC2SW, SW2OFC, 
                                                     RE2NIB, OFC2NIB, 
                                                     opRequest_, transaction_, 
                                                     sw_status_, sw_, 
                                                     sw_status_update_, 
                                                     opRequest, transaction, 
                                                     sw_status, sw_e, 
                                                     sw_status_update_N, 
                                                     sw_status_update_NI, req_, 
                                                     sw_status_update_R, req, 
                                                     sw_status_update, op_, 
                                                     sw_s, op, sw >>

expanderEventHandlerProcess(self) == ExpanderNIBEventHandlerProc(self)

NIBEventHandlerForREProc(self) == /\ pc[self] = "NIBEventHandlerForREProc"
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
                                                  OFC2NIB, opRequest_, 
                                                  transaction_, sw_status_, 
                                                  sw_, sw_status_update_, 
                                                  opRequest, transaction, 
                                                  sw_status, sw_e, 
                                                  sw_status_update_e, 
                                                  sw_status_update_NI, req_, 
                                                  sw_status_update_R, req, 
                                                  sw_status_update, op_, sw_s, 
                                                  op, sw >>

NIBEventHandlerForRE(self) == NIBEventHandlerForREProc(self)

NIBEventHandlerForOFCProc(self) == /\ pc[self] = "NIBEventHandlerForOFCProc"
                                   /\ OFC2NIB # <<>>
                                   /\ sw_status_update_NI' = [sw_status_update_NI EXCEPT ![self] = Head(OFC2NIB)]
                                   /\ OFC2NIB' = Tail(OFC2NIB)
                                   /\ SwStatusNIB' = [SwStatusNIB EXCEPT ![sw_status_update_NI'[self].sw] = sw_status_update_NI'[self].value]
                                   /\ NIB2Upgrader' =      Append(NIB2Upgrader, [type |-> MSG_SW_STATUS_CHANGE,
                                                      sw |-> sw_status_update_NI'[self].sw,
                                                      value|-> sw_status_update_NI'[self].value
                                                      ])
                                   /\ NIB2Expander' =      Append(NIB2Expander, [type |-> MSG_SW_STATUS_CHANGE,
                                                      sw |-> sw_status_update_NI'[self].sw,
                                                      value|-> sw_status_update_NI'[self].value
                                                      ])
                                   /\ pc' = [pc EXCEPT ![self] = "NIBEventHandlerForOFCProc"]
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
                                                   SW2OFC, RE2NIB, opRequest_, 
                                                   transaction_, sw_status_, 
                                                   sw_, sw_status_update_, 
                                                   opRequest, transaction, 
                                                   sw_status, sw_e, 
                                                   sw_status_update_e, 
                                                   sw_status_update_N, req_, 
                                                   sw_status_update_R, req, 
                                                   sw_status_update, op_, sw_s, 
                                                   op, sw >>

NIBEventHandlerForOFC(self) == NIBEventHandlerForOFCProc(self)

REWorkerProc(self) == /\ pc[self] = "REWorkerProc"
                      /\ DrainRequestQueue # <<>>
                      /\ req_' = [req_ EXCEPT ![self] = Head(DrainRequestQueue)]
                      /\ Assert(req_'[self].type \in {DRAIN_SW, UNDRAIN_SW}, 
                                "Failure of assertion at line 537, column 13.")
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
                                      RE2NIB, OFC2NIB, opRequest_, 
                                      transaction_, sw_status_, sw_, 
                                      sw_status_update_, opRequest, 
                                      transaction, sw_status, sw_e, 
                                      sw_status_update_e, sw_status_update_N, 
                                      sw_status_update_NI, sw_status_update_R, 
                                      req, sw_status_update, op_, sw_s, op, sw >>

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
                                              SW2OFC, OFC2NIB, opRequest_, 
                                              transaction_, sw_status_, sw_, 
                                              sw_status_update_, opRequest, 
                                              transaction, sw_status, sw_e, 
                                              sw_status_update_e, 
                                              sw_status_update_N, 
                                              sw_status_update_NI, req_, req, 
                                              sw_status_update, op_, sw_s, op, 
                                              sw >>

RESWEventHandlerProcess(self) == RESWEventHandlerProc(self)

OFCProc(self) == /\ pc[self] = "OFCProc"
                 /\ SWManagementQueue # <<>>
                 /\ req' = [req EXCEPT ![self] = Head(SWManagementQueue)]
                 /\ SWManagementQueue' = Tail(SWManagementQueue)
                 /\ OFC2SW' = [OFC2SW EXCEPT ![req'[self].sw] = Append(OFC2SW[req'[self].sw], req'[self])]
                 /\ pc' = [pc EXCEPT ![self] = "OFCProc"]
                 /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                 SwStatusExpander, SwStatusRE, SwStatusOFC, 
                                 SwStatus, UpgraderRequestQueue, 
                                 ExpanderRequestQueue, DrainRequestQueue, 
                                 Upgrader2NIB, NIB2Upgrader, Expander2NIB, 
                                 NIB2Expander, RE2SW, SW2RE, SW2OFC, RE2NIB, 
                                 OFC2NIB, opRequest_, transaction_, sw_status_, 
                                 sw_, sw_status_update_, opRequest, 
                                 transaction, sw_status, sw_e, 
                                 sw_status_update_e, sw_status_update_N, 
                                 sw_status_update_NI, req_, sw_status_update_R, 
                                 sw_status_update, op_, sw_s, op, sw >>

OFCSwitchManagementProcess(self) == OFCProc(self)

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
                                                opRequest_, transaction_, 
                                                sw_status_, sw_, 
                                                sw_status_update_, opRequest, 
                                                transaction, sw_status, sw_e, 
                                                sw_status_update_e, 
                                                sw_status_update_N, 
                                                sw_status_update_NI, req_, 
                                                sw_status_update_R, req, op_, 
                                                sw_s, op, sw >>

OFCSWEventHandlerProcess(self) == OFCSWEventHandlingProc(self)

SWManagementProc(self) == /\ pc[self] = "SWManagementProc"
                          /\ OFC2SW[sw_s[self]] # <<>>
                          /\ op_' = [op_ EXCEPT ![self] = Head(OFC2SW[sw_s[self]])]
                          /\ Assert(op_'[self].type \in {UP_SW, DOWN_SW}, 
                                    "Failure of assertion at line 615, column 13.")
                          /\ OFC2SW' = [OFC2SW EXCEPT ![sw_s[self]] = Tail(OFC2SW[sw_s[self]])]
                          /\ IF op_'[self].value = SW_DRAINED
                                THEN /\ SwStatus' = [SwStatus EXCEPT ![sw_s[self]] = SW_DRAINED]
                                ELSE /\ IF op_'[self].value = SW_DOWN
                                           THEN /\ Assert(SwStatus[sw_s[self]] # SW_UNDRAINED, 
                                                          "Failure of assertion at line 620, column 17.")
                                                /\ SwStatus' = [SwStatus EXCEPT ![sw_s[self]] = SW_DOWN]
                                           ELSE /\ IF op_'[self].value = SW_UP
                                                      THEN /\ SwStatus' = [SwStatus EXCEPT ![sw_s[self]] = SW_UP]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED SwStatus
                          /\ SW2OFC' = Append(SW2OFC, [type |-> MSG_SW_STATUS_CHANGE,
                                        sw |-> sw_s[self],
                                        value|-> SwStatus'[sw_s[self]]
                                        ])
                          /\ SW2RE' = Append(SW2RE, [type |-> MSG_SW_STATUS_CHANGE,
                                        sw |-> sw_s[self],
                                        value|-> SwStatus'[sw_s[self]]
                                        ])
                          /\ pc' = [pc EXCEPT ![self] = "SWManagementProc"]
                          /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                          SwStatusExpander, SwStatusRE, 
                                          SwStatusOFC, UpgraderRequestQueue, 
                                          ExpanderRequestQueue, 
                                          SWManagementQueue, DrainRequestQueue, 
                                          Upgrader2NIB, NIB2Upgrader, 
                                          Expander2NIB, NIB2Expander, RE2SW, 
                                          RE2NIB, OFC2NIB, opRequest_, 
                                          transaction_, sw_status_, sw_, 
                                          sw_status_update_, opRequest, 
                                          transaction, sw_status, sw_e, 
                                          sw_status_update_e, 
                                          sw_status_update_N, 
                                          sw_status_update_NI, req_, 
                                          sw_status_update_R, req, 
                                          sw_status_update, sw_s, op, sw >>

swManagementProcess(self) == SWManagementProc(self)

SWIRProc(self) == /\ pc[self] = "SWIRProc"
                  /\ RE2SW[sw[self]] # <<>>
                  /\ op' = [op EXCEPT ![self] = Head(RE2SW[sw[self]])]
                  /\ Assert(op'[self].sw = sw[self], 
                            "Failure of assertion at line 647, column 13.")
                  /\ Assert(op'[self].type \in {DRAIN_SW, UNDRAIN_SW}, 
                            "Failure of assertion at line 648, column 13.")
                  /\ RE2SW' = [RE2SW EXCEPT ![sw[self]] = Tail(RE2SW[sw[self]])]
                  /\ IF op'[self].value = SW_DRAINED
                        THEN /\ SwStatus' = [SwStatus EXCEPT ![sw[self]] = SW_DRAINED]
                        ELSE /\ IF op'[self].value = SW_UNDRAINED
                                   THEN /\ SwStatus' = [SwStatus EXCEPT ![sw[self]] = SW_UNDRAINED]
                                   ELSE /\ Assert(FALSE, 
                                                  "Failure of assertion at line 655, column 17.")
                                        /\ UNCHANGED SwStatus
                  /\ SW2RE' = Append(SW2RE, [type |-> MSG_SW_STATUS_CHANGE,
                                sw |-> sw[self],
                                value|-> SwStatus'[sw[self]]
                                ])
                  /\ SW2OFC' = Append(SW2OFC, [type |-> MSG_SW_STATUS_CHANGE,
                                sw |-> sw[self],
                                value|-> SwStatus'[sw[self]]
                                ])
                  /\ pc' = [pc EXCEPT ![self] = "SWIRProc"]
                  /\ UNCHANGED << SwStatusNIB, SwStatusUpgrader, 
                                  SwStatusExpander, SwStatusRE, SwStatusOFC, 
                                  UpgraderRequestQueue, ExpanderRequestQueue, 
                                  SWManagementQueue, DrainRequestQueue, 
                                  Upgrader2NIB, NIB2Upgrader, Expander2NIB, 
                                  NIB2Expander, OFC2SW, RE2NIB, OFC2NIB, 
                                  opRequest_, transaction_, sw_status_, sw_, 
                                  sw_status_update_, opRequest, transaction, 
                                  sw_status, sw_e, sw_status_update_e, 
                                  sw_status_update_N, sw_status_update_NI, 
                                  req_, sw_status_update_R, req, 
                                  sw_status_update, op_, sw_s, sw >>

swIRProcess(self) == SWIRProc(self)

Next == (\E self \in ({UPGRADER} \X {CONT_WORKER}): upgraderWorkerProcess(self))
           \/ (\E self \in ({UPGRADER} \X {CONT_EVENT_HANDLER}): upgraderEventHandlerProcess(self))
           \/ (\E self \in ({EXPANDER} \X {CONT_WORKER}): expanderWorkerProcess(self))
           \/ (\E self \in ({EXPANDER} \X {CONT_EVENT_HANDLER}): expanderEventHandlerProcess(self))
           \/ (\E self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_RE}): NIBEventHandlerForRE(self))
           \/ (\E self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_OFC}): NIBEventHandlerForOFC(self))
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
        /\ \A self \in ({EXPANDER} \X {CONT_WORKER}) : WF_vars(expanderWorkerProcess(self))
        /\ \A self \in ({EXPANDER} \X {CONT_EVENT_HANDLER}) : WF_vars(expanderEventHandlerProcess(self))
        /\ \A self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_RE}) : WF_vars(NIBEventHandlerForRE(self))
        /\ \A self \in ({NIB} \X {CONT_EVENT_HANDLER_NIB_FOR_OFC}) : WF_vars(NIBEventHandlerForOFC(self))
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
    

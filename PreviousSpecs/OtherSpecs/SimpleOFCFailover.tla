-------------------------- MODULE StateConsistency --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS SW, c0, c1, Updated, NotUpdated, batchSize

(*--algorithm stateConsistency
    variables controllerState = [c0 |-> "primary", c1 |-> "backup"],
              switchState = [x \in SW |-> NotUpdated],
              canUpdate = [x \in SW |-> 0],
              latestUpdateRcv = 0,
              latestUpdateSnt = 0,
              latestSWConsidered = 0,
              failedTimes = [x \in SW |-> 0];
    define
        SendInstruction(swID) == canUpdate[swID] = 1
        max(set) == CHOOSE x \in set: \A y \in set: x \geq y
        min(set) == CHOOSE x \in set: \A y \in set: x \leq y
        RECURSIVE GetFirstNofSet(_, _)
        GetFirstNofSet(set, N) == IF Cardinality(set) <= N 
                                    THEN set
                                    ELSE IF N = 1 THEN {min(set)}
                                    ELSE {min(set)} \union GetFirstNofSet(set \ {min(set)}, N-1) 
                                    
        CheckSetSWUpdated(set) == \A x \in set: switchState[x] = Updated
        maxUpdateRcv == CHOOSE x \in SW: /\ switchState[x] = Updated
                                         /\ (\A y \in 1..x: switchState[y] = Updated)
        controllerIsMaster(self) == IF self=c0 THEN controllerState.c0 = "primary"
                                               ELSE controllerState.c1 = "primary"
        getFailed(set) == {x \in set: canUpdate[x] = 0}
        NoMorePossibleUpdates(set) == Cardinality({x \in set: /\ canUpdate[x] # 0
                                                              /\ switchState[x] = NotUpdated}) = 0
    end define  
    
    macro failover()
    begin
        if (self = c0 /\ controllerState.c0 = "primary")
        then
            either
                controllerState.c0 := "failed" || controllerState.c1 := "primary";
                goto EndCont;
            or
                skip;
            end either;
        end if; 
    end macro; 
    
    fair process swProc \in SW
    begin
    Switch:
    while TRUE do 
        await canUpdate[self] # 0;
        if failedTimes[self] = 2 then goto Update; end if;
        UpOrFail:
        either 
            Update:
                switchState[self] := Updated;
                goto EndSW;
        or
            Failure:
                switchState[self] := NotUpdated || canUpdate[self] := 0;
                failedTimes[self] := failedTimes[self] + 1;
                goto Switch;
        end either;
    end while;
    EndSW: skip;
    end process
    
    fair process c \in {c0, c1}
    variables setSwitches = {}, copySet={}, s = 0, considered={}, updated={}, numBatch=0;
    begin
    Controller: skip;
    await controllerIsMaster(self);
    if self = c1 then 
            await NoMorePossibleUpdates(setSwitches);
    end if;
    ControllerObj:
    while TRUE do
        \*setSwitches := GetFirstNofSet(SW\1..latestSWConsidered, batchSize);
        setSwitches := GetFirstNofSet(SW\1..latestUpdateRcv, batchSize);
        copySet := setSwitches;
        if Cardinality(setSwitches) = 0 then goto EndCont; end if;
        check1stbatchForC1:
        if (self = c1 /\ numBatch = 0) then
            await NoMorePossibleUpdates(setSwitches);
        end if;
        Rest:
        latestSWConsidered := max(setSwitches); 
        considered := {};
        SendAllUpdates:
          while TRUE do
             CheckIfFinished:
             if (Cardinality(setSwitches) - Cardinality(considered) = 0) then
                 goto check;
             end if;
             f1: failover();
             sendUpdate: 
                s := min(setSwitches\(considered));
                considered := considered \union {s};
                if numBatch = 0 then
                    if switchState[s] = Updated then
                        goto SendAllUpdates;
                    end if;
                end if;
                sendIRs:
                canUpdate[s] := canUpdate[s] + 1;
          end while;
        check:
            failover();
            nofail: 
            await NoMorePossibleUpdates(setSwitches);
            setSwitches := getFailed(copySet);
            if Cardinality(setSwitches) = 0 then
                latestUpdateRcv := max(copySet);
                numBatch := numBatch + 1;
                goto ControllerObj   
            else
                resendUpdates: considered := {};
                               goto SendAllUpdates;
            end if;                
    end while;       
    EndCont:
        skip;
    end process
    
    end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4084f2ec9f8268e5472ceed0715374f3
VARIABLES controllerState, switchState, canUpdate, latestUpdateRcv, 
          latestUpdateSnt, latestSWConsidered, failedTimes, pc

(* define statement *)
SendInstruction(swID) == canUpdate[swID] = 1
max(set) == CHOOSE x \in set: \A y \in set: x \geq y
min(set) == CHOOSE x \in set: \A y \in set: x \leq y
RECURSIVE GetFirstNofSet(_, _)
GetFirstNofSet(set, N) == IF Cardinality(set) <= N
                            THEN set
                            ELSE IF N = 1 THEN {min(set)}
                            ELSE {min(set)} \union GetFirstNofSet(set \ {min(set)}, N-1)

CheckSetSWUpdated(set) == \A x \in set: switchState[x] = Updated
maxUpdateRcv == CHOOSE x \in SW: /\ switchState[x] = Updated
                                 /\ (\A y \in 1..x: switchState[y] = Updated)
controllerIsMaster(self) == IF self=c0 THEN controllerState.c0 = "primary"
                                       ELSE controllerState.c1 = "primary"
getFailed(set) == {x \in set: canUpdate[x] = 0}
NoMorePossibleUpdates(set) == Cardinality({x \in set: /\ canUpdate[x] # 0
                                                      /\ switchState[x] = NotUpdated}) = 0

VARIABLES setSwitches, copySet, s, considered, updated, numBatch

vars == << controllerState, switchState, canUpdate, latestUpdateRcv, 
           latestUpdateSnt, latestSWConsidered, failedTimes, pc, setSwitches, 
           copySet, s, considered, updated, numBatch >>

ProcSet == (SW) \cup ({c0, c1})

Init == (* Global variables *)
        /\ controllerState = [c0 |-> "primary", c1 |-> "backup"]
        /\ switchState = [x \in SW |-> NotUpdated]
        /\ canUpdate = [x \in SW |-> 0]
        /\ latestUpdateRcv = 0
        /\ latestUpdateSnt = 0
        /\ latestSWConsidered = 0
        /\ failedTimes = [x \in SW |-> 0]
        (* Process c *)
        /\ setSwitches = [self \in {c0, c1} |-> {}]
        /\ copySet = [self \in {c0, c1} |-> {}]
        /\ s = [self \in {c0, c1} |-> 0]
        /\ considered = [self \in {c0, c1} |-> {}]
        /\ updated = [self \in {c0, c1} |-> {}]
        /\ numBatch = [self \in {c0, c1} |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in SW -> "Switch"
                                        [] self \in {c0, c1} -> "Controller"]

Switch(self) == /\ pc[self] = "Switch"
                /\ canUpdate[self] # 0
                /\ IF failedTimes[self] = 2
                      THEN /\ pc' = [pc EXCEPT ![self] = "Update"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "UpOrFail"]
                /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                latestUpdateRcv, latestUpdateSnt, 
                                latestSWConsidered, failedTimes, setSwitches, 
                                copySet, s, considered, updated, numBatch >>

UpOrFail(self) == /\ pc[self] = "UpOrFail"
                  /\ \/ /\ pc' = [pc EXCEPT ![self] = "Update"]
                     \/ /\ pc' = [pc EXCEPT ![self] = "Failure"]
                  /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                  latestUpdateRcv, latestUpdateSnt, 
                                  latestSWConsidered, failedTimes, setSwitches, 
                                  copySet, s, considered, updated, numBatch >>

Update(self) == /\ pc[self] = "Update"
                /\ switchState' = [switchState EXCEPT ![self] = Updated]
                /\ pc' = [pc EXCEPT ![self] = "EndSW"]
                /\ UNCHANGED << controllerState, canUpdate, latestUpdateRcv, 
                                latestUpdateSnt, latestSWConsidered, 
                                failedTimes, setSwitches, copySet, s, 
                                considered, updated, numBatch >>

Failure(self) == /\ pc[self] = "Failure"
                 /\ /\ canUpdate' = [canUpdate EXCEPT ![self] = 0]
                    /\ switchState' = [switchState EXCEPT ![self] = NotUpdated]
                 /\ failedTimes' = [failedTimes EXCEPT ![self] = failedTimes[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "Switch"]
                 /\ UNCHANGED << controllerState, latestUpdateRcv, 
                                 latestUpdateSnt, latestSWConsidered, 
                                 setSwitches, copySet, s, considered, updated, 
                                 numBatch >>

EndSW(self) == /\ pc[self] = "EndSW"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << controllerState, switchState, canUpdate, 
                               latestUpdateRcv, latestUpdateSnt, 
                               latestSWConsidered, failedTimes, setSwitches, 
                               copySet, s, considered, updated, numBatch >>

swProc(self) == Switch(self) \/ UpOrFail(self) \/ Update(self)
                   \/ Failure(self) \/ EndSW(self)

Controller(self) == /\ pc[self] = "Controller"
                    /\ TRUE
                    /\ controllerIsMaster(self)
                    /\ IF self = c1
                          THEN /\ NoMorePossibleUpdates(setSwitches[self])
                          ELSE /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "ControllerObj"]
                    /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                    latestUpdateRcv, latestUpdateSnt, 
                                    latestSWConsidered, failedTimes, 
                                    setSwitches, copySet, s, considered, 
                                    updated, numBatch >>

ControllerObj(self) == /\ pc[self] = "ControllerObj"
                       /\ setSwitches' = [setSwitches EXCEPT ![self] = GetFirstNofSet(SW\1..latestUpdateRcv, batchSize)]
                       /\ copySet' = [copySet EXCEPT ![self] = setSwitches'[self]]
                       /\ IF Cardinality(setSwitches'[self]) = 0
                             THEN /\ pc' = [pc EXCEPT ![self] = "EndCont"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "check1stbatchForC1"]
                       /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                       latestUpdateRcv, latestUpdateSnt, 
                                       latestSWConsidered, failedTimes, s, 
                                       considered, updated, numBatch >>

check1stbatchForC1(self) == /\ pc[self] = "check1stbatchForC1"
                            /\ IF (self = c1 /\ numBatch[self] = 0)
                                  THEN /\ NoMorePossibleUpdates(setSwitches[self])
                                  ELSE /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = "Rest"]
                            /\ UNCHANGED << controllerState, switchState, 
                                            canUpdate, latestUpdateRcv, 
                                            latestUpdateSnt, 
                                            latestSWConsidered, failedTimes, 
                                            setSwitches, copySet, s, 
                                            considered, updated, numBatch >>

Rest(self) == /\ pc[self] = "Rest"
              /\ latestSWConsidered' = max(setSwitches[self])
              /\ considered' = [considered EXCEPT ![self] = {}]
              /\ pc' = [pc EXCEPT ![self] = "SendAllUpdates"]
              /\ UNCHANGED << controllerState, switchState, canUpdate, 
                              latestUpdateRcv, latestUpdateSnt, failedTimes, 
                              setSwitches, copySet, s, updated, numBatch >>

SendAllUpdates(self) == /\ pc[self] = "SendAllUpdates"
                        /\ pc' = [pc EXCEPT ![self] = "CheckIfFinished"]
                        /\ UNCHANGED << controllerState, switchState, 
                                        canUpdate, latestUpdateRcv, 
                                        latestUpdateSnt, latestSWConsidered, 
                                        failedTimes, setSwitches, copySet, s, 
                                        considered, updated, numBatch >>

CheckIfFinished(self) == /\ pc[self] = "CheckIfFinished"
                         /\ IF (Cardinality(setSwitches[self]) - Cardinality(considered[self]) = 0)
                               THEN /\ pc' = [pc EXCEPT ![self] = "check"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "f1"]
                         /\ UNCHANGED << controllerState, switchState, 
                                         canUpdate, latestUpdateRcv, 
                                         latestUpdateSnt, latestSWConsidered, 
                                         failedTimes, setSwitches, copySet, s, 
                                         considered, updated, numBatch >>

f1(self) == /\ pc[self] = "f1"
            /\ IF (self = c0 /\ controllerState.c0 = "primary")
                  THEN /\ \/ /\ controllerState' = [controllerState EXCEPT !.c0 = "failed",
                                                                           !.c1 = "primary"]
                             /\ pc' = [pc EXCEPT ![self] = "EndCont"]
                          \/ /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "sendUpdate"]
                             /\ UNCHANGED controllerState
                  ELSE /\ pc' = [pc EXCEPT ![self] = "sendUpdate"]
                       /\ UNCHANGED controllerState
            /\ UNCHANGED << switchState, canUpdate, latestUpdateRcv, 
                            latestUpdateSnt, latestSWConsidered, failedTimes, 
                            setSwitches, copySet, s, considered, updated, 
                            numBatch >>

sendUpdate(self) == /\ pc[self] = "sendUpdate"
                    /\ s' = [s EXCEPT ![self] = min(setSwitches[self]\(considered[self]))]
                    /\ considered' = [considered EXCEPT ![self] = considered[self] \union {s'[self]}]
                    /\ IF numBatch[self] = 0
                          THEN /\ IF switchState[s'[self]] = Updated
                                     THEN /\ pc' = [pc EXCEPT ![self] = "SendAllUpdates"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "sendIRs"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "sendIRs"]
                    /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                    latestUpdateRcv, latestUpdateSnt, 
                                    latestSWConsidered, failedTimes, 
                                    setSwitches, copySet, updated, numBatch >>

sendIRs(self) == /\ pc[self] = "sendIRs"
                 /\ canUpdate' = [canUpdate EXCEPT ![s[self]] = canUpdate[s[self]] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "SendAllUpdates"]
                 /\ UNCHANGED << controllerState, switchState, latestUpdateRcv, 
                                 latestUpdateSnt, latestSWConsidered, 
                                 failedTimes, setSwitches, copySet, s, 
                                 considered, updated, numBatch >>

check(self) == /\ pc[self] = "check"
               /\ IF (self = c0 /\ controllerState.c0 = "primary")
                     THEN /\ \/ /\ controllerState' = [controllerState EXCEPT !.c0 = "failed",
                                                                              !.c1 = "primary"]
                                /\ pc' = [pc EXCEPT ![self] = "EndCont"]
                             \/ /\ TRUE
                                /\ pc' = [pc EXCEPT ![self] = "nofail"]
                                /\ UNCHANGED controllerState
                     ELSE /\ pc' = [pc EXCEPT ![self] = "nofail"]
                          /\ UNCHANGED controllerState
               /\ UNCHANGED << switchState, canUpdate, latestUpdateRcv, 
                               latestUpdateSnt, latestSWConsidered, 
                               failedTimes, setSwitches, copySet, s, 
                               considered, updated, numBatch >>

nofail(self) == /\ pc[self] = "nofail"
                /\ NoMorePossibleUpdates(setSwitches[self])
                /\ setSwitches' = [setSwitches EXCEPT ![self] = getFailed(copySet[self])]
                /\ IF Cardinality(setSwitches'[self]) = 0
                      THEN /\ latestUpdateRcv' = max(copySet[self])
                           /\ numBatch' = [numBatch EXCEPT ![self] = numBatch[self] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "ControllerObj"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "resendUpdates"]
                           /\ UNCHANGED << latestUpdateRcv, numBatch >>
                /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                latestUpdateSnt, latestSWConsidered, 
                                failedTimes, copySet, s, considered, updated >>

resendUpdates(self) == /\ pc[self] = "resendUpdates"
                       /\ considered' = [considered EXCEPT ![self] = {}]
                       /\ pc' = [pc EXCEPT ![self] = "SendAllUpdates"]
                       /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                       latestUpdateRcv, latestUpdateSnt, 
                                       latestSWConsidered, failedTimes, 
                                       setSwitches, copySet, s, updated, 
                                       numBatch >>

EndCont(self) == /\ pc[self] = "EndCont"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << controllerState, switchState, canUpdate, 
                                 latestUpdateRcv, latestUpdateSnt, 
                                 latestSWConsidered, failedTimes, setSwitches, 
                                 copySet, s, considered, updated, numBatch >>

c(self) == Controller(self) \/ ControllerObj(self)
              \/ check1stbatchForC1(self) \/ Rest(self)
              \/ SendAllUpdates(self) \/ CheckIfFinished(self) \/ f1(self)
              \/ sendUpdate(self) \/ sendIRs(self) \/ check(self)
              \/ nofail(self) \/ resendUpdates(self) \/ EndCont(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in SW: swProc(self))
           \/ (\E self \in {c0, c1}: c(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in SW : WF_vars(swProc(self))
        /\ \A self \in {c0, c1} : WF_vars(c(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f6daa1adc53108e191fb0afd9bb370ba
Consistency == <>(/\ \A x \in SW: /\ switchState[x] = Updated
                                  /\ canUpdate[x] = 1)
UpdateInv == \A x \in SW: canUpdate[x] \leq 1                  
TerminationProp == <>( \/ /\ pc[c0] = "Done"
                          /\ pc[c1] = "Done"
                          /\ \A self \in SW: \/ pc[self] = "Switch" 
                                             \/ pc[self] = "Done" 
                       \/ /\ pc[c0] = "Done"
                          /\ pc[c1] = "Controller"
                          /\ \A self \in SW: pc[self] = "Done")

=============================================================================
\* Modification History
\* Last modified Wed Jul 22 10:58:34 UTC 2020 by root
\* Created Tue Jul 21 11:11:44 UTC 2020 by root

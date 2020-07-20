------------------------------ MODULE starter ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT SW         \* The set of switches SW=1..3 

(*--algorithm starter
variable swState = [sw \in SW |-> "unupdated"],
         controllerState = "unupdated";
\*TypeOK == 
\*  /\ swState \in [sw -> {"updated", "unupdated"}]
\*  /\ controllerState \in {"available", "updated"}
  
define 
    canUpdateSW == controllerState = "updated"
    canUpdateController == controllerState = "unupdated"
end define;

fair process sw \in SW
begin SWITCH:
    while swState[self] \in {"unupdated"} do
        await canUpdateSW;
        either
            swState[self] := "updated";
        
        or
            swState[self] := "unupdated";
        end either;  
    end while;     
    
end process;

fair process controller = 0
begin Controller:
    await canUpdateController;
    controllerState := "updated";
end process;
end algorithm;*)


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-88e1ae36999388ea03ad0bf049e73f3f
VARIABLES swState, controllerState, pc

(* define statement *)
canUpdateSW == controllerState = "updated"
canUpdateController == controllerState = "unupdated"


vars == << swState, controllerState, pc >>

ProcSet == (SW) \cup {0}

Init == (* Global variables *)
        /\ swState = [sw \in SW |-> "unupdated"]
        /\ controllerState = "unupdated"
        /\ pc = [self \in ProcSet |-> CASE self \in SW -> "SWITCH"
                                        [] self = 0 -> "Controller"]

SWITCH(self) == /\ pc[self] = "SWITCH"
                /\ IF swState[self] \in {"unupdated"}
                      THEN /\ canUpdateSW
                           /\ \/ /\ swState' = [swState EXCEPT ![self] = "updated"]
                              \/ /\ swState' = [swState EXCEPT ![self] = "unupdated"]
                           /\ pc' = [pc EXCEPT ![self] = "SWITCH"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED swState
                /\ UNCHANGED controllerState

sw(self) == SWITCH(self)

Controller == /\ pc[0] = "Controller"
              /\ canUpdateController
              /\ controllerState' = "updated"
              /\ pc' = [pc EXCEPT ![0] = "Done"]
              /\ UNCHANGED swState

controller == Controller

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == controller
           \/ (\E self \in SW: sw(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in SW : WF_vars(sw(self))
        /\ WF_vars(controller)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5ea2ea1199a0fa086a4e724815a7978a
Consistency == 
  \E s \in SW: ~ /\ swState[s] = "unupdated"
                  /\ controllerState = "updated"
\*Consistency == controllerState = "updated" ~> \A s \in SW: swState[s] = "updated"

=============================================================================
\* Modification History
\* Last modified Sun Jul 19 19:33:01 PDT 2020 by zmy
\* Created Sun Jul 19 16:02:48 PDT 2020 by zmy

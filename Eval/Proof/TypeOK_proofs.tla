---- MODULE TypeOK_proofs ----
EXTENDS TLAPS, zenith

\* Locality lemmas ...
locality == INSTANCE locality_proofs

TypeOKSWProc ==
    /\ ingressPkt \in (MSG_SET_OF_CMD \cup {NADIR_NULL})
    /\ installedIRs \in Seq(INSTALLABLE_IR_SET)

\* Proved with Z3
THEOREM TypeOKSWProc_Proof == ModuleSpec => []TypeOKSWProc
<1>1 Init => TypeOKSWProc
    BY DEF Init, TypeOKSWProc
<1>2 ModuleNext /\ TypeOKSWProc => TypeOKSWProc'
    <2> SUFFICES ASSUME ModuleNext, TypeOKSWProc PROVE TypeOKSWProc'
    <2> QED 
<1>3 TypeOKSWProc /\ UNCHANGED vars => TypeOKSWProc'
    BY DEF TypeOKSWProc, vars
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ModuleSpec

TypeOKSWFail ==
    /\ sw_fail_ordering_var \in Seq(SUBSET STRUCT_SET_SWITCH_OBJECT)
    /\ statusMsg \in (MSG_SET_SWITCH_EVENT \cup {NADIR_NULL})
    /\ switchObject \in (STRUCT_SET_SWITCH_OBJECT \cup {NADIR_NULL})

TypeOKSWResolve ==
    /\ statusResolveMsg \in (MSG_SET_SWITCH_EVENT \cup {NADIR_NULL})

TypeOKNIBEH ==
    /\ nibEvent \in (MSG_SET_TE_EVENT \cup {NADIR_NULL})
    /\ RCIRStatus \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]
    /\ RCSwSuspensionStatus \in [SW -> ENUM_SET_SW_STATE]

TypeOKTE ==
    /\ topoChangeEvent \in (MSG_SET_TE_EVENT \cup {NADIR_NULL})
    /\ currSetDownSw \in SUBSET SW
    /\ prev_dag_id \in (DAG_ID_SET \cup {NADIR_NULL})
    /\ DAGID \in (DAG_ID_SET \cup {NADIR_NULL})
    /\ init \in BOOLEAN
    /\ nxtDAG \in (STRUCT_SET_DAG_OBJECT \cup {NADIR_NULL})
    /\ setRemovableIRs \in SUBSET SCHEDULABLE_IR_SET
    /\ nxtDAGVertices \in SUBSET SCHEDULABLE_IR_SET
    /\ irsToUnschedule \in SUBSET SCHEDULABLE_IR_SET
    /\ unschedule \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
    /\ irToRemove \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
    /\ irToAdd \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
    /\ irsToConnect \in SUBSET SCHEDULABLE_IR_SET
    /\ irToConnect \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})

TypeOKBoss ==
    /\ seqEvent \in (MSG_SET_DAG_EVENT \cup {NADIR_NULL})

TypeOKSEQ == 
    /\ toBeScheduledIRs \in SUBSET SCHEDULABLE_IR_SET
    /\ nextIR \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
    /\ currDAG \in (STRUCT_SET_DAG_OBJECT \cup {NADIR_NULL})
    /\ IRDoneSet \in SUBSET SCHEDULABLE_IR_SET
    /\ irSet \in SUBSET SCHEDULABLE_IR_SET
    /\ pickedIR \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
    /\ seqWorkerIsBusy \in BOOLEAN

TypeOKWP ==
    /\ nextIRObjectToSend \in (STRUCT_IR \cup {NADIR_NULL})
    /\ index \in Nat

TypeOKEH ==
    /\ monitoringEvent \in (MSG_SET_KEEPALIVE \cup MSG_SET_TIMEOUT \cup {NADIR_NULL})
    /\ setIRsToReset \in SUBSET SCHEDULABLE_IR_SET
    /\ resetIR \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})
    /\ SwSuspensionStatus \in [SW -> ENUM_SET_SW_STATE]

TypeOKMS ==
    /\ msg \in (MSG_SET_SWITCH_EVENT \cup {NADIR_NULL})
    /\ currentIRID \in (SCHEDULABLE_IR_SET \cup {NADIR_NULL})

TypeOKModuleSW ==
    /\ switchStatus \in [SW -> STRUCT_SET_SWITCH_STATUS]
    /\ TCAM \in [SW -> SUBSET INSTALLABLE_IR_SET]
    /\ controlMsgCounter \in [SW -> Nat]
    /\ RecoveryStatus \in [SW -> STRUCT_RECOVERY_STATUS]

TypeOKModuleRC ==
    /\ ScheduledIRs \in [SCHEDULABLE_IR_SET -> BOOLEAN]
    /\ DAGState \in [DAG_ID_SET -> ENUM_SET_DAG_STATE]

TypeOKModuleOFC ==
    /\ NIBIRStatus \in [INSTALLABLE_IR_SET -> STRUCT_IR_PAIR]

TypeOKQueues ==
    /\ swSeqChangedStatus \in Seq(MSG_SET_TIMEOUT \cup MSG_SET_KEEPALIVE)
    /\ switch2Controller \in Seq(MSG_SET_SWITCH_EVENT)
    /\ TEEventQueue \in Seq(MSG_SET_TE_EVENT)
    /\ DAGEventQueue \in Seq(MSG_SET_DAG_EVENT)
    /\ DAGQueue \in Seq(STRUCT_SET_DAG_OBJECT)
    /\ RCNIBEventQueue \in Seq(MSG_SET_TE_EVENT)
    /\ IRQueueNIB \in Seq(STRUCT_SET_NIB_TAGGED_IR)
    /\ controller2Switch \in [SW -> Seq(MSG_SET_OF_CMD)]

LEMMA StitchingLemma == (
/\ TypeOKSWProc
/\ TypeOKSWFail
/\ TypeOKSWResolve
/\ TypeOKNIBEH
/\ TypeOKTE
/\ TypeOKBoss
/\ TypeOKSEQ
/\ TypeOKWP
/\ TypeOKEH
/\ TypeOKMS
/\ TypeOKModuleSW
/\ TypeOKModuleRC
/\ TypeOKModuleOFC
/\ TypeOKQueues) <=> TypeOK
PROOF BY DEF TypeOK, TypeOKSWProc, TypeOKSWFail, TypeOKSWResolve ,TypeOKNIBEH,
             TypeOKTE, TypeOKBoss, TypeOKSEQ, TypeOKWP, TypeOKEH, TypeOKMS, TypeOKModuleSW,
             TypeOKModuleRC, TypeOKModuleOFC, TypeOKQueues

LEMMA AUX_TypeOK_is_inv == Spec => []AUX_TypeOK
PROOF OMITTED

====
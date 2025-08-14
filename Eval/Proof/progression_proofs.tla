---- MODULE progression_proofs ----
EXTENDS TLAPS, zenith, fairness_proofs

\* See `TypeOK_proofs.tla` for this
LEMMA TypeOK_inv == Spec => []TypeOK
PROOF OMITTED 
LEMMA AUX_TypeOK_inv == Spec => []AUX_TypeOK
PROOF OMITTED 
LEMMA PC_TypeOK_inv == Spec => []PC_TypeOK
PROOF OMITTED  

LEMMA TypeOK_transit == TypeOK /\ [Next]_vars => TypeOK'
PROOF OMITTED 
LEMMA AUX_TypeOK_transit == AUX_TypeOK /\ [Next]_vars => AUX_TypeOK'
PROOF OMITTED 
LEMMA PC_TypeOK_transit == PC_TypeOK /\ [Next]_vars => PC_TypeOK'
PROOF OMITTED  

LEMMA WPPCLemma == 
    \A t \in CONTROLLER_THREAD_POOL:
        Spec /\ TypeOK =>
            (~(pc[<<ofc0, t>>] = "ControllerThread") ~> (pc[<<ofc0, t>>] = "ControllerThread"))

\* For any WP thread, an object on `IRQueueNIB` is `unprocessed`, if the current
\* object index in the thread does not point to it.
\* Note that merely using `ExistsItemWithTag` will not be enough, since it would
\* make it look like the object is unprocessed while the thread is actively working
\* on it.
WPHasUnprocessedEvent(self) == /\ ExistsItemWithTag(IRQueueNIB, (self[2]))
                               /\ (index[self[2]] # GetFirstItemIndexWithTag(IRQueueNIB, (self[2])))
                               /\ TypeOK
                               /\ AUX_TypeOK
                               /\ PC_TypeOK

\* A WP thread has begun processing when it attempts to send the IR and has acquired
\* an object from `IRQueueNIB`.
WPBeginsProcessingEvent(self) == /\ (pc[self] = "ControllerThreadSendIR")
                                 /\ (index[self[2]] = GetFirstItemIndexWithTag(IRQueueNIB, (self[2])))

\* First, WP begins processing by taking an enabled step when an unprocessed event exists
LEMMA WPUnblocks == \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL):
    Spec => (
        (WPHasUnprocessedEvent(self) /\ (pc[self] = "ControllerThread")) 
            ~> WPBeginsProcessingEvent(self)
    )
<1> SUFFICES ASSUME NEW t \in ({ofc0} \X CONTROLLER_THREAD_POOL) PROVE 
    Spec => (
        (WPHasUnprocessedEvent(t) /\ (pc[t] = "ControllerThread")) 
            ~> WPBeginsProcessingEvent(t)
    )
    OBVIOUS 
<1> DEFINE P == WPHasUnprocessedEvent(t) /\ (pc[t] = "ControllerThread")
<1> DEFINE Q == WPBeginsProcessingEvent(t)
<1> USE DEF P, Q
<1> SUFFICES Spec => (P ~> Q)
    BY PTL
<1>1 (P /\ [Next]_vars) => (P' \/ Q')
    <2>1 (P /\ UNCHANGED vars) => P'
        <3>1 UNCHANGED vars => UNCHANGED <<IRQueueNIB, index, pc>>
            BY DEF vars
        <3>2 TypeOK /\ UNCHANGED vars => TypeOK'
            BY TypeOK_transit
        <3>3 AUX_TypeOK /\ UNCHANGED vars => AUX_TypeOK'
            BY AUX_TypeOK_transit
        <3>4 PC_TypeOK /\ UNCHANGED vars => PC_TypeOK'
            BY PC_TypeOK_transit
        <3> QED BY <3>1, <3>2, <3>3, <3>4 DEF WPHasUnprocessedEvent
    <2>2 P /\ Next => (P' \/ Q')
        \* <3> DEFINE SUB_P == /\ ExistsItemWithTag(IRQueueNIB, (t))
        \*                     /\ (index[t] # GetFirstItemIndexWithTag(IRQueueNIB, (t)))
        \*                     /\ (pc[t] = "ControllerThread")
        \* <3> USE DEF SUB_P
        \* <3>1 SUB_P /\ TypeOK /\ AUX_TypeOK <=> P
        \*     BY Isa DEF WPHasUnprocessedEvent
        \* \* <3>1 SUB_P /\ TypeOK /\ AUX_TypeOK /\ Next => SUB_P' /\ TypeOK' /\ AUX_TypeOK'
        \*     \* BY <4>2, TypeOK_transit, AUX_TypeOK_transit
        \* \* <3>seq CASE (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
        \* \*     <4>1 PICK self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self)
        \* \*         BY <3>seq
        \* \*     <4>2 SUB_P /\ Next => SUB_P'
        \* \*         <5>ControllerWorkerSeqProc CASE ControllerWorkerSeqProc(self)
        \* \*         <5>ControllerWorkerSeqScheduleDAG CASE ControllerWorkerSeqScheduleDAG(self)
        \* \*         <5>SchedulerMechanism CASE SchedulerMechanism(self)
        \* \*         <5>AddDeleteDAGIRDoneSet CASE AddDeleteDAGIRDoneSet(self)
        \* \*         <5>RemoveDagFromQueue CASE RemoveDagFromQueue(self)
        \* \*         <5> QED
        \* \*     <4>3 SUB_P /\ TypeOK /\ AUX_TypeOK /\ Next => SUB_P' /\ TypeOK' /\ AUX_TypeOK'
        \* \*         BY <4>2, TypeOK_transit, AUX_TypeOK_transit
        \* \*     <4> QED BY <4>1, <4>2
        \* \* <3>wp CASE (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
        \* \*     <4>1 PICK self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self)
        \* \*         BY <3>wp
        \* \*     <4> QED
        \* \* <3>eh CASE (\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
        \* \*     <4>1 PICK self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self)
        \* \*         BY <3>eh
        \* \*     <4> QED
        \* \* <3>others CASE (
        \* \*     /\ Next
        \* \*     /\ ~(\E self \in ({rc0} \X {CONT_WORKER_SEQ}): controllerSequencer(self))
        \* \*     /\ ~(\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): controllerWorkerThreads(self))
        \* \*     /\ ~(\E self \in ({ofc0} \X {CONT_EVENT}): controllerEventHandler(self))
        \* \* )
        \* \*     (* Other steps do not change IRQueueNIB or local WP variables, so P' remains true *)
        \* \*     PROOF OMITTED
        \* \* <3> QED BY <3>seq, <3>wp, <3>eh, <3>others DEF Next
        \* \* <3> QED BY <3>3
        \* <3> QED
    <2> QED BY <2>1, <2>2
<1>2 P /\ <<ControllerThread(t)>>_vars => Q'
    <2> SUFFICES ASSUME P, <<ControllerThread(t)>>_vars PROVE Q'
        OBVIOUS 
    <2> USE DEF ProcSet, ALL_LABELS
    <2>1 /\ index' = [index EXCEPT ![t[2]] = GetFirstItemIndexWithTag(IRQueueNIB, (t[2]))]
         /\ pc' = [pc EXCEPT ![t] = "ControllerThreadSendIR"]
         /\ UNCHANGED IRQueueNIB
        BY DEF ControllerThread
    <2>2 /\ pc \in [ProcSet -> ALL_LABELS]
         /\ t \in ProcSet
         /\ index \in [CONTROLLER_THREAD_POOL -> Nat]
         /\ t[2] \in CONTROLLER_THREAD_POOL
        \* BY DEF WPHasUnprocessedEvent, TypeOK
    <2>3 /\ pc'[t] = "ControllerThreadSendIR"
         /\ index'[t[2]] = GetFirstItemIndexWithTag(IRQueueNIB', (t[2]))
        BY Zenon, <2>1, <2>2
    <2> QED BY <2>3 DEF WPBeginsProcessingEvent
<1>3 P => ENABLED <<ControllerThread(t)>>_vars
    \* This proof fails on newer TLAPS versions, but succeeds with older ones.
    \* We think that this is a bug, since if the assignment in `AUX_IRQ_deq'`
    \* is commented out, the proof succeeds, which is strange as it is a primed
    \* variable and has no effect on whether or not an action is enabled.
    \* Since we are committed to using a new version of TLAPS, we have no way
    \* to verify this, despite how trivial it is.
    \* NOTE: The reason that we use newer version of TLAPS is because we need
    \*       the features from this pull request to parse Zenith:
    \*       `https://github.com/tlaplus/tlapm/pull/140`
    \* BY Isa, ExpandENABLED DEF ControllerThread, vars, WPHasUnprocessedEvent
<1>4 Spec => WF_vars(ControllerThread(t))
    BY Isa, FAIRNESS_WP DEF Spec
<1> QED BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

\* While an unprocessed event exists, only returning to the top of the loop
\* can restart processing.
LEMMA WPUnprocessedWhileBusy == \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL):
    Spec => (
        (WPHasUnprocessedEvent(self) /\ ~(pc[self] = "ControllerThread"))
            ~> (WPHasUnprocessedEvent(self) /\ (pc[self] = "ControllerThread"))
    )
<1> SUFFICES ASSUME 
    NEW t \in ({ofc0} \X CONTROLLER_THREAD_POOL),
    Spec,
    TypeOK, AUX_TypeOK, PC_TypeOK
    PROVE 
    Spec => (
        (WPHasUnprocessedEvent(t) /\ ~(pc[t] = "ControllerThread"))
            ~> (WPHasUnprocessedEvent(t) /\ (pc[t] = "ControllerThread"))
    )
<1> QED

THEOREM WPEventuallyProcessesEvents == \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL):
    Spec => (WPHasUnprocessedEvent(self) ~> WPBeginsProcessingEvent(self))
<1> SUFFICES ASSUME Spec,
        NEW self \in ({ofc0} \X CONTROLLER_THREAD_POOL)
    PROVE Spec => (WPHasUnprocessedEvent(self) ~> WPBeginsProcessingEvent(self))
    OBVIOUS 
<1>1 (WPHasUnprocessedEvent(self) /\ (pc[self] = "ControllerThread")) 
        ~> WPBeginsProcessingEvent(self)
    BY WPUnblocks
<1>2 (WPHasUnprocessedEvent(self) /\ ~(pc[self] = "ControllerThread"))
        ~> (WPHasUnprocessedEvent(self) /\ (pc[self] = "ControllerThread"))
    BY WPUnprocessedWhileBusy
<1> QED BY <1>1, <1>2, PTL
====
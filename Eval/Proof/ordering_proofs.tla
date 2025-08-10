---- MODULE ordering_proofs ----
EXTENDS TLAPS, zenith, SequenceTheorems

\* Note: With TLAPS 1.6.0, most proofs with the `<=>` token just fail with Z3.
\*       However, Zenon is still able to finish them.

\* See `locality_proofs` for this
LEMMA SwitchProcessLocality ==
    \A sw \in SW: 
        TypeOK /\ AUX_TypeOK /\ Next /\ ~(swProcess(<<SW_SIMPLE_ID, sw>>)) => UNCHANGED swProcessLocals(sw)

LEMMA SequenceDomain == 
ASSUME 
    NEW S, NEW seq \in Seq(S)
PROVE DOMAIN seq = 1..Len(seq)
PROOF OBVIOUS 

\* See `TypeOK_proofs` for these
LEMMA AUX_TypeOK_is_inv == Spec => []AUX_TypeOK
PROOF OMITTED
LEMMA AUX_TypeOK_transit == AUX_TypeOK /\ Next => AUX_TypeOK'
PROOF OMITTED 
LEMMA TypeOK_is_inv == Spec => []TypeOK
PROOF OMITTED 
LEMMA TypeOK_in_transit == TypeOK /\ Next => TypeOK'
PROOF OMITTED 

\* We will take as fact that `IRQueueNIB` and `controller2switch`, individually,
\* preserve order.
\* The goal of this proof is to show that the composition of the two also preserves
\* ordering.

LEMMA IRQ_ordering_transit == (IRQ_ordering /\ Next /\ AUX_TypeOK /\ TypeOK) => IRQ_ordering'
PROOF OMITTED 
LEMMA C2S_ordering_transit == (C2S_ordering /\ Next /\ AUX_TypeOK /\ TypeOK) => C2S_ordering'
PROOF OMITTED 

LEMMA IRQ_ordering_is_inv == Spec => []IRQ_ordering
<1> USE DEF ConstantAssumptions
<1>1 Init => IRQ_ordering
    BY ConstantAssumptions DEF IRQ_ordering, Init, OrderingPreserved
<1>2 IRQ_ordering /\ (UNCHANGED vars) => IRQ_ordering'
    BY DEF vars, IRQ_ordering, OrderingPreserved
<1> QED BY PTL, <1>1, <1>2, AUX_TypeOK_is_inv, TypeOK_is_inv, IRQ_ordering_transit DEF Spec

LEMMA C2S_ordering_is_inv == Spec => []C2S_ordering
<1> USE DEF ConstantAssumptions
<1>1 Init => C2S_ordering
    BY ConstantAssumptions DEF C2S_ordering, Init, OrderingPreserved
<1>2 C2S_ordering /\ (UNCHANGED vars) => C2S_ordering'
    BY DEF vars, C2S_ordering, OrderingPreserved
<1> QED BY PTL, <1>1, <1>2, AUX_TypeOK_is_inv, TypeOK_is_inv, C2S_ordering_transit DEF Spec

\* We first need to prove the following.
\*  - C1: Any item that appears in `AUX_SEQ_deq` must also appear in `AUX_C2S_deq`
\*  - C2: Any item that appears in `AUX_C2S_enq` must also appear in `AUX_IRQ_deq`
\*  - C3: Any item that appears in `AUX_IRQ_enq` must also appear in `AUX_SEQ_enq`
\* We call these `continuity` lemmas since they assert that objects flow from one
\* queue into another.

LEMMA continuity_C2S_to_switch_transit == (continuity_C2S_to_switch /\ Next /\ AUX_TypeOK/\ TypeOK) => continuity_C2S_to_switch'
<1> SUFFICES ASSUME continuity_C2S_to_switch, Next, AUX_TypeOK, TypeOK PROVE continuity_C2S_to_switch'
    OBVIOUS 
<1> USE DEF continuity_C2S_to_switch, Next, AUX_TypeOK
<1>1 /\ DOMAIN AUX_SEQ_deq' = SW
     /\ DOMAIN AUX_SEQ_deq = SW
     /\ DOMAIN AUX_C2S_deq' = SW
     /\ DOMAIN AUX_C2S_deq = SW
     /\ AUX_TypeOK'
    PROOF BY AUX_TypeOK_transit DEF AUX_TypeOK
<1>2 ASSUME 
        NEW sw \in SW
        PROVE \E f \in [DOMAIN AUX_SEQ_deq'[sw] -> DOMAIN AUX_C2S_deq'[sw]]:
            /\ \A x \in DOMAIN f: AUX_SEQ_deq'[sw][x].sched_num = AUX_C2S_deq'[sw][f[x]].sched_num
            /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    <2>1 \/ (swProcess(<<SW_SIMPLE_ID, sw>>))
         \/ ~(swProcess(<<SW_SIMPLE_ID, sw>>))
        OBVIOUS 
    <2>sw CASE (swProcess(<<SW_SIMPLE_ID, sw>>))
        <3>1 SwitchSimpleProcess(<<SW_SIMPLE_ID, sw>>)
            BY <2>sw DEF swProcess
        <3>2 /\ AUX_C2S_deq' = [AUX_C2S_deq EXCEPT ![sw] = Append(AUX_C2S_deq[sw], ingressPkt'[sw])]
             /\ AUX_SEQ_deq' = [AUX_SEQ_deq EXCEPT ![sw] = Append(AUX_SEQ_deq[sw], ingressPkt'[sw])]
            BY <3>1 DEF SwitchSimpleProcess
        <3>3 /\ AUX_C2S_deq'[sw] = Append(AUX_C2S_deq[sw], ingressPkt'[sw])
             /\ AUX_SEQ_deq'[sw] = Append(AUX_SEQ_deq[sw], ingressPkt'[sw])
            BY <3>2
        <3>4 PICK f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_C2S_deq[sw]]:
                /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_deq[sw][f[x]].sched_num
                /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
            BY <1>1 DEF continuity_C2S_to_switch
        <3>5 /\ DOMAIN AUX_C2S_deq[sw] = 1..Len(AUX_C2S_deq[sw])
             /\ DOMAIN AUX_SEQ_deq[sw] = 1..Len(AUX_SEQ_deq[sw])
             /\ AUX_C2S_deq'[sw] \in Seq(MSG_SET_OF_CMD)
             /\ AUX_SEQ_deq'[sw] \in Seq(MSG_SET_OF_CMD)
            BY <1>1
        <3>6 /\ DOMAIN AUX_C2S_deq'[sw] = 1..Len(AUX_C2S_deq[sw])+1
             /\ DOMAIN AUX_SEQ_deq'[sw] = 1..Len(AUX_SEQ_deq[sw])+1
            BY <3>3, <3>5
        <3>7 DEFINE 
                g == [x \in 1..Len(AUX_SEQ_deq[sw])+1 |-> 
                    IF x = Len(AUX_SEQ_deq[sw])+1 THEN Len(AUX_C2S_deq[sw]) + 1 ELSE f[x]]
        <3>8 DOMAIN g = DOMAIN AUX_SEQ_deq'[sw]
            BY <3>6 DEF g
        <3>9 \A x \in DOMAIN g: \/ /\ g[x] = f[x]
                                   /\ x \in DOMAIN f
                                \/ /\ g[x] = Len(AUX_C2S_deq[sw]) + 1
                                   /\ x = Len(AUX_SEQ_deq[sw])+1
            BY <3>4, <3>5 DEF g
        <3>10 ASSUME 
            NEW x \in DOMAIN g 
            PROVE /\ g[x] \in DOMAIN AUX_C2S_deq'[sw]
                  /\ AUX_SEQ_deq'[sw][x].sched_num = AUX_C2S_deq'[sw][g[x]].sched_num
            <4>a CASE /\ g[x] = f[x]
                      /\ x \in DOMAIN f
                <5>1 g[x] \in 1..Len(AUX_C2S_deq[sw])
                    BY <4>a, <3>4, <3>5
                <5>2 g[x] \in DOMAIN AUX_C2S_deq'[sw]
                    BY <5>1, <3>6
                <5>3 /\ AUX_SEQ_deq'[sw][x].sched_num = AUX_SEQ_deq[sw][x].sched_num
                     /\ AUX_C2S_deq'[sw][g[x]].sched_num = AUX_C2S_deq[sw][g[x]].sched_num
                    BY <4>a, <3>4, <5>1, <3>3
                <5> QED BY <5>2, <5>3, <3>4, <4>a
            <4>b CASE /\ g[x] = Len(AUX_C2S_deq[sw]) + 1
                      /\ x = Len(AUX_SEQ_deq[sw])+1
                <5>1 g[x] \in DOMAIN AUX_C2S_deq'[sw]
                    BY <4>b, <3>6
                <5>2 /\ AUX_SEQ_deq'[sw][x] = ingressPkt'[sw]
                     /\ AUX_C2S_deq'[sw][g[x]] = ingressPkt'[sw]
                    BY <4>b, <3>3
                <5>3 AUX_SEQ_deq'[sw][x].sched_num = AUX_C2S_deq'[sw][g[x]].sched_num
                    BY <5>2
                <5> QED BY <5>1, <5>3
            <4> QED BY <3>9, <4>a, <4>b
        <3>11 \A x, y \in DOMAIN g: (x < y) => (g[x] < g[y])
            <4> SUFFICES ASSUME NEW x \in DOMAIN g, NEW y \in DOMAIN g, x < y PROVE g[x] < g[y]
                BY Zenon
            <4>1 DOMAIN g = 1..Len(AUX_SEQ_deq[sw]) \cup {Len(AUX_SEQ_deq[sw])+1}
                BY SMT DEF g
            <4>2 CASE y \in 1..Len(AUX_SEQ_deq[sw])
                <5>1 x \in DOMAIN f /\ y \in DOMAIN f
                    BY SMT, <4>2, <3>4
                <5>2 g[x] = f[x] /\ g[y] = f[y]
                    BY <4>2 DEF g
                <5> QED BY <5>1, <5>2, <3>4
            <4>3 CASE y = Len(AUX_SEQ_deq[sw])+1
                <5>2 /\ g[y] = Len(AUX_C2S_deq[sw]) + 1
                     /\ x # Len(AUX_SEQ_deq[sw])+1
                     /\ x \in 1..Len(AUX_SEQ_deq[sw])
                     /\ g[x] = f[x]
                    BY <4>1, <4>3 DEF g
                <5>3 f[x] \leq Len(AUX_C2S_deq[sw])
                    BY SMT, <5>2, <3>4
                <5> QED BY SMT, <5>2, <5>3
            <4> QED BY <4>1, <4>2, <4>3
        <3>12 \A x, y \in DOMAIN g: (g[x] < g[y]) => (x < y)
            <4> SUFFICES ASSUME NEW x \in DOMAIN g, NEW y \in DOMAIN g, g[x] < g[y] PROVE x < y
                BY Zenon
            <4>1 DOMAIN g = 1..Len(AUX_SEQ_deq[sw]) \cup {Len(AUX_SEQ_deq[sw])+1}
                (* TODO: For whatever reason, this one fails (despite the previous one working ...) *)
                \* BY SMT DEF g
                PROOF OMITTED 
            <4>2 CASE y \in 1..Len(AUX_SEQ_deq[sw])
                <5>1 CASE x \in 1..Len(AUX_SEQ_deq[sw])
                    <6>1 /\ x \in DOMAIN f
                         /\ y \in DOMAIN f
                         /\ g[x] = f[x] 
                         /\ g[y] = f[y]
                         /\ f[x] < f[y]
                        BY <4>2, <5>1, <3>4 DEF g
                    <6> QED BY <3>4, <6>1
                <5>2 CASE x = Len(AUX_SEQ_deq[sw])+1
                    <6>1 /\ x \in DOMAIN g
                         /\ y \in DOMAIN g
                         /\ y \in DOMAIN f
                         /\ g[y] = f[y]
                         /\ f[y] \leq Len(AUX_C2S_deq[sw])
                         /\ g[x] = Len(AUX_C2S_deq[sw]) + 1
                        BY <4>2, <5>2, <3>4 DEF g
                    <6>2 /\ g[x] > g[y]
                         /\ \A z \in DOMAIN g: g[z] \in Nat
                        BY <6>1 DEF g
                    <6>3 (g[x] > g[y]) /\ (g[x] < g[y]) = FALSE
                        BY SMT, <6>2, <6>1
                    <6> QED BY <6>2, <6>3
                <5> QED BY <5>1, <5>2, <4>1
            <4>3 CASE y = Len(AUX_SEQ_deq[sw])+1
                <5>1 CASE x \in 1..Len(AUX_SEQ_deq[sw])
                    BY SMT, <4>3, <5>1
                <5>2 CASE x = Len(AUX_SEQ_deq[sw])+1
                    <6>1 y = x
                        BY SMT, <4>3, <5>2
                    <6> QED BY <6>1 (* Contradiction ... *)
                <5> QED BY <5>1, <5>2, <4>1
            <4> QED BY <4>1, <4>2, <4>3
        <3>13 \A x, y \in DOMAIN g: (x < y) <=> (g[x] < g[y])
            BY Zenon, <3>11, <3>12
        <3>14 /\ g \in [DOMAIN AUX_SEQ_deq'[sw] -> DOMAIN AUX_C2S_deq'[sw]]
              /\ \A x \in DOMAIN g: AUX_SEQ_deq'[sw][x].sched_num = AUX_C2S_deq'[sw][g[x]].sched_num
            BY <3>10, <3>8
        <3> QED BY Zenon, <3>13, <3>14
    <2>other CASE ~(swProcess(<<SW_SIMPLE_ID, sw>>))
        <3>1 UNCHANGED swProcessLocals(sw)
            BY <2>other, SwitchProcessLocality
        <3> QED BY <3>1 DEF swProcessLocals
    <2> QED BY <2>1, <2>sw, <2>other
<1> QED BY <1>1, <1>2 DEF continuity_C2S_to_switch

\* The proof for these are almost an exact replica of `continuity_C2S_to_switch_transit`.
\* We omit them for brevity.
LEMMA continuity_IRQ_to_C2S_transit == (continuity_IRQ_to_C2S /\ Next /\ AUX_TypeOK /\ TypeOK) => continuity_IRQ_to_C2S'
PROOF OMITTED 
LEMMA continuity_SEQ_to_IRQ_transit == (continuity_SEQ_to_IRQ /\ Next /\ AUX_TypeOK /\ TypeOK) => continuity_SEQ_to_IRQ'
PROOF OMITTED 

\* These follow trivially from above

LEMMA continuity_C2S_to_switch_is_inv == Spec => []continuity_C2S_to_switch
<1>1 Init => continuity_C2S_to_switch
    BY DEF Init, continuity_C2S_to_switch
<1>2 continuity_C2S_to_switch /\ (UNCHANGED vars) => continuity_C2S_to_switch'
    BY DEF vars, continuity_C2S_to_switch
<1> QED BY PTL, <1>1, <1>2, continuity_C2S_to_switch_transit, AUX_TypeOK_is_inv, TypeOK_is_inv DEF Spec

LEMMA continuity_IRQ_to_C2S_is_inv == Spec => []continuity_IRQ_to_C2S
<1>1 Init => continuity_IRQ_to_C2S
    BY ConstantAssumptions DEF Init, continuity_IRQ_to_C2S, ScheduledOfSw, ConstantAssumptions
<1>2 continuity_IRQ_to_C2S /\ (UNCHANGED vars) => continuity_IRQ_to_C2S'
    BY DEF vars, continuity_IRQ_to_C2S
<1> QED BY PTL, <1>1, <1>2, continuity_IRQ_to_C2S_transit, AUX_TypeOK_is_inv, TypeOK_is_inv DEF Spec

LEMMA continuity_SEQ_to_IRQ_is_inv == Spec => []continuity_SEQ_to_IRQ
<1>1 Init => continuity_SEQ_to_IRQ
    BY Isa, ConstantAssumptions DEF Init, continuity_SEQ_to_IRQ, ScheduledOfSw, ConstantAssumptions
<1>2 continuity_SEQ_to_IRQ /\ (UNCHANGED vars) => continuity_SEQ_to_IRQ'
    BY DEF vars, continuity_SEQ_to_IRQ
<1> QED BY PTL, <1>1, <1>2, continuity_SEQ_to_IRQ_transit, AUX_TypeOK_is_inv, TypeOK_is_inv DEF Spec

LEMMA StitchingLemma1 == 
    (continuity_C2S_to_switch /\ C2S_ordering /\ AUX_TypeOK /\ TypeOK) =>
        \A sw \in SW:
            \E f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_C2S_enq[sw]]:
                /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_enq[sw][f[x]].sched_num
                /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
<1> SUFFICES ASSUME 
        continuity_C2S_to_switch, C2S_ordering, AUX_TypeOK, TypeOK,
        NEW sw \in SW
    PROVE 
        \E f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_C2S_enq[sw]]:
            /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_enq[sw][f[x]].sched_num
            /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    OBVIOUS
<1>1 SW = DOMAIN AUX_SEQ_deq
    BY DEF AUX_TypeOK
<1>2 PICK f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_C2S_deq[sw]]:
        /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_deq[sw][f[x]].sched_num
        /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    BY <1>1 DEF continuity_C2S_to_switch
<1>3 PICK g \in [DOMAIN AUX_C2S_deq[sw] -> DOMAIN AUX_C2S_enq[sw]]:
        /\ \A x \in DOMAIN g: AUX_C2S_deq[sw][x] = AUX_C2S_enq[sw][g[x]]
        /\ \A x, y \in DOMAIN g: (x < y) <=> g[x] < g[y]
    BY DEF C2S_ordering, OrderingPreserved
<1>4 DEFINE gof == [x \in DOMAIN AUX_SEQ_deq[sw] |-> g[f[x]]]
<1>5 /\ DOMAIN gof = DOMAIN AUX_SEQ_deq[sw]
     /\ \A x \in DOMAIN gof: gof[x] \in DOMAIN AUX_C2S_enq[sw]
    BY <1>2, <1>3 DEF gof
<1>6 gof \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_C2S_enq[sw]]
    BY <1>5
<1>7 ASSUME
    NEW x \in DOMAIN gof,
    NEW y \in DOMAIN gof
    PROVE /\ (x < y) <=> (gof[x] < gof[y])
          /\ AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_enq[sw][gof[x]].sched_num
    <2>1 /\ (x < y) <=> (f[x] < f[y])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_deq[sw][f[x]].sched_num
        BY <1>6, <1>2
    <2>2 /\ f[x] \in DOMAIN g
         /\ f[y] \in DOMAIN g
        BY <1>2, <1>3
    <2>3 /\ (f[x] < f[y]) <=> (g[f[x]] < g[f[y]])
         /\ AUX_C2S_deq[sw][f[x]] = AUX_C2S_enq[sw][g[f[x]]]
        BY <2>2, <1>3
    <2>4 /\ (x < y) <=> (g[f[x]] < g[f[y]])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_enq[sw][g[f[x]]].sched_num
        BY <2>1, <2>3
    <2> QED BY <2>4 DEF gof
<1> QED BY <1>6, <1>7, <1>1

LEMMA StitchingLemma2 == 
    (continuity_C2S_to_switch /\ C2S_ordering /\ continuity_IRQ_to_C2S /\ AUX_TypeOK /\ TypeOK) =>
        \A sw \in SW:
            \E f \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]], sw)]:
                /\ \A x \in DOMAIN f: /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][f[x]].sched_num
                                      /\ AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][f[x]].sw = sw
                /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
<1> SUFFICES ASSUME
        continuity_C2S_to_switch, C2S_ordering, continuity_IRQ_to_C2S, AUX_TypeOK, TypeOK,
        NEW sw \in SW
    PROVE 
        \E f \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]], sw)]:
            /\ \A x \in DOMAIN f: /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][f[x]].sched_num
                                  /\ AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][f[x]].sw = sw
            /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    OBVIOUS 
<1>1 /\ SW = DOMAIN AUX_SEQ_deq
     /\ SW = DOMAIN AUX_C2S_enq
    BY DEF AUX_TypeOK
<1>2 PICK f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_C2S_enq[sw]]:
        /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_enq[sw][f[x]].sched_num
        /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    BY StitchingLemma1
<1>3 PICK g \in [DOMAIN AUX_C2S_enq[sw] -> ScheduledOfSw(AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]], sw)]:
        /\ \A x \in DOMAIN g: 
            /\ AUX_C2S_enq[sw][x].sched_num = AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][g[x]].sched_num
            /\ AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][g[x]].sw = sw
        /\ \A x, y \in DOMAIN g: (x < y) <=> g[x] < g[y]
    BY <1>1 DEF continuity_IRQ_to_C2S
<1>4 DEFINE gof == [x \in DOMAIN AUX_SEQ_deq[sw] |-> g[f[x]]]
<1>5 /\ DOMAIN gof = DOMAIN AUX_SEQ_deq[sw]
     /\ \A x \in DOMAIN gof: gof[x] \in ScheduledOfSw(AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]], sw)
    BY <1>2, <1>3 DEF gof
<1>6 gof \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]], sw)]
    BY <1>5
<1>7 ASSUME
    NEW x \in DOMAIN gof,
    NEW y \in DOMAIN gof
    PROVE /\ (x < y) <=> (gof[x] < gof[y])
          /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][gof[x]].sched_num
          /\ AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][gof[x]].sw = sw
    <2>1 /\ (x < y) <=> (f[x] < f[y])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_C2S_enq[sw][f[x]].sched_num
        BY <1>6, <1>2
    <2>2 /\ f[x] \in DOMAIN g
         /\ f[y] \in DOMAIN g
        BY <1>2, <1>3
    <2>3 /\ (f[x] < f[y]) <=> (g[f[x]] < g[f[y]])
         /\ AUX_C2S_enq[sw][f[x]].sched_num = AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][g[f[x]]].sched_num
         /\ AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][g[f[x]]].sw = sw
        BY <2>2, <1>3
    <2>4 /\ (x < y) <=> (g[f[x]] < g[f[y]])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][g[f[x]]].sched_num
         /\ AUX_IRQ_deq[SW_THREAD_SHARD_MAP[sw]][g[f[x]]].sw = sw
        BY <2>1, <2>3
    <2> QED BY <2>4 DEF gof
<1> QED BY <1>6, <1>7, <1>1

LEMMA StitchingLemma3 == 
    (continuity_C2S_to_switch /\ C2S_ordering /\ continuity_IRQ_to_C2S /\ IRQ_ordering /\ AUX_TypeOK /\ TypeOK) =>
        \A sw \in SW:
            \E f \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_enq[SW_THREAD_SHARD_MAP[sw]], sw)]:
                /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_enq[SW_THREAD_SHARD_MAP[sw]][f[x]].sched_num
                /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
<1> SUFFICES ASSUME
        continuity_C2S_to_switch, C2S_ordering, continuity_IRQ_to_C2S, IRQ_ordering, AUX_TypeOK, TypeOK,
        NEW sw \in SW
    PROVE 
        \E f \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_enq[SW_THREAD_SHARD_MAP[sw]], sw)]:
            /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_enq[SW_THREAD_SHARD_MAP[sw]][f[x]].sched_num
            /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    OBVIOUS 
<1>a DEFINE t == SW_THREAD_SHARD_MAP[sw]
<1>1 /\ SW = DOMAIN AUX_SEQ_deq
     /\ SW = DOMAIN AUX_C2S_enq
     /\ t \in CONTROLLER_THREAD_POOL
    BY ConstantAssumptions DEF AUX_TypeOK, t, ConstantAssumptions
<1>2 PICK f \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_deq[t], sw)]:
        /\ \A x \in DOMAIN f: /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_deq[t][f[x]].sched_num
                              /\ AUX_IRQ_deq[t][f[x]].sw = sw
        /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    BY StitchingLemma2 DEF t
<1>2a /\ ScheduledOfSw(AUX_IRQ_deq[t], sw) \subseteq DOMAIN AUX_IRQ_deq[t]
      /\ \A x \in DOMAIN f: f[x] \in ScheduledOfSw(AUX_IRQ_deq[t], sw)
    BY <1>2 DEF ScheduledOfSw, t
<1>3 PICK g \in [DOMAIN AUX_IRQ_deq[t] -> DOMAIN AUX_IRQ_enq[t]]:
        /\ \A x \in DOMAIN g: 
            AUX_IRQ_deq[t][x] = AUX_IRQ_enq[t][g[x]]
        /\ \A x, y \in DOMAIN g: (x < y) <=> g[x] < g[y]
    BY <1>1 DEF IRQ_ordering, OrderingPreserved, t
<1>4 DEFINE gof == [x \in DOMAIN AUX_SEQ_deq[sw] |-> g[f[x]]]
<1>5 /\ DOMAIN gof = DOMAIN AUX_SEQ_deq[sw]
     /\ \A x \in DOMAIN gof: /\ AUX_IRQ_deq[t][f[x]].sw = sw
                             /\ f[x] \in DOMAIN g
    BY <1>2, <1>2a, <1>3 DEF gof, t
<1>6 \A x \in DOMAIN gof: AUX_IRQ_enq[t][gof[x]].sw = sw
    BY <1>5, <1>3 DEF gof, t
<1>7 \A x \in DOMAIN gof: gof[x] \in ScheduledOfSw(AUX_IRQ_enq[t], sw)
    BY <1>6 DEF ScheduledOfSw
<1>8 gof \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_enq[t], sw)]
    BY <1>5, <1>7
<1>9 ASSUME
    NEW x \in DOMAIN gof,
    NEW y \in DOMAIN gof
    PROVE /\ (x < y) <=> (gof[x] < gof[y])
          /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_enq[t][gof[x]].sched_num
    <2>1 /\ (x < y) <=> (f[x] < f[y])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_deq[t][f[x]].sched_num
        BY <1>2 DEF t
    <2>2 /\ f[x] \in DOMAIN g
         /\ f[y] \in DOMAIN g
        BY <1>5
    <2>3 /\ (f[x] < f[y]) <=> (g[f[x]] < g[f[y]])
         /\ AUX_IRQ_deq[t][f[x]].sched_num = AUX_IRQ_enq[t][g[f[x]]].sched_num
        BY <2>2, <1>3 DEF t
    <2>4 /\ (x < y) <=> (g[f[x]] < g[f[y]])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_enq[t][g[f[x]]].sched_num
        BY <2>1, <2>3 DEF t
    <2> QED BY <2>4 DEF gof
<1> QED BY <1>8, <1>9, <1>1

Continuity == (continuity_C2S_to_switch /\ C2S_ordering /\ continuity_IRQ_to_C2S /\ IRQ_ordering /\ continuity_SEQ_to_IRQ)

LEMMA ContinuityLemma == 
    (Continuity /\ AUX_TypeOK /\ TypeOK) =>
        \A sw \in SW:
            \E f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_SEQ_enq[sw]]:
                /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_SEQ_enq[sw][f[x]].sched_num
                /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
<1> SUFFICES ASSUME 
        (continuity_C2S_to_switch /\ C2S_ordering /\ continuity_IRQ_to_C2S /\ IRQ_ordering),
        continuity_SEQ_to_IRQ,
        AUX_TypeOK, TypeOK,
        NEW sw \in SW
    PROVE 
        \E f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_SEQ_enq[sw]]:
            /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_SEQ_enq[sw][f[x]].sched_num
            /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    BY DEF Continuity
<1>a DEFINE t == SW_THREAD_SHARD_MAP[sw]
<1>1 /\ SW = DOMAIN AUX_SEQ_deq
     /\ SW = DOMAIN AUX_C2S_enq
     /\ SW = DOMAIN AUX_SEQ_enq
     /\ t \in CONTROLLER_THREAD_POOL
    BY ConstantAssumptions DEF AUX_TypeOK, t, ConstantAssumptions
<1>2 PICK f \in [DOMAIN AUX_SEQ_deq[sw] -> ScheduledOfSw(AUX_IRQ_enq[t], sw)]:
            /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_enq[t][f[x]].sched_num
            /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    BY StitchingLemma3 DEF t
<1>3 PICK g \in [ScheduledOfSw(AUX_IRQ_enq[t], sw) -> DOMAIN AUX_SEQ_enq[sw]]:
        /\ \A x \in DOMAIN g:
            AUX_IRQ_enq[t][x].sched_num = AUX_SEQ_enq[sw][g[x]].sched_num
        /\ \A x, y \in DOMAIN g: (x < y) <=> g[x] < g[y]
    BY <1>1 DEF continuity_SEQ_to_IRQ, t
<1>4 DEFINE gof == [x \in DOMAIN AUX_SEQ_deq[sw] |-> g[f[x]]]
<1>5 /\ DOMAIN gof = DOMAIN AUX_SEQ_deq[sw]
     /\ \A x \in DOMAIN gof: 
            gof[x] \in DOMAIN AUX_SEQ_enq[sw]
    BY <1>2, <1>3 DEF gof
<1>6 gof \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_SEQ_enq[sw]]
    BY <1>5
<1>7 ASSUME
    NEW x \in DOMAIN gof,
    NEW y \in DOMAIN gof
    PROVE /\ (x < y) <=> (gof[x] < gof[y])
          /\ AUX_SEQ_deq[sw][x].sched_num = AUX_SEQ_enq[sw][gof[x]].sched_num
    <2>1 /\ (x < y) <=> (f[x] < f[y])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_IRQ_enq[t][f[x]].sched_num
        BY <1>2 DEF t
    <2>2 /\ f[x] \in DOMAIN g
         /\ f[y] \in DOMAIN g
        BY <1>2, <1>3
    <2>3 /\ (f[x] < f[y]) <=> (g[f[x]] < g[f[y]])
         /\ AUX_IRQ_enq[t][f[x]].sched_num = AUX_SEQ_enq[sw][g[f[x]]].sched_num
        BY <2>2, <1>3 DEF t
    <2>4 /\ (x < y) <=> (g[f[x]] < g[f[y]])
         /\ AUX_SEQ_deq[sw][x].sched_num = AUX_SEQ_enq[sw][g[f[x]]].sched_num
        BY <2>1, <2>3 DEF t
    <2> QED BY <2>4 DEF gof
<1> QED BY <1>6, <1>7, <1>1

LEMMA continuity_implies_ordering == 
    (Continuity /\ AUX_TypeOK /\ TypeOK) => AUX_SeqOrderPreserved
<1> SUFFICES ASSUME 
        Continuity, AUX_TypeOK, TypeOK
    PROVE 
        AUX_SeqOrderPreserved
    OBVIOUS
<1>1 /\ SW = DOMAIN AUX_SEQ_deq
     /\ SW = DOMAIN AUX_SEQ_enq
    BY ConstantAssumptions DEF AUX_TypeOK, ConstantAssumptions
<1>2 ASSUME NEW sw \in SW
    PROVE 
        \E f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_SEQ_enq[sw]]:
            /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_SEQ_enq[sw][f[x]].sched_num
            /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
    <2>1 PICK f \in [DOMAIN AUX_SEQ_deq[sw] -> DOMAIN AUX_SEQ_enq[sw]]:
                /\ \A x \in DOMAIN f: AUX_SEQ_deq[sw][x].sched_num = AUX_SEQ_enq[sw][f[x]].sched_num
                /\ \A x, y \in DOMAIN f: (x < y) <=> f[x] < f[y]
        BY ContinuityLemma
    <2> QED BY <2>1
<1> QED BY <1>2 DEF AUX_SeqOrderPreserved

LEMMA Continuity_is_inv == Spec => []Continuity
BY PTL, IRQ_ordering_is_inv, C2S_ordering_is_inv, continuity_C2S_to_switch_is_inv, continuity_IRQ_to_C2S_is_inv, continuity_SEQ_to_IRQ_is_inv DEF Continuity

THEOREM seq_ordering_is_inv == Spec => []AUX_SeqOrderPreserved
BY PTL, Continuity_is_inv, continuity_implies_ordering, AUX_TypeOK_is_inv, TypeOK_is_inv
====
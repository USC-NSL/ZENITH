---------------------------- MODULE dag ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

min(set) == CHOOSE x \in set: \A y \in set: x \leq y

RECURSIVE Paths(_, _)
Paths(n, G) ==  
    IF n = 1
    THEN 
        G
    ELSE
        LET 
            nextVs(p) == { e[2] : e \in {e \in G : e[1] = p[Len(p)]} }
            nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
        IN
            UNION {nextPaths(p) : p \in Paths(n-1, G)} \cup Paths(n-1, G)

RECURSIVE AllPossibleSizes(_, _)
AllPossibleSizes(maxSize, sumUpToNow) == 
    IF sumUpToNow = 0
    THEN
        {<<0>>}
    ELSE
        LET 
            Upperbound == min({sumUpToNow, maxSize})
        IN
            UNION {{<<x>> \o y: y \in AllPossibleSizes(x, sumUpToNow-x)}: x \in 1..Upperbound}

generateConnectedDAG(S) == {
    x \in SUBSET (S \X S): 
        /\ ~\E y \in S: <<y, y>> \in x
        /\ ~\E y, z \in S: /\  <<y, z>> \in x 
                           /\  <<z, y>> \in x
        /\ \A y \in S: ~\E z \in S: /\ <<z, y>> \in x
                                    /\ z >= y
        /\ \/ Cardinality(S) = 1
           \/ \A y \in S: \E z \in S: \/ <<y, z>> \in x
                                      \/ <<z, y>> \in x
        /\ \/ x = {}
           \/ ~\E p1, p2 \in Paths(Cardinality(x), x): /\ p1 # p2
                                                       /\ p1[1] = p2[1]
                                                       /\ p2[Len(p2)] = p1[Len(p1)]
        /\ Cardinality(x) >= Cardinality(S) - 1                                                                                                                        
        /\  \/ x = {}
            \/ \A p \in Paths(Cardinality(x), x): \/ Len(p) = 1
                                                  \/ p[1] # p[Len(p)]
}

====================================================================

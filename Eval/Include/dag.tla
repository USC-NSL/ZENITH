---------------------------- MODULE dag ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(***********************************************************************)
(* This file contains definitions used to create dependency graphs for *)
(* IRs. These are always in the form of a directed, acycilic graph.    *)
(***********************************************************************)

min(set) == CHOOSE x \in set: \A y \in set: x \leq y

(************************************************************************)
(* Get paths of a given length `n` within a graph with set of nodes `G` *)
(************************************************************************)
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

(*********************************************************************)
(* Generate the set of all connected DAGs with elements from set `S` *)
(*********************************************************************)
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

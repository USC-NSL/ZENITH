---------------------------- MODULE dag ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(***********************************************************************)
(* This file contains definitions used to create dependency graphs for *)
(* IRs. These are always in the form of a directed, acycilic graph.    *)
(***********************************************************************)

min(set) == CHOOSE x \in set: \A y \in set: x \leq y

(************************************************************************)
(* Get paths of a given length `n` within a graph with set of edges `G` *)
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
(* Note that number of DAGs of size `n` is super-exponential in `n`, *)
(* this operator will explode if `S` is big enough.                  *)
(*********************************************************************)
IsDAG(nodeSet, edgeSet) == 
    /\ ~\E y \in nodeSet: <<y, y>> \in edgeSet \* No self-loops
    /\ ~\E y, z \in nodeSet: /\  <<y, z>> \in edgeSet  \* No bidirectional edges
                             /\  <<z, y>> \in edgeSet
    /\ \A y \in nodeSet: ~\E z \in nodeSet: /\ <<z, y>> \in edgeSet \* A small optimization ...
                                            /\ z >= y
    /\ \/ Cardinality(nodeSet) = 1 \* Is a connected graph
       \/ \A y \in nodeSet: \E z \in nodeSet: \/ <<y, z>> \in edgeSet
                                              \/ <<z, y>> \in edgeSet
    /\ \/ edgeSet = {} \* 
       \/ ~\E p1, p2 \in Paths(Cardinality(edgeSet), edgeSet): /\ p1 # p2
                                                               /\ p1[1] = p2[1]
                                                               /\ p2[Len(p2)] = p1[Len(p1)]
    /\ Cardinality(edgeSet) >= Cardinality(nodeSet) - 1                                                                                                                        
    /\ \/ edgeSet = {}
       \/ \A p \in Paths(Cardinality(edgeSet), edgeSet): \/ Len(p) = 1
                                                         \/ p[1] # p[Len(p)]

generateConnectedDAG(S) == {edgeSet \in SUBSET (S \X S): IsDAG(S, edgeSet)}

RECURSIVE _GetSimpleDAGRootEdges(_, _, _, _)
_GetSimpleDAGRootEdges(width, shift, nodeSet, edgeSet) ==
    IF Cardinality(nodeSet) = width + 1
        THEN edgeSet
        ELSE _GetSimpleDAGRootEdges(width, shift, nodeSet \cup {Cardinality(nodeSet) + shift + 1}, edgeSet \cup {<<1 + shift, Cardinality(nodeSet) + shift + 1>>})
GetSimpleDAGRootEdges(width, shift) == _GetSimpleDAGRootEdges(width, shift, {1}, {})

RECURSIVE _GetSimpleDAGDepthEdges(_, _, _, _, _)
_GetSimpleDAGDepthEdges(width, shift, currentDepth, index, edgeSet) ==
    IF index = width+1
        THEN edgeSet
        ELSE LET nextNode == (1 + (currentDepth-1) * width) + index + shift
                 nextEdge == <<(nextNode - width), nextNode>>
             IN _GetSimpleDAGDepthEdges(width, shift, currentDepth, index + 1, edgeSet \cup {nextEdge})
GetSimpleDAGDepthEdges(width, shift, currentDepth) == _GetSimpleDAGDepthEdges(width, shift, currentDepth, 1, {})

RECURSIVE _SimpleDAG(_, _, _, _, _, _)
_SimpleDAG(depth, width, shift, nodeSet, edgeSet, currentDepth) ==
    IF currentDepth = depth + 1
        THEN [v |-> nodeSet, e |-> edgeSet]
        ELSE LET nextNodes == (2 + (currentDepth-1) * width + shift)..(1 + (currentDepth) * width + shift)
             IN IF currentDepth = 1
                THEN _SimpleDAG(depth, width, shift, nodeSet \cup nextNodes, GetSimpleDAGRootEdges(width, shift), 2)
                ELSE _SimpleDAG(depth, width, shift, nodeSet \cup nextNodes, edgeSet \cup GetSimpleDAGDepthEdges(width, shift, currentDepth), currentDepth + 1)
SimpleDAG(depth, width, shift) == _SimpleDAG(depth, width, shift, {shift + 1}, {}, 1)

====================================================================

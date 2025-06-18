---- MODULE graph ----
EXTENDS TLC, Integers, FiniteSets, Sequences


\* `TRUE` if `edgeSet` is a set of pairs, each element in `nodeSet`
IsSetOfEdges(edgeSet, nodeSet) == edgeSet \in SUBSET (nodeSet \X nodeSet)

\* Get set of nodes that have incoming edges from a given node
OutgoingEdges(node, edgeSet) == {e \in edgeSet: e[1] = node}

\* Get set of nodes that we can hop to from end of a path without creating a cycle
PathNextHops(path, nodeSet, edgeSet) == {n \in nodeSet: /\ <<path[Len(path)], n>> \in edgeSet
                                                        /\ ~\E x \in DOMAIN path: path[x] = n}

\* Extend an existing path without creating a cycle
RECURSIVE _ExtendPath(_, _, _)
_ExtendPath(path, nextHops, newPaths) ==
    IF Cardinality(nextHops) = 0
        THEN newPaths
        ELSE LET nextHop == CHOOSE x \in nextHops: TRUE
             IN _ExtendPath(path, nextHops \ {nextHop}, newPaths \cup {path \o <<nextHop>>})
ExtendPath(path, nodeSet, edgeSet) ==
    LET nextHops == PathNextHops(path, nodeSet, edgeSet)
    IN _ExtendPath(path, nextHops, {})

\* Extend a set of existing paths of the same length without creating a cycle
RECURSIVE _NextLengthPaths(_, _, _, _)
_NextLengthPaths(paths, nodeSet, edgeSet, nextPaths) ==
    IF Cardinality(paths) = 0
        THEN nextPaths
        ELSE LET currentPath == CHOOSE path \in paths: TRUE
             IN _NextLengthPaths(paths \ {currentPath}, nodeSet, edgeSet, nextPaths \cup ExtendPath(currentPath, nodeSet, edgeSet))
NextLengthPaths(paths, nodeSet, edgeSet) == _NextLengthPaths(paths, nodeSet, edgeSet, {})
    
\* Get set of shortest paths between a `start` and `finish` node in a graph over set of
\* nodes `nodeSet` with edge set `edgeSet`.
\* Another operator returns paths between any two members of a given set
RECURSIVE _ShortestPathsBetween(_, _, _, _, _)
_ShortestPathsBetween(start, finish, nodeSet, edgeSet, paths) ==
    LET completedPaths == {p \in paths: p[Len(p)] = finish}
    IN IF Cardinality(completedPaths) > 0
        THEN completedPaths
        ELSE LET nextPaths == NextLengthPaths(paths, nodeSet, edgeSet)
             IN _ShortestPathsBetween(start, finish, nodeSet, edgeSet, nextPaths)
ShortestPathsBetween(start, finish, nodeSet, edgeSet) ==
    LET lengthOnePaths == OutgoingEdges(start, edgeSet)
    IN _ShortestPathsBetween(start, finish, nodeSet, edgeSet, lengthOnePaths)

RECURSIVE _ShortestPathsFrom(_, _, _, _, _)
_ShortestPathsFrom(start, finishSet, nodeSet, edgeSet, paths) ==
    IF Cardinality(finishSet) = 0
        THEN paths
        ELSE LET 
                currentFinish == CHOOSE x \in finishSet: TRUE
                currentPathsToFinish == ShortestPathsBetween(start, currentFinish, nodeSet, edgeSet)
             IN _ShortestPathsFrom(start, finishSet \ {currentFinish}, nodeSet, edgeSet, paths \cup currentPathsToFinish)
ShortestPathsFrom(start, finishSet, nodeSet, edgeSet) ==
    _ShortestPathsFrom(start, finishSet \ {start}, nodeSet, edgeSet, {})

RECURSIVE _ShortestPaths(_, _, _, _, _)
_ShortestPaths(startSet, finishSet, nodeSet, edgeSet, paths) ==
    IF Cardinality(startSet) = 0
        THEN paths
        ELSE LET 
                currentStart == CHOOSE x \in startSet: TRUE
                currentPaths == ShortestPathsFrom(currentStart, finishSet, nodeSet, edgeSet)
             IN _ShortestPaths(startSet \ {currentStart}, finishSet, nodeSet, edgeSet, paths \cup currentPaths)
ShortestPaths(endpoints, nodeSet, edgeSet) == 
    _ShortestPaths(endpoints, endpoints, nodeSet, edgeSet, {})

\* Given a set of edges, pick only edges that never cross a particular node, as if
\* they belong to a graph that does not have that node.
RemoveNodeFromEdgeSet(nodeToRemove, edgeSet) == {e \in edgeSet: /\ e[1] # nodeToRemove
                                                                /\ e[2] # nodeToRemove}
RECURSIVE RemoveNodesFromGraph(_, _)
RemoveNodesFromGraph(nodeSetToRemove, edgeSet) ==
    IF Cardinality(nodeSetToRemove) = 0
        THEN edgeSet
        ELSE LET currentNode == CHOOSE x \in nodeSetToRemove: TRUE
             IN RemoveNodesFromGraph(nodeSetToRemove \ {currentNode}, RemoveNodeFromEdgeSet(currentNode, edgeSet))

\* \* Given a set, convert it to a list
\* RECURSIVE _ListOfPaths(_, _, _)
\* _ListOfPaths(pathSet, somePath, index) ==
\*     IF Cardinality(pathSet) = 0
\*         THEN somePath
\*         ELSE LET someElement == CHOOSE e \in pathSet: TRUE
\*              IN _ListOfPaths(pathSet \ {someElement}, somePath @@ (index :> someElement), index+1)
\* ListOfPaths(pathSet) ==
\*     LET startElement == CHOOSE e \in pathSet: TRUE
\*     IN _ListOfPaths(pathSet \ {startElement}, (1 :> startElement), 2)
    
\* \* Given a list of paths, get the mapping from index to path with a shift
\* RECURSIVE _PathMapReverse(_, _, _, _)
\* _PathMapReverse(pathList, indices, shift, reverseMap) ==
\*     IF Cardinality(indices) = 0
\*         THEN reverseMap
\*         ELSE LET nextIndex == CHOOSE x \in indices: TRUE
\*              IN _PathMapReverse(pathList, indices \ {nextIndex}, shift, reverseMap @@ ((nextIndex + shift) :> pathList[nextIndex]))
\* PathMapReverse(pathList, shift) ==
\*     LET
\*         indexSet == DOMAIN pathList
\*         firstIndex == CHOOSE x \in indexSet: TRUE
\*     IN
\*         _PathMapReverse(pathList, indexSet \ {firstIndex}, shift, ((shift + firstIndex) :> pathList[firstIndex]))

\* Generate IRs for the current path (or set of paths) at a given priority
\* while also creating a reversed chain for the DAG.
\* It traverses the paths in _reverse_ order to build the DAG concurrently.
RECURSIVE _GeneratePathIRs(_, _, _, _, _, _, _) 
_GeneratePathIRs(path, startingIR, index, priority, irSet, edgeSet, nodeSet) ==
    IF index = Cardinality(DOMAIN path)
        THEN [irs |-> irSet, edges |-> edgeSet, nodes |-> nodeSet]
        ELSE LET 
                newIRIndex == startingIR + index
                pathIndex == Len(path) - index + 1
                newIRObject == [sw |-> path[pathIndex], ir |-> newIRIndex, priority |-> priority]
                newDagEdge == IF index = 1
                                THEN <<>>
                                ELSE <<newIRIndex-1, newIRIndex>>
             IN IF Len(newDagEdge) = 0
                    THEN
                        _GeneratePathIRs(
                                path, startingIR, index+1, priority, 
                                irSet \cup {newIRObject}, 
                                edgeSet, 
                                nodeSet \cup {newIRIndex})
                    ELSE
                        _GeneratePathIRs(
                                path, startingIR, index+1, priority, 
                                irSet \cup {newIRObject}, 
                                edgeSet \cup {newDagEdge},
                                nodeSet \cup {newIRIndex})
GeneratePathIRs(path, startingIR, priority) == _GeneratePathIRs(path, startingIR, 1, priority, {}, {}, {})

RECURSIVE _GeneratePathSetIRs(_, _, _, _, _, _)
_GeneratePathSetIRs(pathSet, startingIR, priority, irSet, edgeSet, nodeSet) ==
    IF Cardinality(pathSet) = 0
        THEN [irs |-> irSet, edges |-> edgeSet, nodes |-> nodeSet]
        ELSE LET 
                nextPath == CHOOSE x \in pathSet: TRUE
                nextPathIRsAndDAG == GeneratePathIRs(nextPath, startingIR, priority)
             IN _GeneratePathSetIRs(
                    pathSet \ {nextPath}, 
                    startingIR + Cardinality(nextPathIRsAndDAG.irs), 
                    priority, 
                    irSet \cup nextPathIRsAndDAG.irs, 
                    edgeSet \cup nextPathIRsAndDAG.edges,
                    nodeSet \cup nextPathIRsAndDAG.nodes)
GeneratePathSetIRs(pathSet, startingIR, priority) == _GeneratePathSetIRs(pathSet, startingIR, priority, {}, {}, {})

\* A swiss knife operator that generates everything the drain application needs to know
GenerateDrainApplicationData(NodeSet, EdgeSet, NodeToDrain, Endpoints) ==
    LET 
        drainedNodeSet == NodeSet \ {NodeToDrain}
        drainedEdgeSet == RemoveNodeFromEdgeSet(NodeToDrain, EdgeSet)
        originalPaths == ShortestPaths(Endpoints, NodeSet, EdgeSet)
        drainedPaths == ShortestPaths(Endpoints \ {NodeToDrain}, drainedNodeSet, drainedEdgeSet)
        originalIRs == GeneratePathSetIRs(originalPaths, 0, 1)
        numberOfOriginalIRs == Cardinality(originalIRs.nodes)
        drainedIRs == GeneratePathSetIRs(drainedPaths, numberOfOriginalIRs, 10)
    IN
        [
            OriginalPaths |-> originalPaths,
            DrainedPaths |-> drainedPaths,
            OriginalIRs |-> originalIRs,
            DrainedIRs |-> drainedIRs,
            TotalNumberOfIRs |-> (Cardinality(originalIRs.nodes) + Cardinality(drainedIRs.nodes))
        ]

\* Get children of a node
NodeChildren(nodeSet, edgeSet, node) == {n \in (nodeSet \ {node}): <<node, n>> \in edgeSet}
\* Get children of a set of nodes
RECURSIVE _NodeSetChildren(_, _, _, _)
_NodeSetChildren(nodeSet, edgeSet, parentSet, childrenSet) ==
    IF Cardinality(parentSet) = 0
        THEN childrenSet
        ELSE LET 
                parent == CHOOSE parent \in parentSet: TRUE
                newChildren == NodeChildren(nodeSet, edgeSet, parent)
                newParentSet == parentSet \ {parent}
             IN _NodeSetChildren(nodeSet, edgeSet, newParentSet, childrenSet \cup newChildren)
NodeSetChildren(nodeSet, edgeSet, parentSet) == _NodeSetChildren(nodeSet, edgeSet, parentSet, {})

\* Get the root(s) of a DAG, the set of all nodes with no parents
GetDAGRoot(nodeSet, edgeSet) == {node \in nodeSet: \A x \in (nodeSet \ {node}): <<x, node>> \notin edgeSet}
\* Get the leaves of a DAG, the set of all nodes with no children
GetDAGLeaves(nodeSet, edgeSet) == {node \in nodeSet: \A x \in (nodeSet \ {node}): <<node, x>> \notin edgeSet}

\* Do BFS on a DAG (useful for abstract core)
RECURSIVE _GetDAGLevels(_, _, _, _)
_GetDAGLevels(nodeSet, edgeSet, currentLevel, levels) ==
    LET nextLevel == NodeSetChildren(nodeSet, edgeSet, currentLevel)
    IN IF Cardinality(nextLevel) = 0
        THEN levels
        ELSE _GetDAGLevels(nodeSet, edgeSet, nextLevel, levels \o <<nextLevel>>)
GetDAGLevels(nodeSet, edgeSet) ==
    LET 
        roots == GetDAGRoot(nodeSet, edgeSet)
        levels == <<roots>>
    IN _GetDAGLevels(nodeSet, edgeSet, roots, levels)

\* A utility that adds a whole level to a DAG (i.e. the new nodes will have the whole previous DAG
\* as their dependency)
RECURSIVE AddDependentNodeToDAG(_, _, _)
AddDependentNodeToDAG(dag, leaves, newNode) ==
    IF Cardinality(leaves) = 0
        THEN [v |-> dag.v \cup {newNode}, e |-> dag.e]
        ELSE LET currentLeaf == CHOOSE x \in leaves: TRUE
             IN AddDependentNodeToDAG(
                [v |-> dag.v, e |-> dag.e \cup {<<currentLeaf, newNode>>}], 
                leaves \ {currentLeaf}, 
                newNode)

RECURSIVE _ExpandDAG(_, _, _)
_ExpandDAG(dag, leaves, newNodes) ==
    IF Cardinality(newNodes) = 0
        THEN dag
        ELSE LET currentNode == CHOOSE x \in newNodes: TRUE
             IN _ExpandDAG(AddDependentNodeToDAG(dag, leaves, currentNode), leaves, newNodes \ {currentNode})

ExpandDAG(dag, newNodes) ==
    LET leaves == GetDAGLeaves(dag.v, dag.e)
    IN _ExpandDAG(dag, leaves, newNodes)

RECURSIVE _SetToSeq(_, _)
_SetToSeq(someSet, seq) ==
    IF Cardinality(someSet) = 0
        THEN seq
        ELSE LET currentElement == CHOOSE x \in someSet: TRUE
             IN _SetToSeq(someSet \ {currentElement}, seq \o <<currentElement>>)
SetToSeq(someSet) == _SetToSeq(someSet, <<>>)

RECURSIVE _BFS(_, _)
_BFS(levels, list) ==
    IF Len(levels) = 0
        THEN list
        ELSE _BFS(Tail(levels), list \o <<SetToSeq(Head(levels))>>)
DAGBFS(nodeSet, edgeSet) == 
    LET levels == GetDAGLevels(nodeSet, edgeSet)
    IN _BFS(levels, <<>>)

\* VARIABLES NodeSet, EdgeSet, NodeToDrain

\* Init == /\ NodeSet = 1..45
\*         /\ EdgeSet = {
\*             <<1, 10>>, <<10, 1>>, <<2, 10>>, <<10, 2>>, <<3, 10>>, <<10, 3>>, <<4, 11>>, <<11, 4>>, <<5, 11>>, <<11, 5>>, <<6, 11>>, <<11, 6>>, <<7, 12>>, <<12, 7>>, <<8, 12>>, <<12, 8>>,
\*             <<9, 12>>, <<12, 9>>, <<1, 13>>, <<13, 1>>, <<2, 13>>, <<13, 2>>, <<3, 13>>, <<13, 3>>, <<4, 14>>, <<14, 4>>, <<5, 14>>, <<14, 5>>, <<6, 14>>, <<14, 6>>, <<7, 15>>, <<15, 7>>,
\*             <<8, 15>>, <<15, 8>>, <<9, 15>>, <<15, 9>>, <<1, 16>>, <<16, 1>>, <<2, 16>>, <<16, 2>>, <<3, 16>>, <<16, 3>>, <<4, 17>>, <<17, 4>>, <<5, 17>>, <<17, 5>>, <<6, 17>>, <<17, 6>>,
\*             <<7, 18>>, <<18, 7>>, <<8, 18>>, <<18, 8>>, <<9, 18>>, <<18, 9>>, <<1, 19>>, <<19, 1>>, <<2, 19>>, <<19, 2>>, <<3, 19>>, <<19, 3>>, <<4, 20>>, <<20, 4>>, <<5, 20>>, <<20, 5>>,
\*             <<6, 20>>, <<20, 6>>, <<7, 21>>, <<21, 7>>, <<8, 21>>, <<21, 8>>, <<9, 21>>, <<21, 9>>, <<1, 22>>, <<22, 1>>, <<2, 22>>, <<22, 2>>, <<3, 22>>, <<22, 3>>, <<4, 23>>, <<23, 4>>,
\*             <<5, 23>>, <<23, 5>>, <<6, 23>>, <<23, 6>>, <<7, 24>>, <<24, 7>>, <<8, 24>>, <<24, 8>>, <<9, 24>>, <<24, 9>>, <<1, 25>>, <<25, 1>>, <<2, 25>>, <<25, 2>>, <<3, 25>>, <<25, 3>>,
\*             <<4, 26>>, <<26, 4>>, <<5, 26>>, <<26, 5>>, <<6, 26>>, <<26, 6>>, <<7, 27>>, <<27, 7>>, <<8, 27>>, <<27, 8>>, <<9, 27>>, <<27, 9>>, <<10, 28>>, <<28, 10>>, <<10, 29>>, <<29, 10>>,
\*             <<10, 30>>, <<30, 10>>, <<11, 28>>, <<28, 11>>, <<11, 29>>, <<29, 11>>, <<11, 30>>, <<30, 11>>, <<12, 28>>, <<28, 12>>, <<12, 29>>, <<29, 12>>, <<12, 30>>, <<30, 12>>, <<13, 31>>, <<31, 13>>,
\*             <<13, 32>>, <<32, 13>>, <<13, 33>>, <<33, 13>>, <<14, 31>>, <<31, 14>>, <<14, 32>>, <<32, 14>>, <<14, 33>>, <<33, 14>>, <<15, 31>>, <<31, 15>>, <<15, 32>>, <<32, 15>>, <<15, 33>>, <<33, 15>>,
\*             <<16, 34>>, <<34, 16>>, <<16, 35>>, <<35, 16>>, <<16, 36>>, <<36, 16>>, <<17, 34>>, <<34, 17>>, <<17, 35>>, <<35, 17>>, <<17, 36>>, <<36, 17>>, <<18, 34>>, <<34, 18>>, <<18, 35>>, <<35, 18>>,
\*             <<18, 36>>, <<36, 18>>, <<19, 37>>, <<37, 19>>, <<19, 38>>, <<38, 19>>, <<19, 39>>, <<39, 19>>, <<20, 37>>, <<37, 20>>, <<20, 38>>, <<38, 20>>, <<20, 39>>, <<39, 20>>, <<21, 37>>, <<37, 21>>,
\*             <<21, 38>>, <<38, 21>>, <<21, 39>>, <<39, 21>>, <<22, 40>>, <<40, 22>>, <<22, 41>>, <<41, 22>>, <<22, 42>>, <<42, 22>>, <<23, 40>>, <<40, 23>>, <<23, 41>>, <<41, 23>>, <<23, 42>>, <<42, 23>>,
\*             <<24, 40>>, <<40, 24>>, <<24, 41>>, <<41, 24>>, <<24, 42>>, <<42, 24>>, <<25, 43>>, <<43, 25>>, <<25, 44>>, <<44, 25>>, <<25, 45>>, <<45, 25>>, <<26, 43>>, <<43, 26>>, <<26, 44>>, <<44, 26>>,
\*             <<26, 45>>, <<45, 26>>, <<27, 43>>, <<43, 27>>, <<27, 44>>, <<44, 27>>, <<27, 45>>, <<45, 27>>
\*             }
\*         /\ NodeToDrain = 10

\* Init == /\ NodeSet = 1..9
\*         /\ EdgeSet = {
\*                 <<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>, <<4, 5>>, <<5, 6>>,
\*                 <<3, 7>>, <<7, 8>>, <<8, 9>>, <<9, 6>>,
\*                 <<2, 1>>, <<3, 1>>, <<4, 2>>, <<4, 3>>, <<5, 4>>, <<6, 5>>,
\*                 <<7, 3>>, <<8, 7>>, <<9, 8>>, <<6, 9>>
\*             }
\*         /\ NodeToDrain = 4

\* Init == /\ NodeSet = 1..7
\*         /\ EdgeSet = {
\*                 <<1, 4>>, <<2, 5>>, <<5, 7>>, <<3, 6>>
\*             }
\*         /\ NodeToDrain = 4

\* Next == /\ NodeSet' = (NodeSet \ {NodeToDrain})
\*         /\ EdgeSet' = RemoveNodeFromEdgeSet(NodeToDrain, EdgeSet)
\*         /\ UNCHANGED <<NodeToDrain>>
\* Next == UNCHANGED <<NodeToDrain, NodeSet, EdgeSet>>
        
\* vars == <<NodeSet, EdgeSet, NodeToDrain>>

\* Spec == Init /\ [][Next]_vars
\* Inv == PrintT(DAGBFS(NodeSet, EdgeSet))
\* Inv == PrintT(GenerateDrainApplicationData(
\*         NodeSet, EdgeSet, NodeToDrain, 
\*         {1, 6}
\*     ))
\* Inv == LET res == GenerateDrainApplicationData(NodeSet, EdgeSet, NodeToDrain, {1, 6})
\*        IN PrintT(ExpandDAG([v |-> res.DrainedIRs.nodes, e |-> res.DrainedIRs.edges], res.OriginalIRs.nodes))
            
\* Inv == PrintT(GenerateDrainApplicationData(
\*         NodeSet, EdgeSet, NodeToDrain, 
\*         {28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45}
\*     ))
\* Inv == LET 
\*             setOfPaths == ShortestPaths({1, 6}, NodeSet, EdgeSet)
\*             pathSetIRs == GeneratePathSetIRs(setOfPaths, 10, 2)
\*        IN /\ PrintT(setOfPaths)
\*           /\ PrintT(pathSetIRs)
\* Inv == LET 
\*             setOfPaths == ShortestPathsBetween(1, 6, NodeSet, EdgeSet)
\*             pathSetIRs == GeneratePathSetIRs(setOfPaths, 10, 2)
\*        IN /\ PrintT(setOfPaths)
\*           /\ PrintT(pathSetIRs)
\* Inv == LET 
\*             setOfPaths == ShortestPathsBetween(1, 6, NodeSet, EdgeSet)
\*             listOfPaths == ListOfPaths(setOfPaths)
\*        IN /\ PrintT(listOfPaths)
\*           /\ PrintT(PathMapReverse(listOfPaths, 10))


====
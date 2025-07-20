---- MODULE drain ----
EXTENDS Integers, Sequences, FiniteSets, TLC, NadirTypes, graph

CONSTANTS SW, MaxNumIRs

(* Constants to uniquely identify this process *)
CONSTANTS app0, DRAIN_APP

(*--fair algorithm drainApplication
    variables
        \* ---- CORE GLOBAL VARIABLES ----
        \* Queue of DAGs from applications to the controller
        DAGEventQueue = <<>>,

        \* ---- APPLICATION GLOBAL VARIABLES ----
        \* This is the queue of drain requests.
        \* A drain request has 4 parts:
        \*  - The current topology (i.e. set of running switches and links)
        \*  - The set of paths active in the network (i.e. current routing configuration in the network)
        \*  - The set of IRs that implement the paths in the previous set
        \*  - The node index to drain
        DrainRequestQueue = <<>>
    
    define
        RECURSIVE _getPathSetEndpoints(_, _)
        _getPathSetEndpoints(pathSet, endpoints) ==
            IF Cardinality(pathSet) = 0
                THEN endpoints
                ELSE LET currentPath == CHOOSE x \in pathSet: TRUE
                     IN _getPathSetEndpoints(pathSet \ {currentPath}, endpoints \cup {currentPath[Len(currentPath)]})
        getPathSetEndpoints(pathSet) == _getPathSetEndpoints(pathSet, {})

        RECURSIVE _HighestPriorityInIRSet(_, _)
        _HighestPriorityInIRSet(setOfIRObjects, priority) ==
            IF Cardinality(setOfIRObjects) = 0
                THEN priority
                ELSE LET currentIRObject == CHOOSE x \in setOfIRObjects: TRUE
                         currentPriority == IF priority < currentIRObject.priority THEN currentIRObject.priority ELSE priority
                     IN _HighestPriorityInIRSet(setOfIRObjects \ {currentIRObject}, currentPriority)
        HighestPriorityInIRSet(setOfIRObjects) == _HighestPriorityInIRSet(setOfIRObjects, 0)

        RECURSIVE _GetDeletionIRs(_, _)
        _GetDeletionIRs(setOfIRs, deleterSet) ==
            IF Cardinality(setOfIRs) = 0
                THEN deleterSet
                ELSE LET currentIR == CHOOSE x \in setOfIRs: TRUE
                     IN _GetDeletionIRs(setOfIRs \ {currentIR}, deleterSet \cup {currentIR.ir + MaxNumIRs})
        
        GetDeletionIRs(setOfIRs) == _GetDeletionIRs(setOfIRs, {})
    end define;

    \* These macros are reserved by Nadir. They signal queue operations ...
    macro NadirFIFOPut(queue, object)
    begin
        queue := Append(queue, object);
    end macro;
    macro NadirFIFOGet(queue, message)
    begin
        await Len(queue) > 0;
        message := Head(queue);
        queue := Tail(queue);
    end macro;

    macro InspectDrainRequest(request, topo, path, node, irs) begin
        \* Messages on queues are usually functions from strings to arbitrary
        \* TLA+ values. In practice, they would look like C structs.
        topo := request.topology;
        path := request.paths;
        node := request.node;
        irs := request.irs;
    end macro;

    \* macro ComputeDrainedPathIRs(newPaths, previousIRs, newIRs, newDAG) begin
    \*     \* The new IRs MUST be installed with a higher priority than 
    \*     \* previous paths (otherwise, there is no way to guarantee the
    \*     \* drain is hitless). To do this, sift through previous IRs and
    \*     \* get the highest priority in it.
    \*     with res = GeneratePathSetIRs(newPaths, Cardinality(previousIRs), HighestPriorityInIRSet(previousIRs) + 1)  do
    \*         newIRs := res.irs;
    \*         newDAG := ExpandDAG([v |-> res.nodes, e |-> res.edges], res.OriginalIRs.nodes);
    \*     end with;
    \* end macro;

    \* \* Generate IRs for the current path (or set of paths) at a given priority
    \* \* while also creating a reversed chain for the DAG.
    \* \* It traverses the paths in _reverse_ order to build the DAG concurrently.
    \* RECURSIVE _GeneratePathIRs(_, _, _, _, _, _, _) 
    \* _GeneratePathIRs(path, startingIR, index, priority, irSet, edgeSet, nodeSet) ==
    \*     IF index = Cardinality(DOMAIN path)
    \*         THEN [irs |-> irSet, edges |-> edgeSet, nodes |-> nodeSet]
    \*         ELSE LET 
    \*                 newIRIndex == startingIR + index
    \*                 pathIndex == Len(path) - index + 1
    \*                 newIRObject == [sw |-> path[pathIndex], ir |-> newIRIndex, priority |-> priority]
    \*                 newDagEdge == IF index = 1
    \*                                 THEN <<>>
    \*                                 ELSE <<newIRIndex-1, newIRIndex>>
    \*             IN IF Len(newDagEdge) = 0
    \*                     THEN
    \*                         _GeneratePathIRs(
    \*                                 path, startingIR, index+1, priority, 
    \*                                 irSet \cup {newIRObject}, 
    \*                                 edgeSet, 
    \*                                 nodeSet \cup {newIRIndex})
    \*                     ELSE
    \*                         _GeneratePathIRs(
    \*                                 path, startingIR, index+1, priority, 
    \*                                 irSet \cup {newIRObject}, 
    \*                                 edgeSet \cup {newDagEdge},
    \*                                 nodeSet \cup {newIRIndex})
    \* GeneratePathIRs(path, startingIR, priority) == _GeneratePathIRs(path, startingIR, 1, priority, {}, {}, {})

    \* RECURSIVE _GeneratePathSetIRs(_, _, _, _, _, _)
    \* _GeneratePathSetIRs(pathSet, startingIR, priority, irSet, edgeSet, nodeSet) ==
    \*     IF Cardinality(pathSet) = 0
    \*         THEN [irs |-> irSet, edges |-> edgeSet, nodes |-> nodeSet]
    \*         ELSE LET 
    \*                 nextPath == CHOOSE x \in pathSet: TRUE
    \*                 nextPathIRsAndDAG == GeneratePathIRs(nextPath, startingIR, priority)
    \*             IN _GeneratePathSetIRs(
    \*                     pathSet \ {nextPath}, 
    \*                     startingIR + Cardinality(nextPathIRsAndDAG.irs), 
    \*                     priority, 
    \*                     irSet \cup nextPathIRsAndDAG.irs, 
    \*                     edgeSet \cup nextPathIRsAndDAG.edges,
    \*                     nodeSet \cup nextPathIRsAndDAG.nodes)
    \* GeneratePathSetIRs(pathSet, startingIR, priority) == _GeneratePathSetIRs(pathSet, startingIR, priority, {}, {}, {})

    procedure ComputeDrainedPathIRs(newPaths, previousIRs, newIRs, newDAG)
    variables nextPriority = NADIR_NULL, newIRsStartingIndex = NADIR_NULL, 
              newIRSet = {}, newDAGEdgeSet = {}, newDAGNodeSet = {}, 
              currentPath = NADIR_NULL, currentPathResult = {};
    begin
    ComputePriority:
        \* The new IRs MUST be installed with a higher priority than 
        \* previous paths (otherwise, there is no way to guarantee the
        \* drain is hitless). To do this, sift through previous IRs and
        \* get the highest priority in it.
        nextPriority := HighestPriorityInIRSet(previousIRs) + 1;
        \* Each hop in a new path will have a new IR associated with. Each
        \* IR needs an index, and so will start at the end of current IR list
        \* for indexing.
        newIRsStartingIndex := Cardinality(previousIRs);
    
    ComputeNewPathsDAG:
    while Cardinality(newPaths) > 0 do
        \* Pick one of the new paths
        currentPath := (CHOOSE p \in newPaths: TRUE);
        \* Compute the IRs and the ordering that implements the new path
        currentPathResult := GeneratePathIRs(currentPath, newIRsStartingIndex, nextPriority);
        \* Accumulate the result and remove the processed path from the set
        newIRSet := newIRSet \cup currentPathResult.irs;
        newDAGEdgeSet := newDAGEdgeSet \cup currentPathResult.edges;
        newDAGNodeSet := newDAGNodeSet \cup currentPathResult.nodes;
        newPaths := newPaths \ {currentPath};
    end while;
    
    CleanupPreviousIRs:
        \* To cleanup the previous IRs, add the deletion instruction for all the previous
        \* IRs at the end of the DAG (i.e. attach them to all the leaves of the DAG)
        newDAG := ExpandDAG([v |-> newDAGNodeSet, e |-> newDAGEdgeSet], GetDeletionIRs(previousIRs));
    end procedure;

    process drainer \in ({app0} \X {DRAIN_APP})
    variables 
        currentRequest = NADIR_NULL, currentTopology = NADIR_NULL, currentPaths = {}, nodeToDrain = NADIR_NULL, currentIRs = {}, 
        endpoints = {}, pathsAfterDrain = {}, drainPathSetIRs = {}, drainedDAG = {}, nextDAGID = 1;
    begin
    DrainLoop:
    while TRUE do
        \* (MACRO CALL) Wait until a new drain request comes in
        NadirFIFOGet(DrainRequestQueue, currentRequest);
        \* (MACRO CALL) Read the contents of the request
        InspectDrainRequest(currentRequest, currentTopology, currentPaths, nodeToDrain, currentIRs);
        ComputeDrain:
            \* First, get the set of endpoints that we need to keep connected during/after drain
            endpoints := getPathSetEndpoints(currentPaths) \ {nodeToDrain};
            \* Get all paths assuming the given node was removed from the topology
            pathsAfterDrain := ShortestPaths(
                endpoints, 
                (currentTopology.Nodes \ {nodeToDrain}), 
                RemoveNodeFromEdgeSet(nodeToDrain, currentTopology.Edges));
            \* (PROCEDURE CALL) Compute the new DAG and IRs that implement the paths
            call ComputeDrainedPathIRs(pathsAfterDrain, currentIRs, drainPathSetIRs, drainedDAG);
        SubmitDAG:
            \* (MACRO CALL) Generate an ID for this DAG and send it to the core
            NadirFIFOPut(DAGEventQueue, [id |-> nextDAGID, dag |-> drainedDAG]);
            nextDAGID := nextDAGID + 1;
    end while;
    end process;
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "d092d3c2" /\ chksum(tla) = "276483c")
CONSTANT defaultInitValue
VARIABLES DAGEventQueue, DrainRequestQueue, pc, stack

(* define statement *)
RECURSIVE _getPathSetEndpoints(_, _)
_getPathSetEndpoints(pathSet, endpoints) ==
    IF Cardinality(pathSet) = 0
        THEN endpoints
        ELSE LET currentPath == CHOOSE x \in pathSet: TRUE
             IN _getPathSetEndpoints(pathSet \ {currentPath}, endpoints \cup {currentPath[Len(currentPath)]})
getPathSetEndpoints(pathSet) == _getPathSetEndpoints(pathSet, {})

RECURSIVE _HighestPriorityInIRSet(_, _)
_HighestPriorityInIRSet(setOfIRObjects, priority) ==
    IF Cardinality(setOfIRObjects) = 0
        THEN priority
        ELSE LET currentIRObject == CHOOSE x \in setOfIRObjects: TRUE
                 currentPriority == IF priority < currentIRObject.priority THEN currentIRObject.priority ELSE priority
             IN _HighestPriorityInIRSet(setOfIRObjects \ {currentIRObject}, currentPriority)
HighestPriorityInIRSet(setOfIRObjects) == _HighestPriorityInIRSet(setOfIRObjects, 0)

RECURSIVE _GetDeletionIRs(_, _)
_GetDeletionIRs(setOfIRs, deleterSet) ==
    IF Cardinality(setOfIRs) = 0
        THEN deleterSet
        ELSE LET currentIR == CHOOSE x \in setOfIRs: TRUE
             IN _GetDeletionIRs(setOfIRs \ {currentIR}, deleterSet \cup {currentIR.ir + MaxNumIRs})

GetDeletionIRs(setOfIRs) == _GetDeletionIRs(setOfIRs, {})

VARIABLES newPaths, previousIRs, newIRs, newDAG, nextPriority, 
          newIRsStartingIndex, newIRSet, newDAGEdgeSet, newDAGNodeSet, 
          currentPath, currentPathResult, currentRequest, currentTopology, 
          currentPaths, nodeToDrain, currentIRs, endpoints, pathsAfterDrain, 
          drainPathSetIRs, drainedDAG, nextDAGID

vars == << DAGEventQueue, DrainRequestQueue, pc, stack, newPaths, previousIRs, 
           newIRs, newDAG, nextPriority, newIRsStartingIndex, newIRSet, 
           newDAGEdgeSet, newDAGNodeSet, currentPath, currentPathResult, 
           currentRequest, currentTopology, currentPaths, nodeToDrain, 
           currentIRs, endpoints, pathsAfterDrain, drainPathSetIRs, 
           drainedDAG, nextDAGID >>

ProcSet == (({app0} \X {DRAIN_APP}))

Init == (* Global variables *)
        /\ DAGEventQueue = <<>>
        /\ DrainRequestQueue = <<>>
        (* Procedure ComputeDrainedPathIRs *)
        /\ newPaths = [ self \in ProcSet |-> defaultInitValue]
        /\ previousIRs = [ self \in ProcSet |-> defaultInitValue]
        /\ newIRs = [ self \in ProcSet |-> defaultInitValue]
        /\ newDAG = [ self \in ProcSet |-> defaultInitValue]
        /\ nextPriority = [ self \in ProcSet |-> NADIR_NULL]
        /\ newIRsStartingIndex = [ self \in ProcSet |-> NADIR_NULL]
        /\ newIRSet = [ self \in ProcSet |-> {}]
        /\ newDAGEdgeSet = [ self \in ProcSet |-> {}]
        /\ newDAGNodeSet = [ self \in ProcSet |-> {}]
        /\ currentPath = [ self \in ProcSet |-> NADIR_NULL]
        /\ currentPathResult = [ self \in ProcSet |-> {}]
        (* Process drainer *)
        /\ currentRequest = [self \in ({app0} \X {DRAIN_APP}) |-> NADIR_NULL]
        /\ currentTopology = [self \in ({app0} \X {DRAIN_APP}) |-> NADIR_NULL]
        /\ currentPaths = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ nodeToDrain = [self \in ({app0} \X {DRAIN_APP}) |-> NADIR_NULL]
        /\ currentIRs = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ endpoints = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ pathsAfterDrain = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ drainPathSetIRs = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ drainedDAG = [self \in ({app0} \X {DRAIN_APP}) |-> {}]
        /\ nextDAGID = [self \in ({app0} \X {DRAIN_APP}) |-> 1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "DrainLoop"]

ComputePriority(self) == /\ pc[self] = "ComputePriority"
                         /\ nextPriority' = [nextPriority EXCEPT ![self] = HighestPriorityInIRSet(previousIRs[self]) + 1]
                         /\ newIRsStartingIndex' = [newIRsStartingIndex EXCEPT ![self] = Cardinality(previousIRs[self])]
                         /\ pc' = [pc EXCEPT ![self] = "ComputeNewPathsDAG"]
                         /\ UNCHANGED << DAGEventQueue, DrainRequestQueue, 
                                         stack, newPaths, previousIRs, newIRs, 
                                         newDAG, newIRSet, newDAGEdgeSet, 
                                         newDAGNodeSet, currentPath, 
                                         currentPathResult, currentRequest, 
                                         currentTopology, currentPaths, 
                                         nodeToDrain, currentIRs, endpoints, 
                                         pathsAfterDrain, drainPathSetIRs, 
                                         drainedDAG, nextDAGID >>

ComputeNewPathsDAG(self) == /\ pc[self] = "ComputeNewPathsDAG"
                            /\ IF Cardinality(newPaths[self]) > 0
                                  THEN /\ currentPath' = [currentPath EXCEPT ![self] = (CHOOSE p \in newPaths[self]: TRUE)]
                                       /\ currentPathResult' = [currentPathResult EXCEPT ![self] = GeneratePathIRs(currentPath'[self], newIRsStartingIndex[self], nextPriority[self])]
                                       /\ newIRSet' = [newIRSet EXCEPT ![self] = newIRSet[self] \cup currentPathResult'[self].irs]
                                       /\ newDAGEdgeSet' = [newDAGEdgeSet EXCEPT ![self] = newDAGEdgeSet[self] \cup currentPathResult'[self].edges]
                                       /\ newDAGNodeSet' = [newDAGNodeSet EXCEPT ![self] = newDAGNodeSet[self] \cup currentPathResult'[self].nodes]
                                       /\ newPaths' = [newPaths EXCEPT ![self] = newPaths[self] \ {currentPath'[self]}]
                                       /\ pc' = [pc EXCEPT ![self] = "ComputeNewPathsDAG"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "CleanupPreviousIRs"]
                                       /\ UNCHANGED << newPaths, newIRSet, 
                                                       newDAGEdgeSet, 
                                                       newDAGNodeSet, 
                                                       currentPath, 
                                                       currentPathResult >>
                            /\ UNCHANGED << DAGEventQueue, DrainRequestQueue, 
                                            stack, previousIRs, newIRs, newDAG, 
                                            nextPriority, newIRsStartingIndex, 
                                            currentRequest, currentTopology, 
                                            currentPaths, nodeToDrain, 
                                            currentIRs, endpoints, 
                                            pathsAfterDrain, drainPathSetIRs, 
                                            drainedDAG, nextDAGID >>

CleanupPreviousIRs(self) == /\ pc[self] = "CleanupPreviousIRs"
                            /\ newDAG' = [newDAG EXCEPT ![self] = ExpandDAG([v |-> newDAGNodeSet[self], e |-> newDAGEdgeSet[self]], GetDeletionIRs(previousIRs[self]))]
                            /\ pc' = [pc EXCEPT ![self] = "Error"]
                            /\ UNCHANGED << DAGEventQueue, DrainRequestQueue, 
                                            stack, newPaths, previousIRs, 
                                            newIRs, nextPriority, 
                                            newIRsStartingIndex, newIRSet, 
                                            newDAGEdgeSet, newDAGNodeSet, 
                                            currentPath, currentPathResult, 
                                            currentRequest, currentTopology, 
                                            currentPaths, nodeToDrain, 
                                            currentIRs, endpoints, 
                                            pathsAfterDrain, drainPathSetIRs, 
                                            drainedDAG, nextDAGID >>

ComputeDrainedPathIRs(self) == ComputePriority(self)
                                  \/ ComputeNewPathsDAG(self)
                                  \/ CleanupPreviousIRs(self)

DrainLoop(self) == /\ pc[self] = "DrainLoop"
                   /\ Len(DrainRequestQueue) > 0
                   /\ currentRequest' = [currentRequest EXCEPT ![self] = Head(DrainRequestQueue)]
                   /\ DrainRequestQueue' = Tail(DrainRequestQueue)
                   /\ currentTopology' = [currentTopology EXCEPT ![self] = currentRequest'[self].topology]
                   /\ currentPaths' = [currentPaths EXCEPT ![self] = currentRequest'[self].paths]
                   /\ nodeToDrain' = [nodeToDrain EXCEPT ![self] = currentRequest'[self].node]
                   /\ currentIRs' = [currentIRs EXCEPT ![self] = currentRequest'[self].irs]
                   /\ pc' = [pc EXCEPT ![self] = "ComputeDrain"]
                   /\ UNCHANGED << DAGEventQueue, stack, newPaths, previousIRs, 
                                   newIRs, newDAG, nextPriority, 
                                   newIRsStartingIndex, newIRSet, 
                                   newDAGEdgeSet, newDAGNodeSet, currentPath, 
                                   currentPathResult, endpoints, 
                                   pathsAfterDrain, drainPathSetIRs, 
                                   drainedDAG, nextDAGID >>

ComputeDrain(self) == /\ pc[self] = "ComputeDrain"
                      /\ endpoints' = [endpoints EXCEPT ![self] = getPathSetEndpoints(currentPaths[self]) \ {nodeToDrain[self]}]
                      /\ pathsAfterDrain' = [pathsAfterDrain EXCEPT ![self] =                ShortestPaths(
                                                                              endpoints'[self],
                                                                              (currentTopology[self].Nodes \ {nodeToDrain[self]}),
                                                                              RemoveNodeFromEdgeSet(nodeToDrain[self], currentTopology[self].Edges))]
                      /\ /\ newDAG' = [newDAG EXCEPT ![self] = drainedDAG[self]]
                         /\ newIRs' = [newIRs EXCEPT ![self] = drainPathSetIRs[self]]
                         /\ newPaths' = [newPaths EXCEPT ![self] = pathsAfterDrain'[self]]
                         /\ previousIRs' = [previousIRs EXCEPT ![self] = currentIRs[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ComputeDrainedPathIRs",
                                                                  pc        |->  "SubmitDAG",
                                                                  nextPriority |->  nextPriority[self],
                                                                  newIRsStartingIndex |->  newIRsStartingIndex[self],
                                                                  newIRSet  |->  newIRSet[self],
                                                                  newDAGEdgeSet |->  newDAGEdgeSet[self],
                                                                  newDAGNodeSet |->  newDAGNodeSet[self],
                                                                  currentPath |->  currentPath[self],
                                                                  currentPathResult |->  currentPathResult[self],
                                                                  newPaths  |->  newPaths[self],
                                                                  previousIRs |->  previousIRs[self],
                                                                  newIRs    |->  newIRs[self],
                                                                  newDAG    |->  newDAG[self] ] >>
                                                              \o stack[self]]
                      /\ nextPriority' = [nextPriority EXCEPT ![self] = NADIR_NULL]
                      /\ newIRsStartingIndex' = [newIRsStartingIndex EXCEPT ![self] = NADIR_NULL]
                      /\ newIRSet' = [newIRSet EXCEPT ![self] = {}]
                      /\ newDAGEdgeSet' = [newDAGEdgeSet EXCEPT ![self] = {}]
                      /\ newDAGNodeSet' = [newDAGNodeSet EXCEPT ![self] = {}]
                      /\ currentPath' = [currentPath EXCEPT ![self] = NADIR_NULL]
                      /\ currentPathResult' = [currentPathResult EXCEPT ![self] = {}]
                      /\ pc' = [pc EXCEPT ![self] = "ComputePriority"]
                      /\ UNCHANGED << DAGEventQueue, DrainRequestQueue, 
                                      currentRequest, currentTopology, 
                                      currentPaths, nodeToDrain, currentIRs, 
                                      drainPathSetIRs, drainedDAG, nextDAGID >>

SubmitDAG(self) == /\ pc[self] = "SubmitDAG"
                   /\ DAGEventQueue' = Append(DAGEventQueue, ([id |-> nextDAGID[self], dag |-> drainedDAG[self]]))
                   /\ nextDAGID' = [nextDAGID EXCEPT ![self] = nextDAGID[self] + 1]
                   /\ pc' = [pc EXCEPT ![self] = "DrainLoop"]
                   /\ UNCHANGED << DrainRequestQueue, stack, newPaths, 
                                   previousIRs, newIRs, newDAG, nextPriority, 
                                   newIRsStartingIndex, newIRSet, 
                                   newDAGEdgeSet, newDAGNodeSet, currentPath, 
                                   currentPathResult, currentRequest, 
                                   currentTopology, currentPaths, nodeToDrain, 
                                   currentIRs, endpoints, pathsAfterDrain, 
                                   drainPathSetIRs, drainedDAG >>

drainer(self) == DrainLoop(self) \/ ComputeDrain(self) \/ SubmitDAG(self)

Next == (\E self \in ProcSet: ComputeDrainedPathIRs(self))
           \/ (\E self \in ({app0} \X {DRAIN_APP}): drainer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 

(* NADIR type annotations and assumptions *)

\* These define C-like structs later
STRUCT_SET_RC_DAG == [v: SUBSET NADIR_INT_ID_SET, e: SUBSET (NADIR_INT_ID_SET \X NADIR_INT_ID_SET)]
STRUCT_SET_DAG_OBJECT == [id: NADIR_INT_ID_SET, dag: STRUCT_SET_RC_DAG]
STRUCT_SET_IR_OBJECT == [priority: Nat, sw: SW, ir: NADIR_INT_ID_SET]
STRUCT_SET_TOPOLOGY == [Nodes: SUBSET Nat, Edges: SUBSET (Nat \X Nat)]
STRUCT_SET_DRAIN_REQUEST == [topology: STRUCT_SET_TOPOLOGY, paths: Seq(Nat), node: Nat, irs: SUBSET STRUCT_SET_IR_OBJECT]

\* This aggregator defines the name of structs during code generation
NadirStructSet == ("StructRCDAG" :> STRUCT_SET_RC_DAG) @@
                  ("StructDAGObject" :> STRUCT_SET_DAG_OBJECT) @@
                  ("StructIRObject" :> STRUCT_SET_IR_OBJECT) @@
                  ("StructTopology" :> STRUCT_SET_TOPOLOGY) @@
                  ("StructDrainRequest" :> STRUCT_SET_DRAIN_REQUEST)

\* The type annotation. It is also an invariant of the specification
TypeOK ==  /\ NadirFIFO(STRUCT_SET_DAG_OBJECT, DAGEventQueue)
           /\ NadirFIFO(STRUCT_SET_DRAIN_REQUEST, DrainRequestQueue)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_DRAIN_REQUEST), currentRequest)
           /\ NadirLocalVariableTypeCheck(NadirNullable(STRUCT_SET_TOPOLOGY), currentTopology)
           /\ NadirLocalVariableTypeCheck(SUBSET Seq(Nat), currentPaths)
           /\ NadirLocalVariableTypeCheck(NadirNullable(Nat), nodeToDrain)
           /\ NadirLocalVariableTypeCheck(SUBSET STRUCT_SET_IR_OBJECT, currentIRs)
           /\ NadirLocalVariableTypeCheck(SUBSET Nat, endpoints)
           /\ NadirLocalVariableTypeCheck(SUBSET Seq(Nat), pathsAfterDrain)
           /\ NadirLocalVariableTypeCheck(SUBSET STRUCT_SET_IR_OBJECT, drainPathSetIRs)
           /\ NadirLocalVariableTypeCheck(SUBSET STRUCT_SET_RC_DAG, drainedDAG)
           /\ NadirLocalVariableTypeCheck(Nat, nextDAGID)

\* These assumptions define what type of inputs we should expect
\* Any other input (like `SW` for this specification) is assumed to be a set of TLC Model Values
NadirConstantAssumptions == MaxNumIRs \in Nat

ASSUME NadirConstantAssumptions

====

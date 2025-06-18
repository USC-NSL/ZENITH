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
                     IN _GetDeletionIRs(setOfIRs \ {currentIR}, deleterSet \cup {currentIR + MaxNumIRs})
        
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

    macro ComputeDrainedPathIRs(newPaths, previousIRs, newIRs, newDAG) begin
        \* The new IRs MUST be installed with a higher priority than 
        \* previous paths (otherwise, there is no way to guarantee the
        \* drain is hitless). To do this, sift through previous IRs and
        \* get the highest priority in it.
        with res = GeneratePathSetIRs(newPaths, Cardinality(previousIRs), HighestPriorityInIRSet(previousIRs) + 1)  do
            newIRs := res.irs;
            newDAG := ExpandDAG([v |-> res.nodes, e |-> res.edges], res.OriginalIRs.nodes);
        end with;
    end macro;

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
            with nodesAfterDrain = (currentTopology.Nodes \ {nodeToDrain}) do
                \* Get all paths assuming the given node was removed from the topology
                pathsAfterDrain := ShortestPaths(
                    endpoints, 
                    nodesAfterDrain, 
                    RemoveNodeFromEdgeSet(nodeToDrain, currentTopology.Edges));
                \* (MACRO CALL) Compute the new DAG and IRs that implement the paths
                ComputeDrainedPathIRs(pathsAfterDrain, currentIRs, drainPathSetIRs, drainedDAG);
            end with;
        SubmitDAG:
            \* (MACRO CALL) Generate an ID for this DAG and send it to the core
            NadirFIFOPut(DAGEventQueue, [id |-> nextDAGID, dag |-> drainedDAG]);
            nextDAGID := nextDAGID + 1;
    end while;
    end process;
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "a61310aa" /\ chksum(tla) = "57a326cd")
VARIABLES DAGEventQueue, DrainRequestQueue, pc

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
             IN _GetDeletionIRs(setOfIRs \ {currentIR}, deleterSet \cup {currentIR + MaxNumIRs})

GetDeletionIRs(setOfIRs) == _GetDeletionIRs(setOfIRs, {})

VARIABLES currentRequest, currentTopology, currentPaths, nodeToDrain, 
          currentIRs, endpoints, pathsAfterDrain, drainPathSetIRs, drainedDAG, 
          nextDAGID

vars == << DAGEventQueue, DrainRequestQueue, pc, currentRequest, 
           currentTopology, currentPaths, nodeToDrain, currentIRs, endpoints, 
           pathsAfterDrain, drainPathSetIRs, drainedDAG, nextDAGID >>

ProcSet == (({app0} \X {DRAIN_APP}))

Init == (* Global variables *)
        /\ DAGEventQueue = <<>>
        /\ DrainRequestQueue = <<>>
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
        /\ pc = [self \in ProcSet |-> "DrainLoop"]

DrainLoop(self) == /\ pc[self] = "DrainLoop"
                   /\ Len(DrainRequestQueue) > 0
                   /\ currentRequest' = [currentRequest EXCEPT ![self] = Head(DrainRequestQueue)]
                   /\ DrainRequestQueue' = Tail(DrainRequestQueue)
                   /\ currentTopology' = [currentTopology EXCEPT ![self] = currentRequest'[self].topology]
                   /\ currentPaths' = [currentPaths EXCEPT ![self] = currentRequest'[self].paths]
                   /\ nodeToDrain' = [nodeToDrain EXCEPT ![self] = currentRequest'[self].node]
                   /\ currentIRs' = [currentIRs EXCEPT ![self] = currentRequest'[self].irs]
                   /\ pc' = [pc EXCEPT ![self] = "ComputeDrain"]
                   /\ UNCHANGED << DAGEventQueue, endpoints, pathsAfterDrain, 
                                   drainPathSetIRs, drainedDAG, nextDAGID >>

ComputeDrain(self) == /\ pc[self] = "ComputeDrain"
                      /\ endpoints' = [endpoints EXCEPT ![self] = getPathSetEndpoints(currentPaths[self]) \ {nodeToDrain[self]}]
                      /\ LET nodesAfterDrain == (currentTopology[self].Nodes \ {nodeToDrain[self]}) IN
                           /\ pathsAfterDrain' = [pathsAfterDrain EXCEPT ![self] =                ShortestPaths(
                                                                                   endpoints'[self],
                                                                                   nodesAfterDrain,
                                                                                   RemoveNodeFromEdgeSet(nodeToDrain[self], currentTopology[self].Edges))]
                           /\ LET res == GeneratePathSetIRs(pathsAfterDrain'[self], Cardinality(currentIRs[self]), HighestPriorityInIRSet(currentIRs[self]) + 1) IN
                                /\ drainPathSetIRs' = [drainPathSetIRs EXCEPT ![self] = res.irs]
                                /\ drainedDAG' = [drainedDAG EXCEPT ![self] = ExpandDAG([v |-> res.nodes, e |-> res.edges], res.OriginalIRs.nodes)]
                      /\ pc' = [pc EXCEPT ![self] = "SubmitDAG"]
                      /\ UNCHANGED << DAGEventQueue, DrainRequestQueue, 
                                      currentRequest, currentTopology, 
                                      currentPaths, nodeToDrain, currentIRs, 
                                      nextDAGID >>

SubmitDAG(self) == /\ pc[self] = "SubmitDAG"
                   /\ DAGEventQueue' = Append(DAGEventQueue, ([id |-> nextDAGID[self], dag |-> drainedDAG[self]]))
                   /\ nextDAGID' = [nextDAGID EXCEPT ![self] = nextDAGID[self] + 1]
                   /\ pc' = [pc EXCEPT ![self] = "DrainLoop"]
                   /\ UNCHANGED << DrainRequestQueue, currentRequest, 
                                   currentTopology, currentPaths, nodeToDrain, 
                                   currentIRs, endpoints, pathsAfterDrain, 
                                   drainPathSetIRs, drainedDAG >>

drainer(self) == DrainLoop(self) \/ ComputeDrain(self) \/ SubmitDAG(self)

Next == (\E self \in ({app0} \X {DRAIN_APP}): drainer(self))

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

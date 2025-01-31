---- MODULE NadirTypes ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences

(**********************************************************************)
(* This constant represents any Null-like value the implementation.   *)
(* This includes things like initial values of local variables.       *)
(* During implementation, any expression that depends on the explicit *) 
(* value of this constant will cause an error.                        *)
(**********************************************************************)
CONSTANT NADIR_NULL

(*************************************************************************)
(* The spec may refer to certain structs without implementation with     *)
(* just a simple integer identifier. For example, a packet that is to be *)
(* delivered to some node might be just represented with a number.       *)
(* During implementation, a struct will be used to represent the data    *)
(* which is not all reflected in the spec. The number that the spec      *)
(* uses is the `ID` of the data and it is essentially a pointer to       *)
(* the actual data in the implementation.                                *)
(* Such identifier are picked from this set, and during implementation   *)
(* we will make sure to allow for arbitrary data structures to be found  *)
(* with the object associated with it.                                   *)
(*************************************************************************)
NADIR_INT_ID_SET == ({0} \cup Nat)

(********************************************************************************)
(* TLC functions can go from any set of comparable values, to any TLC value.    *)
(* Usually though, most implementations also make the assumption that the range *)
(* itself is also a set of comparable values (which is not requried).           *)
(* This expression assumes the function is of that type and checks for what     *)
(* values the domain and range elements exist.                                  *)
(********************************************************************************)
NadirFunctionTypeCheck(domainSet, rangeElemSet, f) == /\ DOMAIN f \subseteq domainSet
                                                      /\ \A x \in DOMAIN f: f[x] \in rangeElemSet

(*****************************************************************)
(* An extension of the above for checking function of functions. *)
(*****************************************************************)
NadirDoubleFunctionTypeCheck(domainSet1, domainSet2, rangeElemSet2, f) == /\ DOMAIN f \subseteq domainSet1
                                                                          /\ \A x \in DOMAIN f: NadirFunctionTypeCheck(domainSet2, rangeElemSet2, f[x])

(********************************************************************************)
(* A FIFO queue of messages, is a tuple that is only accessed on head and tail. *)
(* The code generation specifically checks for this in the spec and the         *)
(* implementation will make optimizations based on this fact.                   *)
(********************************************************************************)
NadirFIFO(messageSet, queue) == queue \in Seq(messageSet)

(*****************************************************************************)
(* A FIFO queue that can emit messages to multiple destinations when needed. *)
(* Semantically, it is equivalent to a function mapping some domain to a set *)
(* of FIFO queues like above.                                                *)
(*****************************************************************************)
NadirFanoutFIFO(destinationSet, messageSet, functionOfQueues) == NadirFunctionTypeCheck(destinationSet, Seq(messageSet), functionOfQueues)

(******************************************************************************)
(* The queue above is a FIFO, this one implies that it is an AckQueue instead *)
(******************************************************************************)
NadirAckQueue(messageSet, queue) == queue \in Seq(messageSet)
                                    \* /\ \A x \in messageSet: "tag" \in DOMAIN x

(**********************************************************************)
(* This asserts that the set of given variables can be Null at times. *)
(**********************************************************************)
NadirNullable(x) == x \cup {NADIR_NULL}

(******************************************************************************************)
(* When PlusCal is translated into TLA+, local variables under a process `p`, operating   *)
(* over a set `S` of processes, will be implemented as a function from `p \X S` to the    *)
(* actual variable value in the PlusCal spec. This definition checks for the value of the *)
(* variable, but not for the domain, since that is rarely useful in practice.             *)
(******************************************************************************************)
NadirLocalVariableTypeCheck(varType, var) == \A x \in DOMAIN var: var[x] \in varType

(*******************************************************************************************)
(* Nadir _expects_ processes to be identified with the product of two sets `M x SM`, where *)
(* `M` is a singleton containing a model value that defined the _module_ of the process,   *)
(* and `SM` is a non-empty set of model values, describing _sub-modules_ of the process.   *)
(* A process belongs only to a single module, and its sub-modules can fail independently.  *)
(* The following signals to Nadir what such identifiers are.                               *)
(*******************************************************************************************)
NadirProcessIdentifier(moduleMV, setOfSubModuleMVs) == {moduleMV} \X setOfSubModuleMVs
NadirSetOfPIDs(PIDSet) == \A PID \in PIDSet: Len(PID) = 2

NadirIDAsInteger(x) == x
IntegerAsNadirID(x) == x
IntegerSetAsNadirIDSet(x) == x

======================
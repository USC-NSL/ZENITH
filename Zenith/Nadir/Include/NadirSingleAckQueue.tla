---- MODULE NadirSingleAckQueue ----
EXTENDS Integers, Sequences, TLC
CONSTANTS UNTAGGED, TAGS, OBJECTS
VARIABLES _queue, _unacked

(******************************************************************)
(* This is a trivial ACK queue implementation with a prefetch     *)
(* count of 1, meaning that each subscriber can only have at most *)
(* a single unacked object.                                       *)
(* This queue allows a subscriber to tag first available object   *)
(* on the queue with its subscriber tag and prevent others from   *)
(* tagging it. It can NACK it to allow other threads to handle    *)
(* it, or ACK it which causes the object to be removed from the   *)
(* queue.                                                         *)
(******************************************************************)

Init == /\ _queue = <<>>            \* A queue of pairs of the form `<object, tag>`
        /\ _unacked = UNTAGGED      \* Maps subscriber tags to their un-acked object

(* Put an object at the end of the queue and mark it as untagged *)
Publish(object) == /\ _queue' = Append(_queue, [obj |-> object, tag |-> UNTAGGED])
                   /\ UNCHANGED <<_unacked>>

(* There is an item not yet being processed *)
ExistsUntaggedItem(tag) == \E x \in DOMAIN _queue: _queue[x].tag = tag

(* Recursively get the index of the first item in the queue with a given tag *)
RECURSIVE _GetFirstItemIndexWithTag(_, _)
_GetFirstItemIndexWithTag(index, tag) == IF _queue[index].tag = tag
                                            THEN index
                                            ELSE _GetFirstItemIndexWithTag(index+1, tag)

(* Shortcuts for getting the first item index in the queue with or without a given tag *)
GetFirstUntaggedItemIndex == _GetFirstItemIndexWithTag(1, UNTAGGED)
GetFirstItemIndexWithTag(tag) == _GetFirstItemIndexWithTag(1, tag)

(* Remove an item from the sequence given its index and make a new sequence *)
RemoveFromSequenceByIndex(seq, index) == [j \in 1..(Len(seq) - 1) |-> IF j < index THEN seq[j] ELSE seq[j+1]]

(* Get the tagged object (there can only be at most one) *)
ReadTaggedObject(tag) == _unacked[tag]

(* If possible, tag an object so you can read it and protect it from other threads *)
Get(tag) == /\ \/ /\ tag \in DOMAIN _unacked
                  /\ _unacked[tag] # UNTAGGED
               \/ ExistsUntaggedItem(tag)
            /\ IF tag \notin DOMAIN _unacked \/ _unacked[tag] = UNTAGGED
                THEN LET 
                        idx == GetFirstUntaggedItemIndex
                     IN 
                        /\ _queue' = [_queue EXCEPT ![idx] = <<_queue[idx].obj, tag>>]
                        /\ _unacked' = IF _unacked = UNTAGGED
                                        THEN (tag :> _queue[idx].obj)
                                        ELSE [_unacked EXCEPT ![tag] = _queue[idx].obj]
                ELSE UNCHANGED <<_queue, _unacked>>

(* Declare that you cannot handle the item you tagged and return it to the queue, untagged *)
Nack(tag) == /\ _unacked[tag] # UNTAGGED
             /\ LET
                    idx == GetFirstItemIndexWithTag(tag)
                IN
                    /\ Assert(_queue[idx].object = _unacked[tag], "Object mismatch during NACK!")
                    /\ Assert(_queue[idx].tag = tag, "Tag mismatch during NACK!")
                    /\ _queue' = [_queue EXCEPT ![idx] = <<_queue[idx].obj, tag>>]
                    /\ _unacked' = [_unacked EXCEPT ![tag] = UNTAGGED]

(* Declare that you handled the item you tagged and remove it from the queue *)
Ack(tag) == /\ _unacked[tag] # UNTAGGED
            /\ LET
                    idx == GetFirstItemIndexWithTag(tag)
               IN
                    /\ Assert(_queue[idx].object = _unacked[tag], "Object mismatch during ACK!")
                    /\ Assert(_queue[idx].tag = tag, "Tag mismatch during ACK!")
                    /\ _queue' = RemoveFromSequenceByIndex(_queue, idx)
                    /\ _unacked' = [_unacked EXCEPT ![tag] = UNTAGGED]

(* Check if there is anything in the queue at all (be it tagged or not) *)
NotEmpty == Len(_queue) > 0

Next == \/ \E tag \in TAGS: Get(tag)
        \/ \E tag \in TAGS: Nack(tag)
        \/ \E tag \in TAGS: Ack(tag)
        \/ \E object \in OBJECTS: Publish(object)

Spec == Init /\ [][Next]_<<_queue, _unacked>>

======================
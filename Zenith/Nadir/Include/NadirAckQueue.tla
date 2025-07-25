---- MODULE NadirAckQueue ----
EXTENDS TLC, Integers, Sequences, NadirTypes

ExistsItemWithTag(queue, tag) == \E x \in DOMAIN queue: queue[x].tag = tag

RECURSIVE _GetFirstItemIndexWithTag(_, _, _)
_GetFirstItemIndexWithTag(queue, index, tag) == IF queue[index].tag = tag
                                                    THEN index
                                                    ELSE _GetFirstItemIndexWithTag(queue, index+1, tag)

GetFirstUntaggedItemIndex(queue) == _GetFirstItemIndexWithTag(queue, 1, NADIR_NULL)
GetFirstItemIndexWithTag(queue, tag) == _GetFirstItemIndexWithTag(queue, 1, tag)

RemoveFromSequenceByIndex(seq, index) == [j \in 1..(Len(seq) - 1) |-> IF j < index THEN seq[j] ELSE seq[j+1]]

GetItemIndexWithTag(queue, tag) == IF ~ExistsItemWithTag(queue, tag)
                                    THEN GetFirstUntaggedItemIndex(queue)
                                    ELSE GetFirstItemIndexWithTag(queue, tag)
====
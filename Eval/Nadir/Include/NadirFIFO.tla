---- MODULE NadirFIFO ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences

VARIABLES _fifo, _msg

FIFOGet == /\ Len(_fifo) > 0
           /\ _msg' = Head(_fifo)
           /\ _fifo' = Tail(_fifo)

FIFOPut(object) == _fifo' = Append(_fifo, object)

======================
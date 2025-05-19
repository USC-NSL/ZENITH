---- MODULE nadir_spec_tlc ----
EXTENDS NoFailover, TLC, Nadir

CONSTANTS
t0
----

const_SW == {1, 2}
----

const_CONTROLLER_THREAD_POOL == {t0}
----

const_IR2SW == (1 :> 1) @@ (2 :> 2) @@ (3 :> 2)
----

const_MaxDAGID == 15
----

const_MaxNumIRs == 3
----

const_TOPO_DAG_MAPPING == 
({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ ({1} :> [v |-> {3}, e |-> {}])
----

=============================================================================

# Simplified Specs For NADIR

These are simplified spec and configuration files for generating code directly from NADIR.

This spec does not implement failover and switch side reconciliation, and is based on the spec [here](../../noFailover/5.switchCompleteTransientFailure/verified_wo_sw_reconciliation.tla).

# Changelog
    
- Removed constants `NO_STATUS`, `DAG_UNLOCK`, `IR_UNLOCK` and introduced `NADIR_NULL`. 
Anything that is supposed to be a placeholder for some `null` like value during implementation will be represented as `NADIR_NULL`.

- (Finally!) Broke apart `controllerStateNIB` into 2 separate variables, `ofcInternalState` and `rcInternalState`. 
These have no relation to the NIB and during implementation, will be treated as two separate things (so, 2 separate databases for 2 separate modules, as they should have been from the beginning!)

- At this point, we are committed to having a single RC, thus indexing any variable with the RC thread identifier `rc0` is pointless, and it makes function implementation awkward. 
Thus, we completely removed anything that looks like `self[1]` or `[rc0]` indexing, and also fixed the associated macros to reflect that.

- Removed `RCSeqWorkerStatus`, as it does nothing. The 3 constants that are associated with it, `SEQ_WORKER_RUN`, `SEQ_WORKER_STALE_SIGNAL` and `SEQ_WORKER_STALE_REMOVED` were also removed as a result.

- Removed `controllerIsMaster`, it does nothing when we have no failover.
- Removed constant `NO_TAG` and replaced its usage with `NADIR_NULL`.
- Removed the variable `FirstInstall` and the invariant check for redundant installation, as we are no longer considering it.
- Moved previously global variable `DAGID` into the process `controllerTrafficEngineering`, since that is the only place it is used.
- Removed `MaxDAGID` as a variable, and reintroduced it as a constant.
- Sequencer is no longer multithreaded, since it has very little practical utility.

- Intorduced the macro `getNextIRID`, since its implementation actually has some subtle practical qualities.
- Introduced the macro `prepareDeletionIR(forWhat)` which prepares a deletion for an IR with identifier `forWhat`. Can be used for both the RC scheduler and the RC IR monitor.

- Introduced the macro `getNextDAGID`, this will make the changes in implementation much easier.

> For now, we have also removed any code that is not supposed to be implemented (which would be anything related to the switches). In the future, we might allow for implementation via inferred refinement of the spec, instead of having to butcher it.

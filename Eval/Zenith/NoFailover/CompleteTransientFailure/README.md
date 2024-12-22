# Evaluation For `CompleteTransientFailure`

This spec contains the `ZENITH` implementation robust to complete and transient switch failures.
The spec implements:
- Full OFC, including Worker Pool, Event Handler and Monitoring Server
- Full RC, including Worker Sequencer, Boss Sequencer, TE and IR Monitor

This builds on top of `CompletePermanentFailure` specification, and shares all of its inputs with it.

This is the final `ZENITH` specification for the case where no OFC failovers happen (meaning that the whole
of OFC never dies at the same time, such that we need to replace it with a new one). The model allows for
arbitrary switch failure scenarios, and thus is very complex compared to our previous models (with the
exception of OFC Failover model).

The main difficulty here is to see if `ZENITH` is able to correctly switch between configurations meant for
different topologies. Once this spec is verified, the core of `ZENITH`, which consists of:
- The entire OFC
- RC Worker and Boss Sequencers
- RC NIB Event Handler

Are proven to be robust enough to handle configuration changes, in particular, they are robust enough to
handle a queue of input DAGs and push them into the network and clean them up when needed. The TE module
is merely an application here, and while it too should be correct, it is not the main focus here.

We implement two versions of this spec, one that never uses any switch-side reconciliation (the `ZENITH-NR`), 
and a version of it that uses _Directed Reconciliation_ (the `ZENITH-DR`), which means that it only inspects 
certain switches when needed, not all of them at once. The two provide slightly different properties.

## Evaluation Parameters

This is shared for both `ZENITH-NR` and `ZENITH-DR`:

- `SW`: The set of model values that distinguish switches
- `CONTROLLER_THREAD_POOL`: The set of model values that distinguish threads in the Worker Pool
- `SW_MODULE_CAN_FAIL_OR_NOT`: Which switch components (i.e. the NIC ASIC, CPU, OFA or Installer) are allowed to fail.
- `SW_FAIL_ORDERING`: This variable instructs how our switches can fail. We disable transient and partial failures for
one of our switches (`s0` in particular), which means that it can only fail completely.
- `MaxNumIRs`: How many distinct instructions exist within all DAGs?
- `MaxNumFlows`: These are always chosen to be equal to `MaxNumIRs` for this evaluation.
- `MaxDAGID`: A matter of formality, set to some reasonably high number.
- `WHICH_SWITCH_MODEL`: This is set to `SW_SIMPLE_MODEL`. Partial failures are of no concern anymore, and for complete
failures we have also been proven to be robust, thus we choose to keep using the simple model, since without it, the
state space becomes way too large. In this spec, the only thing that matters is _when_ the switch fails, not how it fails.
- `MAX_NUM_CONTROLLER_SUB_FAILURE`: Set such that RC and OFC sub-modules do not fail.
- `FINAL_DAG`: This spec is subject to fairness when it comes to switch failures. Thus, the switches eventually stop failing
at the end of every behavior, and thus the final DAG that `ZENITH` must correctly install, will be the DAG that is associated
with a completely healthy network. This value will hold that particular DAG.
- `IR2SW`: A function that maps IRs to their designated switch.
- `TOPO_DAG_MAPPING`: A function that maps the set of down switches, to the appropriate DAG for that topology.
- `IR2FLOW`: An identity map over the IR number. This is used to create deletion flows for an installed IR.

## Invariants and Properties

For `ZENITH-NR`:
- `InstallationLivenessProp`: Eventually, the network converges to the DAG specified in `FINAL_DAG`, and will stay there.
- `IRCriticalSection`: No two Worker Pool threads ever execute the following labels at the same time, with the same IR
    - `ControllerThreadSendIR` and `ControllerThreadForwardIR`: No two Worker Pool threads ever send the same IR at the same time
    - `ReScheduleifIRNone`: No two Worker Pool threads ever attempt to reschedule the same IR at the same time
    - `WaitForIRToHaveCorrectStatus`: No two Worker Pool threads wait for the installation of the same IR at the same time
- `ConsistencyReq`: The dependency of IRs given the DAG is honored

For `ZENITH-DR`, we also have the following extra property:
- `RedundantInstallation`: For each DAG switch, each IR in it is installed at most once. There are no cases where `ZENITH-DR` 
mistakenly re-installs an IR that is already in the TCAM.

## Evaluation Test
We evaluated with the following configurations:
- 2 switches, one of which can arbitrarily fail at any time
- 1 Worker Pool thread
- 3 IRs
- IR assignments `(1 :> s0) @@ (2 :> s1) @@ (3 :> s1)`
- Set of downed switches to DAG mapping: `({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ `
                                         `({s0} :> [v |-> {3}, e |-> {}])`

This generated 6988498 distinct states, with a graph of diameter 213. The model took 22 minutes and 47 seconds to be verified.

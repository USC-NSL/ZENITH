# Evaluation For `CompletePermanentFailure`

This spec contains the `ZENITH` implementation robust to complete switch failures.
The spec implements:
- Full OFC, including Worker Pool, Event Handler and Monitoring Server
- The Sequencer, Boss Sequencer and Traffic Engineering sub-modules of RC

This builds on top of `BothTransientFailure` specification, and shares most of its inputs with it.

This spec tries to evaluate `ZENITH`s ability to cope with topology changes. The goal is that if a network
change happens, can `ZENITH` correctly clean up the previous configuration within the network and install
the new one?

To this end, this module accepts as an input, a function that maps the current topology (or the current set
of down switches), to a DAG that we wish to install within the network.

Since this evaluation builds on top of `BothTransientFailure`, and Worker Pool remains unchanged from that,
we can be sure that it is still robust to races between worker threads and thus to reduce the state space,
we evaluate using only a single Worker Pool thread; we also no longer allow for OFC sub-modules to fail in this spec, since
we are also sure that they are robust to that. 

The main difficulty of this spec comes with RC, in particular the Traffic Engineering and Sequencer modules that should handle changes from one DAG to another.

## Evaluation Parameters

- `SW`: The set of model values that distinguish switches
- `CONTROLLER_THREAD_POOL`: The set of model values that distinguish threads in the Worker Pool
- `SW_MODULE_CAN_FAIL_OR_NOT`: Which switch components (i.e. the NIC ASIC, CPU, OFA or Installer) are allowed to fail.
- `SW_FAIL_ORDERING`: This variable instructs how our switches can fail. We disable transient and partial failures for
one of our switches (`s0` in particular), which means that it can only fail completely.
- `MaxNumIRs`: How many distinct instructions exist within all DAGs?
- `MaxNumFlows`: These are always chosen to be equal to `MaxNumIRs` for this evaluation.
- `MaxDAGID`: A matter of formality, set to some reasonably high number.
- `WHICH_SWITCH_MODEL`: This is set to `SW_SIMPLE_MODEL`, since with complete failure, there is no sense in simulating the
internal function of a switch, when they are all going to stop at the same time.
- `MAX_NUM_CONTROLLER_SUB_FAILURE`: Set such that RC and OFC sub-modules do not fail.
- `FINAL_DAG`: We choose one switch to fail completely (when that happens is chosen by TLA+). This DAG should be the one
that finally ends up in the network.
- `IR2SW`: A function that maps IRs to their designated switch.
- `TOPO_DAG_MAPPING`: A function that maps the set of down switches, to the appropriate DAG for that topology.
- `IR2FLOW`: An identity map over the IR number. This is used to create deletion flows for an installed IR.

## Invariants and Properties

- `InstallationLivenessProp`: Eventually, the network converges to the DAG specified in `FINAL_DAG`, and will stay there.
- `IRCriticalSection`: No two Worker Pool threads ever execute the following labels at the same time, with the same IR
    - `ControllerThreadSendIR` and `ControllerThreadForwardIR`: No two Worker Pool threads ever send the same IR at the same time
    - `ReScheduleifIRNone`: No two Worker Pool threads ever attempt to reschedule the same IR at the same time
    - `WaitForIRToHaveCorrectStatus`: No two Worker Pool threads wait for the installation of the same IR at the same time
- `RedundantInstallation` and `EachIRAtMostOnce`: Combined together, they assert that an IR, if it manages to be installed, is
installed at most once (since an installed IR can get lost, `RedundantInstallation` by itself cannot guarantee that an IR that
is at `IR_DONE`, isn't installed more than once).
- `ConsistencyReq`: The dependency of IRs given the DAG is honored

## Evaluation Test
We evaluated with the following configurations:
- 3 switches, one of which permanently fails at some arbitrary point
- 1 Worker Pool thread
- 5 IRs
- IR assignments `(1 :> s0) @@ (2 :> s1) @@ (3 :> s2) @@ (4 :> s1) @@ (5 :> s2)`
- Initial DAG: `[v |-> {1, 2, 3}, e |-> {<<1, 2>>, <<1, 3>>}]`
- Final DAG: `[v |-> {4, 5}, e |-> {<<5, 4>>}]`

This generated 100572 distinct states, with a graph with diameter 127. The model took 24 seconds to be verified.

# Evaluation For `BothTransientFailure`

This spec contains the `ZENITH` implementation robust to transient switch failures and module failures.
The spec implements:
- Full OFC, including Worker Pool, Event Handler and Monitoring Server
- The Sequencer sub-module of RC

The specification allows for both `ZENITH` OFC components _and_ switch components to fail independently (so there are
behaviors that allow for both controller components and switches to die within the same branch).

The specification generates any input DAG with the given number of IRs, and also an assignment of IRs to switches. It
will then attempt to install this DAG, while handling switch and component failures.

Switches fail _transiently_, meaning that they do not lose states between failures, and they will not stay dead forever. Thus
in this version of `ZENITH`, if an instruction is installed on a switch, we can be sure that it stays there forever, and if
we are yet to receive the confirmation of the installation of some IR, we will in the very near future.

## Evaluation Parameters

- `SW`: The set of model values that distinguish switches
- `CONTROLLER_THREAD_POOL`: The set of model values that distinguish threads in the Worker Pool
- `MaxNumIRs`: How many distinct instructions exist within a DAG?
- `MAX_NUM_CONTROLLER_SUB_FAILURE`: How many times can a controller sub-module fail within the same branch? (so for example, when OFC
can fail at most 2 times, then at most 2 components of it, be Worker Pool, Monitoring Server or Event Handler, can fail in the same branch).
- `SW_MODULE_CAN_FAIL_OR_NOT`: Which switch components (i.e. the NIC ASIC, CPU, OFA or Installer) are allowed to fail.
- `MaxNumFlows`: These are always chosen to be equal to `MaxNumIRs` for this evaluation.
- `IR_TO_SWITCH_ASSIGNMENT`: An arbitrary assignment of IRs to switches. Since the spec considers all possible DAGs, this value is not needed
to be checked with all possible configurations.

## Invariants and Properties

- `InstallationLivenessProp`: Eventually the DAG is installed. All IRs appear in the associated switch and stay there, and all associated states within the NIB are set to `IR_DONE` and will stay there.
- `IRCriticalSection`: No two Worker Pool threads ever execute the following labels at the same time, with the same IR
    - `ControllerThreadSendIR` and `ControllerThreadForwardIR`: No two Worker Pool threads ever send the same IR at the same time
    - `ReScheduleifIRNone`: No two Worker Pool threads ever attempt to reschedule the same IR at the same time
    - `WaitForIRToHaveCorrectStatus`: No two Worker Pool threads wait for the installation of the same IR at the same time
- `RedundantInstallation`: An IR is installed exactly once, and only if it is not already in the switch
- `ConsistencyReq`: The dependency of IRs given the DAG is honored

## Evaluation Test
We evaluated with the following configurations:
- 2 switches
- 2 Worker Pool threads
- 3 IRs
- Maximum 2 failures
- IR assignments `(1 :> s0) @@ (2 :> s1) @@ (3 :> s1)`

This generated 2333630 distinct states, with a graph with diameter 111. The model took 4 minutes and 44 seconds to be verified.

# Final `ZENITH` Specifications and Evaluations

Final `ZENITH` specifications for each scenario are to be found here. The directories are:
- **`Include/`:** It contains definitions and constants that `ZENITH` extends to implement its functionalities.
    - `*_constants.tla`: define constants for `ZENITH` and its evaluations.
    - `dag.tla` and `graph.tla`: contain definitions that help reason about DAGs and directed graphs (`dag.tla` is used directly in `ZENITH`, `graph.tla` is used only for the specification of a switch drain application which was discussed in the appendix of the paper).
- **`Switch/`:** The full switch specification, decoupled from `ZENITH` itself.
    - `switch.tla`: is the specification of a switch with individual modules for a more expressive specification
    - `simple_switch.tla`: is the specification of a *monolithic* switch (the *AbstractSwitch* as called in the paper)
- **`Zenith/`:** Different `ZENITH` specifications, evaluated for different scenarios.
    - `Applications`: Currently holds the description of a switch drain application.
    - `Scenarios`: Specification of different version of `ZENITH` specifically for different failure scenarios (transient, permanent, etc.)
    - `AbstractCore.tla`: Specification of the *AbstractCore*, an abstract version of `ZENITH` that can be used to verify applications written on top of `ZENITH`.
- **`Nadir/`:** Contains version of the specification that have sufficient annotation for use with our code generation tool, `NADIR`.

>The final specification of `ZENITH`, with its `NADIR` annotations, is the `concurrent_spec.tla` module under `Naidr/`.

We also provide two utility scripts:
- `evaluate.py`: While the TLA+ toolbox can be used to run the evaluation, we think it is easier to directly use the TLA+ tools JAR file instead. This script allows one to parse, translate and evaluate any `ZENITH` specification here and it automatically imports all specifications that we keep in `Include`.
- `trace_utils.py`: A utility that can consume the traces that TLA+ generates as a counter-example, and make them easier to read, by removing some variables, making DIFFs, etc. (for some reason, the JAR file does not produce DIFF traces even when `-diff` is passed to it).

>**Note:** To use `evaluate.py`, an environment variable, `TLA_HOME`, needs to be set that points to the location of the `tla2tools.jar` file, which implements TLC, SANY, and the PlusCal translator.

Each specification has a companion model checking specification of the form `evaluate_*.tla` and a companion boilerplate configuration file `evaluate_*.cfg`. These can be passed directly to `evaluate.py` to link our libraries and invoke TLC.

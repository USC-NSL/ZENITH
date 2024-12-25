# Final `ZENITH` Specifications and Evaluations

Final `ZENITH` specifications for each scenario are to be found here. The directories are:
- **Include:** It contains definitions and constants that `ZENITH` extends to implement its functionalities.
- **Switch:** The full switch specification, decoupled from `ZENITH` itself.
- **Zenith:** Different `ZENITH` specifications, evaluated for different scenarios.

We also provide two utility scripts:
- `evaluate.py`: While the TLA+ toolbox can be used to run the evaluation, we think it is easier to directly use the TLA+ tools JAR file instead. This script allows one to parse, translate and evaluate any `ZENITH` specification here and it automatically imports all specifications that we keep in `Include`.
- `trace_utils.py`: A utility that can consume the traces that TLA+ generates as a counter-example, and make them easier to read, by removing some variables, making DIFFs, etc.

To use `evaluate.py`, an environment variable, `TLA_HOME`, needs to be set that points to the location of the `tla2tools.jar` file, which implements TLC, SANY, and the PlusCal translator.

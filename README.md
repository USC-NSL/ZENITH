# TLA+ Specifications of `ZENITH`

This repository contains all iterations of the `ZENITH` controller specifications.

- `Zenith/` contains the final versions of the controller. We provide multiple version of it that handle different scenarios that show the main challanges of each scenario.
- `PreviousSpecs/` contains all previous iterations of `ZENITH`. As discussed in the paper, designing `ZENITH` was a long procedure that required multiple iterations. Some of these scenarios also contain *bug* descriptions, which are particular traces that show how a particular specification might fail to uphold its requirements.

The TLA$^+$ Toolbox, can be used to work with these specifications, however (especially for the ones under `Zenith/`) we found it easier to directly use the `tla2tools` JAR file.

If inclined to follow this, the scripts for using it are available and described under `Zenith/`.
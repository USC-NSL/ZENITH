# TLA+ Specifications of `ZENITH`

This repository contains all iterations of the `ZENITH` controller specifications.

- `Zenith/` contains the final versions of the controller. We provide multiple version of it that handle different scenarios that show the main challanges of each scenario.
- `PreviousSpecs/` contains all previous iterations of `ZENITH`. As discussed in the paper, designing `ZENITH` was a long procedure that required multiple iterations. Some of these scenarios also contain *bug* descriptions, which are particular traces that show how a particular specification might fail to uphold its requirements.

The TLA+ Toolbox, can be used to work with these specifications, however (especially for the ones under `Zenith/`) we found it easier to directly use the `tla2tools` JAR file.

If inclined to follow this, the scripts for using it are available and described under `Zenith/`.

>**Note:** Certain specification also declare model checking metrics (like state space size, diameter, etc.). In the particular case of verification times, these numbers heavily depend on the *single threaded* throughput of your processor of choice. Since `ZENITH` is a rather large specification, checking liveness properties dominates the verification time in the end, which can only be done on a single thread with TLC.

----
# SIGCOMM Artifact / Citation
The paper describing `ZENITH` was published in ACM SIGCOMM'25 and the artifact resides in a different repository. It can be found [here](https://github.com/USC-NSL/zenith-ae).
```bib
@inproceedings{10.1145/3718958.3750533,
author = {Namyar, Pooria and Ghavidel, Arvin and Zhang, Mingyang and Madhyastha, Harsha V. and Ravi, Srivatsan and Wang, Chao and Govindan, Ramesh},
title = {ZENITH: Towards A Formally Verified Highly-Available Control Plane},
year = {2025},
isbn = {9798400715242},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/3718958.3750533},
doi = {10.1145/3718958.3750533},
booktitle = {Proceedings of the ACM SIGCOMM 2025 Conference},
pages = {409–433},
numpages = {25},
keywords = {software defined networking, formal methods, availability},
location = {S\~{a}o Francisco Convent, Coimbra, Portugal},
series = {SIGCOMM '25}
}
```

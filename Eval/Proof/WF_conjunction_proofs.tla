---- MODULE WF_conjunction_proofs ----
EXTENDS TLAPS, zenith

\* In Zenith, Weak Fairness of all actions is assumed, but in the TLA+ specification,
\* it is only stated for `Next` and individual processes.
\* Because of how `pc` variable is defined, we have the following theorem:
\*
\* ```
\*     For any PlusCal process `proc`, where the next state predicate of `proc`
\*     consists of the disjunction of actions A1, A2, ..., Am, only one action
\*     at most is enabled at any time.
\* ```
\*
\* The plain english version of this theorem is that it is impossible for a correct
\* PlsusCal algorithm to have the `pc` variable of a single process be in more than
\* one label at once.
\*
\* This means that for every process of choice, if an action Ai is enabled, then all
\* other actions Aj such that i # j _MUST_ be disabled, or equivalently, any Aj
\* action such that i # j will remain dissabled, unless an Ai action occures.
\* With the above, we can invoke the WF/SF conjunction rule to assert that Weak/Strong
\* fairness of a process, carries to its individual actions as well (see [1], section
\* 8.5.3 for the statement and proof of this rule).
\*
\* To our knowledge, the theorem above isn't stated formally in any sources that we
\* know of (PlusCal is rarely used with TLAPS, at least for now), however, the informal
\* statement of this property appears in [2], section 5.10.1.
\*
\* TLAPS has poor support for PlusCal, thus an equivalent of this theorem is not
\* anywhere to be found, however, proving it is extremely tedious as well, thus we
\* will omit the proof for these theorems.
\*
\* References:
\*  [1] Leslie Lamport, Specifying Systems (`https://lamport.azurewebsites.net/tla/book-21-07-04.pdf`)
\*  [2] Leslie Lamport, A PlusCal User's, Manual P-Syntax Version 1.8 (`https://lamport.azurewebsites.net/tla/p-manual.pdf`)

====
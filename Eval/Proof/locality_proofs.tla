--------------------------- MODULE locality_proofs ---------------------------
EXTENDS TLAPS, Zenith

\* `Locality` lemmas are lemmas that state that certain actions always leave certain
\* variables unchanged. These lemmas allow us to formally do away with certain steps
\* that trivially remain certain invariants unchanged.
\* These lemmas are either for processes or whole modules:
\*  - Process Lemmas: If a certain process takes no steps, then certain variables are unchanged
\*  - Module Lemmas: If a certain module (i.e. set of processes) take no steps, then certain variables are unchanged

LEMMA SwitchProcessLocality == ~SwitchProcessStep => UNCHANGED swProcessLocals
PROOF OMITTED

LEMMA SwitchFailureLocality == ~SwitchFailureStep => UNCHANGED swFailureProcLocals
PROOF OMITTED
  
LEMMA SwitchResolveLocality == ~SwitchResolveStep => UNCHANGED swResolveFailureLocals
PROOF OMITTED

LEMMA NIBEHProcessLocality == ~NIBEHStep => UNCHANGED rcNibEventHandlerLocals
PROOF OMITTED

LEMMA TEProcessLocality == ~TEStep => UNCHANGED controllerTrafficEngineeringLocals
PROOF OMITTED

LEMMA BOSSProcessLocality == ~BOSSStep => UNCHANGED controllerBossSequencerLocals
PROOF OMITTED

LEMMA SEQProcessLocality == ~SEQStep => UNCHANGED controllerSequencerLocals
PROOF OMITTED

LEMMA WPProcessLocality == ~WPStep => UNCHANGED controllerWorkerThreadsLocals
PROOF OMITTED

LEMMA EHProcessLocality == ~EHStep => UNCHANGED controllerEventHandlerLocals
PROOF OMITTED

LEMMA MSProcessLocality == ~MSStep => UNCHANGED controllerMonitoringServerLocals
PROOF OMITTED

LEMMA SwitchModuleLocality == ~SwitchModuleActions => UNCHANGED swModuleVariables
PROOF OMITTED

LEMMA RCModuleLocality == ~RCModuleActions => UNCHANGED rcModuleVariables
PROOF OMITTED

LEMMA OFCModuleLocality == ~OFCModuleActions => UNCHANGED ofcModuleVariables
PROOF OMITTED

=============================================================================
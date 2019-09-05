# Ivy proofs

This repository contains proofs of SCP's safety property (isolate
protocol.safety in SCP-safety.ivy) and of SCP's liveness properties. The
liveness proof consists of the auxiliary safety invariants proved in
SCP-safety.ivy (isolates `protocol.safety_2` and `protocol.safety_3`), and
lemmas proved in `SCP-liveness-1.ivy`, `SCP-liveness-prepare-1.ivy`,
, `SCP-liveness-prepare-2.ivy`, and
`SCP-liveness-3.ivy`.

* In `SCP-liveness-1.ivy` we prove that if a ballot is long enough and all
  nodes in the quorums of intact nodes are timely, then all intact nodes agree
  on what is confirmed prepared by the end of the ballot.
* In `SCP-liveness-prepare-1.ivy` and `SCP-liveness-prepare-2.ivy`, we prove
  that if all intact nodes agree on what is confirmed prepared before a ballot
  b, then they all propose the same value and this value cannot be contradicted
  in previous ballots. We prove this in two small steps.
* In `SCP-liveness-3.ivy` we prove that if intact nodes all prepare the same
  value in a long-enough ballot, and if this value is not contradicted in
  previous ballots, then all intact nodes confirm the value as committed by the
  end of the ballot.

Together, those three lemmas show that SCP is guaranteed to produce a decision
if given two long-enough consecutive ballots in which all quorums of intact
nodes are timely.

# Isabelle/HOL proofs

We prove in Isabelle/HOL that:
* The union of two intersecting intact sets is intact; this means that maximal
  intact sets are disjoint, and that an FBA system is a collection of disjoint
  maximal intact sets.
* The cascade theorem holds.

To browse and check FBA.thy, use [Isabelle 2019](https://isabelle.in.tum.de/).
The file `output/document.pdf` is a PDF version of FBA.thy.

# Installing and using Ivy

To check the proofs with Ivy, use the following fork, developed by Oded Padon:
[Oded's fork](https://github.com/odedp/ivy).

Clone [Oded's fork](https://github.com/odedp/ivy), create a Python 2.7
virtualenv to work in, install the z3-solver package with pip, and then run
`python setup.py install`. To check `my_file.ivy`, run `ivy_check complete=fo
my_file.ivy`. To set the random seed to something random (using bash on linux):
`ivy_check complete=fo seed=$RANDOM my_file.ivy`.

# Background material to understand the model and proofs

To understand the model and safety proofs: Padon, Oded, et al. "Paxos made EPR:
decidable reasoning about distributed protocols." Proceedings of the ACM on
Programming Languages 1.OOPSLA (2017): 108.

To understand the liveness proofs:

* Padon, Oded, et al. "Temporal prophecy for proving temporal properties of
  infinite-state systems." 2018 Formal Methods in Computer Aided Design
  (FMCAD). IEEE, 2018.
* Padon, O., Hoenicke, J., Losa, G., Podelski, A., Sagiv, M., & Shoham, S.
  (2017). Reducing liveness to safety in first-order logic. Proceedings of the
  ACM on Programming Languages, 2(POPL), 26.

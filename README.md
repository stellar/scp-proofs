# Ivy proofs

This repository contains proofs of SCP's safety property (isolate protocol.safety in SCP-safety.ivy) and of SCP's liveness properties.
The liveness proof consists of the auxiliary safety invariants proved in SCP-safety.ivy, and the two lemmas proved in SCP-liveness-1.ivy and SCP-liveness-2.ivy.
To check the proofs with Ivy, use the following fork, developed by Oded Padon: [Oded's fork](https://github.com/odedp/ivy).

# Isabelle/HOL proofs

To check FBA.thy, use [Isabelle 2019](https://isabelle.in.tum.de/).

# Installing and using Ivy

Clone [Oded's fork](https://github.com/odedp/ivy), create a Python 2.7 virtualenv, install the z3-solver package with pip, and then run `python setup.py install`.
To check `my_file.ivy`, run `ivy_check complete=fo my_file.ivy`. To set the random seed to something random (using bash on linux): `ivy_check complete=fo seed=$RANDOM my_file.ivy`.

# Background material to understand the model and proofs

To understand the model and safety proofs:
Padon, Oded, et al. "Paxos made EPR: decidable reasoning about distributed protocols." Proceedings of the ACM on Programming Languages 1.OOPSLA (2017): 108.

To understand the liveness proofs:

* Padon, Oded, et al. "Temporal prophecy for proving temporal properties of infinite-state systems." 2018 Formal Methods in Computer Aided Design (FMCAD). IEEE, 2018.
* Padon, O., Hoenicke, J., Losa, G., Podelski, A., Sagiv, M., & Shoham, S. (2017). Reducing liveness to safety in first-order logic. Proceedings of the ACM on Programming Languages, 2(POPL), 26.

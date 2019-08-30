# Ivy proofs

This repository contains proofs of SCP's safety property (isolate protocol.safety in SCP-safety.ivy) and of SCP's liveness properties.
The liveness proof consists of the auxiliary safety invariants proved in SCP-safety.ivy, and the two lemmas proved in SCP-liveness-1.ivy and SCP-liveness-2.ivy.
To check the proofs with Ivy, use the following fork, developed by Oded Padon: [Oded's fork](https://github.com/odedp/ivy).

# Isabelle/HOL proofs

To check FBA.thy, use [Isabelle 2019](https://isabelle.in.tum.de/).

# Installing and using Ivy

Clone [Oded's fork](https://github.com/odedp/ivy), create a Python 2.7 virtualenv, install the z3-solver package with pip, and then run `python setup.py install`.
To check `my_file.ivy`, run `ivy_check complete=fo my_file.ivy`. To set the random seed to something random (using bash on linux): `ivy_check complete=fo seed=$RANDOM my_file.ivy`.


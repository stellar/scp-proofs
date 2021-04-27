This directory contains a model for a very simple FBAS.

# Description of the network

* Any majority set is a quorum slice as long as it contains the node itself.
* In other words, `Q(v_i) = { U | |U| >= N / 2 + 1 }`.
* No Byzantine failure.

Run `make proof` and Ivy verifies that the invariants specified in `proof.ivy` hold after initialization and any exported actions.

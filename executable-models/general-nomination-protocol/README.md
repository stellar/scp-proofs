This directory contains a nomination protocol model of a network possibly containing Byzantine nodes.

Run `make proof` and Ivy verifies that the invariants specified in `proof.ivy` hold after initialization and any exported actions.

# Abstractions

The code is largely identical to [the general federated voting model](https://github.com/stellar/scp-proofs/tree/master/executable-models/model-6)
As mentioned in model 6, the abstractions are heavily influenced by, if not identical to, the [the abstractions used by Giuliano Losa](https://github.com/stellar/scp-proofs#the-model).
For more information, see [model-6/READEME.md](https://github.com/stellar/scp-proofs/tree/master/executable-models/model-6)

# Nomination Protocol

The nomination protocol described in the white paper is fairly similar to federated voting.
The differences between federated voting and the nomination protocol that is captured in this model:

- Inability to vote for a value after confirming a value.
- Inability to vote for a value unless
    - the node has heard a leader vote for it already, OR
    - the node considers itself as a leader.

This model's leader relation is more general than that of the white paper.
In the white paper, each node considers exactly one node (itself or another node) as their leader.
However, in this model, at any time, a node may consider any number of nodes (itself or another node) as their leaders and it may add more leaders during the protocol.

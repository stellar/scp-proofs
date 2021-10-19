This directory contains a model for an abstract ballot protocol.

# Description of the network

* There are four nodes.
* `Q(v_i) = {{v_i, v_j, v_k} | i != j, i != k, k != j}`.
* There is no Byzantine failure.

# How to use this
There are three ways to use this model. Executable model, fuzz testing, and verification.
Note: Unfortunately, the executable model and fuzz testing do not work due to the enumerative type in the model.
See [the issue filed on the Ivy repo](https://github.com/kenmcmil/ivy/issues/16).

1. Executable model
    * Run `make && ./executable` to start a REPL environment.
      You can invoke actions to manually examine the model.
      For instance, `node.vote_prepare(0, 1)` makes `Node 0` vote `prepare(Ballot 1)`.
2. Fuzz testing
    * Note: Unfortunately, this is currently not working due to the enumerative type in the model.
      See https://github.com/kenmcmil/ivy/issues/16
    * Run `make && ./fuzz`.
      Ivy randomly generates a valid sequence of actions.
      You can pass the seed as a command line argument. (e.g., `./fuzz seed=123`)
3. Formal verification
    * Run `make proof` and Ivy verifies that the invariants specified in `proof.ivy` hold after initialization and any exported actions.
    * Specifically, it checks that all intact nodes commit the same value.

# Implementation details

* Nodes, quorums and v-blocking sets are all hard-coded.
* Each node can take any of `confirm_nominate`, `vote_prepare`, or `vote_commit`.
    * `confirm_nominate` corresponds to confirming `nominate(value)`.
      This means that the node has been running the nomination protocol,
      and it confirmed a new value.
    * `vote_prepare` corresponds to voting `prepare(ballot)`.
      The node is allowed to perform this action only if it makes sense.
      (e.g., The value in the ballot is the same as the latest output of the nomination protocol.)
    * `vote_commit` corresponds to voting `commit(ballot)`.
      The node can only perform this action only if it makes sense.
      (e.g., The node must have already confirmed `prepare(ballot)`.)
* The network can choose to deliver any `{vote, accept}_{prepare, commit}` messages as long as it makes sense to do so.
    * Messages may be reordered.
    * Upon receiving a message, the recipient tries to accept and/or confirm appropriate statements.

# Difference between this model and the concrete ballot protocol (CBP for short)
You might notice that much of the logic of this model doesn't resemble that of the CBP.
This is because the model is fairly abstract.
One can perform the exact sequence of actions of the CBP by calling appropriate actions of this model in appropriate order.
Thus this model does prove some properties of the CBP.

Examples:
* `PREPARE v i b p p' c.n h.n D` in the CBP encodes a host of conceptual statements as mentioned in Figure 17 of the white paper.
  This can be achieve by invoking `deliver_vote_prepare`, `deliver_accept_prepare`, `deliver_vote_commit` with appropriate values.
* Step 9 of the CBP specifies a condition in which the node must update the ballot counter.
  This can be done by calling `vote_prepare` appropriately.

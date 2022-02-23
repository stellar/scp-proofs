This directory contains a model for an abstract ballot protocol.

# Description of the network

* There are four nodes, `v_0, v_1, v_2, v_3`.
* `Q(v_i) = {{v_i, v_j, v_k} | i != j, i != k, k != j}`.
* `v_3` is Byzantine.

# How to use this
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

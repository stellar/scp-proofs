This directory contains a model for a very simple FBAS.

# Description of the network

* There are four nodes.
* `Q(v_i) = { S | S \subset {0, 1, 2, 3}, |S| = 3, v_i \in S }`.
* Node 0, 1, and 2 are well-behaved and Node 3 is a Byzantine node.
    * Implications:
        * Node 3 may alter its state variables at any point
            * e.g., It may change `heard_vote` even if it hasn't heard the vote.
        * Node 0, 1, and 2 are all well-behaved and intact since {0, 1, 2} is a quorum.

# How to use this
There are three ways to use this model. Executable model, fuzz testing, and verification.

1. Executable model.
    * Run `make && ./executable` to start a REPL environment.
      You can invoke actions to manually examine the model.
      For instance, `node.vote(0, 1)` makes node 0 vote for statement 1.
2. Fuzz testing
    * Run `make && ./fuzz`.
      Ivy randomly generates a sequence of actions.
      You can pass the seed as a command line argument. (e.g., `./fuzz seed=123`)
3. Formal verification
    * Run `make proof` and Ivy verifies that the invariants specified in `proof.ivy` hold after initialization and any exported actions.

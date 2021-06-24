This directory contains a model for the nomination protocol.

# Description of the network

* There are two nodes.
* `Q(v_0) = Q(v_1) = {{ v_0, v_1}}`.
* There is no Byzantine failure.
* Any node may become any node's leader.

# How to use this
There are three ways to use this model. Executable model, fuzz testing, and verification.

1. Executable model.
    * Run `make && ./executable` to start a REPL environment.
      You can invoke actions to manually examine the model.
      For instance, `node.vote(0, 1)` makes node 0 vote to nominate statement 1.
2. Fuzz testing
    * Run `make && ./fuzz`.
      Ivy randomly generates a sequence of actions.
      You can pass the seed as a command line argument. (e.g., `./fuzz seed=123`)
3. Formal verification
    * Run `make proof` and Ivy verifies that the invariants specified in `proof.ivy` hold after initilization and any exported actions.
    * Specifically, it checks that all intact nodes have the same candidate values.

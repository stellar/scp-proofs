This directory contains an experiment in directly connecting Ivy to stellar-core's SCP implementation,
such that Ivy can act upon (and randomly test) the SCP state machine, crypto, messages, nodes and qsets.

# Classes

- `executable` is the main class.
- `Network` class represents the network.
    - `mNodeIDs` stores the list of nodes, and
    - `mBroadcastEnvelopes` stores the list of broadcast messages.
        - Each node is free to receive any of the messages in the given list.
        - `TestSCP::emitEnvelope` appends a message here.
    - `gNetwork` represents the global network.
- `object node` in `executable.ivy` leads to a list of `node`'s for each `id_t`.
  For instance, if there are 4 `id_t`'s, then we would have 4 `node`'s.
  One might think that Ivy would create a class called `node` and an array of 4 `node`'s.
  However, Ivy does NOT do that.
  Ivy will create a 4-element array for each member variable of `node` instead.
  For instance, instead of `nodes[node_id].voted_nominate[statement_id]`, you would check `voted_nominate[node_id][statement_id]`.
- `TestSCP` is a subclass of `SCPDriver` containing the `SCP` class as a member variable.

# How Ivy actions get translated into C++

- Each `export action` in `executable.ivy` corresponds to two things in `executable.cpp`:
    - A method of the `executable` class
        - This is exactly the same as the Ivy action.
        - If the Ivy action contains C++ code, it just gets pasted in here, with any appropriate text substitution.
    - A subclass of `gen`
        - This subclass contains two methods:
            - `generate`
                - Takes an `executable` object.
                - Consults Z3 and checks if it’s possible to take this `action` on the given `executable`.
                - If so, it finds an appropriate argument and stores it.
            - `execute`
                - Takes an `executable` object.
                - Runs the corresponding `action` on the given `executable` object with the arguments `generate` found.
- Each `import action` in `executable.ivy` generates two important items in `executable.cpp`:
    - A method of the `executable` class
        - This is exactly the same as the Ivy action.
        - If the Ivy action contains C++ code, it just gets pasted in here, with any appropriate text substitution.
    - Function object for a callback (`thunk__*`)
        - The constructor takes an `executable` object and a variable.
        - The `()` operator takes extra variables and call the `action` on the `executable` object.

# How callbacks work

Here is an example:

1. Calling an action `receive_pending_envelope` in `executable.ivy` leads to `receiveEnvelope(env)` on `SCP`.
2. In `executable.cpp`, this gets translated into `executable`'s `ext__node__receive_pending_envelope`.
3. `SCP::receiveEnvelope` calls `Slot::processEnvelope`
4. If you keep following this, you might end up calling `emitEnvelop`. (e.g., inside `BallotProtocol::sendLatestEnvelope()`.)
5. And `emitEnvelope` is defined in `TestSCP` since `TestSCP` is a subclass of `SCPDriver`!
6. `emitEnvelope` contains `(*mEmitEnvelopeCb)(envNum);`.
7. And this is the callback. `mEmitEnvelopeCb` is a pointer to the function object `thunk__node__emit_envelope`, which calls the corresponding `action` on the executable object.
8. This is an example where events within `SCP`, which the Ivy code can’t directly see, can indirectly call an `action` in the Ivy code.

# Misc

- Because `SLOT = 0`, it only closes the first slot.

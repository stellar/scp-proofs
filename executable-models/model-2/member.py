nodeCount = 3

print("member(V, S) := false;")
for nodeId in range(nodeCount):
    for setId in range(1<<nodeCount):
        if ((setId >> nodeId) & 1) == 1:
            print("member({}, {}) := true;".format(nodeId, setId))
print()

print("is_quorum(S) := false;")
for setId in range(1<<nodeCount):
    if bin(setId).count("1") >= 2:
        print("is_quorum({}) := true;".format(setId))

print()

print("is_v_blocking(V, S) := true;")
for nodeId in range(nodeCount):
    for setId in range(1<<nodeCount):
        if ((setId >> nodeId) & 1) == 0 and bin(setId).count("1") <= 1:
            # If the set doesn't contain the node AND the set isn't the majority.
            # Then such a set is not v-blocking.
            print("is_v_blocking({}, {}) := false;".format(nodeId, setId))

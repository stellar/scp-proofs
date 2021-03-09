def isMajority(bitmask, nodeCount):
    return 2 * bin(bitmask).count("1") > nodeCount


def contains(bitmask, node):
    return ((bitmask >> node) & 1) == 1


def concatRelationPairs(ls):
    return "|".join(ls)


def memberFormat(nodeId, setId):
    return "(X=v{}&S={})".format(nodeId, setId)


def getMemberRelations(nodeCount):
    members = []
    for nodeId in range(nodeCount):
        for setId in range(1 << nodeCount):
            if contains(setId, nodeId):
                members.append(memberFormat(nodeId, setId))
    return concatRelationPairs(members)


def quorumFormat(setId):
    return "(S={})".format(setId)


def getQuorums(nodeCount):
    quorums = []
    for setId in range(1 << nodeCount):
        if isMajority(setId, nodeCount):
            quorums.append(quorumFormat(setId))
    return concatRelationPairs(quorums)


def vBlockingFormat(nodeId, setId):
    return "(X=v{}&S={})".format(nodeId, setId)


def getNonVBlockingRelations(nodeCount):
    nonVBlockingPairs = []
    for nodeId in range(nodeCount):
        for setId in range(1 << nodeCount):
            if not contains(setId, nodeId) and not isMajority(setId, nodeCount):
                # If the set does NOT the node AND the set is NOT the majority,
                # such a set is NOT v-blocking.
                nonVBlockingPairs.append(vBlockingFormat(nodeId, setId))
    return concatRelationPairs(nonVBlockingPairs)


template = """\
    relation member(X:id_t, S:set_t)
    definition member(X:id_t, S:set_t) =
        {}

    relation is_quorum(S:set_t)
    definition is_quorum(S:set_t) =
        {}

    relation is_v_blocking(X:id_t, S:set_t)
    definition is_v_blocking(X:id_t, S:set_t) =
        ~({})"""


def main():
    count = 3
    print(template.format(getMemberRelations(count),
                          getQuorums(count), getNonVBlockingRelations(count)))


if __name__ == "__main__":
    main()

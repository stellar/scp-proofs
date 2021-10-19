def isMajority(bitmask, nodeCount):
    return 2 * bin(bitmask).count("1") > nodeCount


def contains(bitmask, node):
    return ((bitmask >> node) & 1) == 1


def concatRelationPairs(ls):
    return "|".join(ls)


def memberFormat(nodeId, setId):
    return "(X={}&S={})".format(nodeId, setId)


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
    return "(X={}&S={})".format(nodeId, setId)


def isVBlocking(nodeId, setId, nodeCount):
    if contains(setId, nodeId):
        return True
    universeSetId = (1 << nodeCount) - 1
    complement = universeSetId - setId
    if isMajority(complement, nodeCount):
        # If the complement is a majority,
        # it means that the complement contains a quorum.
        # Therefore, setId is not v-blocking.
        return False
    return True


# Print non-v-blocking relations instead of v-blocking relations
# since there's fewer of them.
def getNonVBlockingRelations(nodeCount):
    nonVBlockingPairs = []
    for nodeId in range(nodeCount):
        for setId in range(1 << nodeCount):
            if not isVBlocking(nodeId, setId, nodeCount):
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
    count = 4
    print(template.format(getMemberRelations(count),
                          getQuorums(count), getNonVBlockingRelations(count)))


if __name__ == "__main__":
    main()

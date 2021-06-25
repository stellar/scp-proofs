This directory contains a model for an FBAS possibly containing Byzantine nodes.

Run `make proof` and Ivy verifies that the invariants specified in `proof.ivy` hold after initialization and any exported actions.

# Abstractions

The abstractions used in this model are heavily influenced by, if not identical to, the [the abstractions used by Giuliano Losa](https://github.com/stellar/scp-proofs#the-model).

More specifically, we will consider any set of nodes with the notion of quorums, blocking sets, and intact nodes that satisfy the axioms:

1. Intact nodes are well-behaved.
1. The intersection of two quorums of intact nodes contains an intact node.
1. The set of intact nodes is a quorum.
1. [Cascade theorem] If `U` is a quorum of an intact node and if all intact members of `U` have accepted `val`, then either all intact nodes have accepted `val`, or there is an intact node `n` such that `n` has not accepted `val` and `n` is blocked by a set of intact nodes that have all accepted `val`.
1. If an intact node is blocked by a set of nodes `S`, then `S` contains an intact node.

And we consider any set `V` that satisfies the 5 statements above.

It is important to emphasize that we consider any configuration as long as they satisfy the statements above, and we do not consider other concepts.
Specifically, quorums are not defined in terms of quorum slices and any sets can block any nodes as long as they satisfy the 5 axioms.

Of course, this abstraction makes sense only if all the statements above are indeed in correct in the white paper, and the following is a sketch of a proof for each.

# Proofs

Let `B` be the set of befouled nodes.
Due to quorum intersection, B is a DSet by Theorem 3.

## Intact nodes are well-behaved.

This is true by the definition of intactness.

## The intersection of two quorums of intact nodes contains an intact node.

By the definition of a DSet, the given FBAS enjoys quorum intersection despite B.
In other words, the intersection of two quorums of intact nodes contains an intact node.

## The set of intact nodes is a quorum.

Since `B` is a DSet, the given FBAS enjoys quorum availability despite `B` by the definition of a DSet.
Quorum availability despite `B` means `V = B` or `V \ B` is a quorum in `<V, Q>`.
In the first case, all nodes are befouled.
In the second case, the set of all intact nodes is a quorum.

## Cascade theorem

This is almost identical to Theorem 10.
The only difference is that Theorem 10 assumes`U ⊂ S` and we assume `(U \ B) ⊂ S` here.
However, the proof for Theorem 10 only uses the fact that `(U \ B) ⊂ S`, anyway.

## If an intact node is blocked by a set of nodes `S`, then `S` contains an intact node.

Let `v` be an intact node.
`V \ B` is a quorum since the given FBAS enjoys quorum availability despite `B`.
Clearly, `V \ B` contains `v`.
Thus `v` has a quorum slice that consists only of intact nodes.
Therefore, any set consisting only of befouled nodes can't block `v`.
Hence, any `v`-blocking set must contain befouled nodes.


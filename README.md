# Ivy proofs

This repository contains proofs of SCP's safety property (isolate
protocol.safety in SCP-safety.ivy) and of SCP's liveness properties. The
liveness proof consists of the auxiliary safety invariants proved in
SCP-safety.ivy (isolates `protocol.safety_2` and `protocol.safety_3`), and
lemmas proved in `SCP-liveness-1.ivy`, `SCP-liveness-prepare-1.ivy`,
, `SCP-liveness-prepare-2.ivy`, and
`SCP-liveness-3.ivy`.

* In `SCP-liveness-1.ivy` we prove that if a ballot is long enough and all
  nodes in the quorums of intact nodes are timely, then all intact nodes agree
  on what is confirmed prepared by the end of the ballot.
* In `SCP-liveness-prepare-1.ivy` and `SCP-liveness-prepare-2.ivy`, we prove
  that if all intact nodes agree on what is confirmed prepared before a ballot
  b, then they all propose the same value and this value cannot be contradicted
  in previous ballots. We prove this in two small steps.
* In `SCP-liveness-3.ivy` we prove that if intact nodes all prepare the same
  value in a long-enough ballot, and if this value is not contradicted in
  previous ballots, then all intact nodes confirm the value as committed by the
  end of the ballot.

Together, those three lemmas show that SCP is guaranteed to produce a decision
if given two long-enough consecutive ballots in which all quorums of intact
nodes are timely.

# Isabelle/HOL proofs

FBA.thy contains a formalization of the notion of intact set, to which the
safety and liveness properties of SCP apply. Informally, a set *I* is intact
when (a) *I* is a quorum, and (b) even if all nodes outside *I* are faulty, any
two quorums of members of *I* intersect.

Given this definition, we prove that:
* The cascade theorem holds.
* The union of two intersecting intact sets is intact; this means that maximal
  intact sets are disjoint, and that an FBA system is a collection of disjoint
  maximal intact sets.

To browse and check FBA.thy with Isabelle, use [Isabelle
2019](https://isabelle.in.tum.de/). The file `output/document.pdf` is a PDF
version of FBA.thy.

# Installing and using Ivy

To check the Ivy proofs, use the following fork of Ivy, developed by Oded
Padon: [Oded's fork](https://github.com/odedp/ivy).

Clone [Oded's fork](https://github.com/odedp/ivy), create a Python 2.7
virtualenv to work in, install the z3-solver package with pip, and then run
`python setup.py install`. To check `my_file.ivy`, run `ivy_check complete=fo
my_file.ivy`. To set the random seed to something random (using bash on linux):
`ivy_check complete=fo seed=$RANDOM my_file.ivy`.

# Background material to understand the model and proofs

To understand the model and safety proofs: Padon, Oded, et al. "Paxos made EPR:
decidable reasoning about distributed protocols." Proceedings of the ACM on
Programming Languages 1.OOPSLA (2017): 108.

To understand the liveness proofs:

* Padon, Oded, et al. "Temporal prophecy for proving temporal properties of
  infinite-state systems." 2018 Formal Methods in Computer Aided Design
  (FMCAD). IEEE, 2018.
* Padon, O., Hoenicke, J., Losa, G., Podelski, A., Sagiv, M., & Shoham, S.
  (2017). Reducing liveness to safety in first-order logic. Proceedings of the
  ACM on Programming Languages, 2(POPL), 26.

# What is proved with Ivy?

## The model

First, the proofs make statements about a model of SCP written in the Ivy
language, and not about SCP's implementation or SCP's description in the
Whitepaper. This model may not reflect what the reader think SCP is (and what
SCP is may be open to interpretation since there is not agreed-upon formal
specification). One can find the SCP model in all the Ivy files in the
repository (it is duplicated in several files for technical reasons, but when
Ivy's liveness support will be more mature the model should appear only in one
place). This model could in principle be taken as the formal specification of
SCP.

**Caveat 1**: Discrepancies between the SCP model and any other notion of what
SCP is would imply that the statements proved with Ivy may not apply to that
other notion of what SCP is.

The model consists of an initial state and a collection of actions, which are
atomic steps that update the global state of the system. Actions model what
nodes do upon receiving messages or upon timers firing. Each action consists of
preconditions (expressed using `assume` statements) and state updates. An
execution of the model is a sequence of global states, starting with the
initial state, and such that each state is obtained from the preceding state by
applying an action whose preconditions are satisfied. This is an instance of
Lamport's Standard Model, used e.g. in TLA+, which Lamport discusses in his
Turing Award lecture.

Preconditions and state updates are specified using First-Order Logic formulas.
By convention, all unbound upper-case variables are taken to be universally
quantified. For more details about specifying protocols in Ivy (and proving
their safety), see the [Ivy tutorial](https://microsoft.github.io/ivy/).

**Caveat 2:** It is easy to write a model that does nothing, e.g. because the
preconditions of the actions are too strong or even contradictory, and then
prove that there is no safety violation. Such a proof would obviously be
meaningless. In fact, the `change_ballot` action had a contradictory assumption
at some point during the development of the SCP model, which was latter fixed
in commit
[3a403d0](https://github.com/stellar/scp-proofs/commit/3a403d09e85097dafef96f5639f619c4f123a99f).
One way to ensure that the model does do something is to prove liveness
properties, e.g. than in every execution, every intact node eventually decides.
We discuss the liveness of SCP below.

### Abstractions

The SCP model abstracts over several aspects of SCP. First, there is no notion
of slice in the model. Instead, we consider a set of nodes which each have
a set of quorums and a notion of blocking set. We then define intertwined and
intact sets using the following axioms:
1. The intersection of two quorums of intertwined nodes contains a well-behaved
   node.
2. The intersection of two quorums of intact nodes contains an intact node.
3. The set of intact nodes is a quorum.
4. If `Q` is a quorum of an intact node and if all members of `Q` have accepted
   `(b,v)` as prepared, then either all intact nodes have accepted `(b,v)` as
   prepared, or there is an intact node `n` such that `n` has not accepted
   `(b,v)` as prepared and `n` is blocked by a set of intact nodes that have
   all accepted `(b,v)` as prepared. This is an instance of the cascade
   theorem.
5. If an intact node is blocked by a set of nodes `S`, then `S` contains an
   intact node. Properties 4 and 5 are proved in the Isabelle/HOL theory
   `FBA.thy`.

**Caveat 3**: If those axioms are inconsistent (i.e. lead to a contradiction
when taken together), the proofs mean nothing. We verified 4 and 5 in
Isabelle/HOL, but there is no mechanically-checked link between the Ivy axioms
and the Isabelle/HOL theory. Thus there is still the possibility that of
a typo. 

**TODO**: It might be possible to use Ivy to check that the axioms have
a model, which would rule out any inconsistency.

Abstracting slices away may see like a bold step. However, the model still
preserves the most challenging algorithmic aspect of implementing consensus in
a federated Byzantine agreement system, i.e. the fact that the notion of quorum
is different for each participant. What is not captured by the model includes
the fact that quorums are discovered dynamically (nodes know all their quorums
upfront in the model) and that quorums might change during execution as nodes
adjust their slices. However, as argued in the Stellar Whitepaper, the safety
of SCP in the case in which quorums change dynamically is no worse than the
safety of the case in which slices do not change and a node's slices are taken
to be all the slices that it ever uses in the dynamic case. Thus the proof
still gives some assurance about the dynamic case.

Second, the model does not specify the nomination protocol. Instead, we assume
that nomination can return arbitrary values (for proving liveness, we add
temporal assumptions about nomination; see the liveness section).

Finally, there is no notion of real-time in the model. Thus we cannot  make any
statements about the amount of time that things take to happen. Instead, in the
liveness properties and proofs, we make statements using Linear-Time Temporal
Logic (LTL), which allows to express that something eventually happens without
giving any bound on the actual time at which it will happen. As we explain in
the liveness section, some of the liveness assumptions that we make could be
proved from simpler assumptions, thereby increasing our confidence in the
protocol, if we could reason about real-time properties.


## Safety

We prove that intertwined nodes never disagree by providing a collection of
conjectures which, together with the safety property to prove, form an
inductive invariant (i.e. they hold in the initial state and are preserved by
every action).

The key invariants are:
1. A well-behaved node does to accept `(b,v)` as committed unless it confirmed
   `(b,v)` as prepared.
2. A well-behaved node does not accept contradictory statements (where `commit
   (b,v)` and `prepare (b',v')` are contradictory when `b < b'` and `v ≠ v'`.
3. If an intertwined node confirms a statement, then there is a quorum of an
   intertwined node whose well-behaved members accepted that statement.
4. A well-behaved node does not accept different values as prepared in the same
   ballot.

Ivy automatically checks that those invariants, along with the auxiliary
conjectures present in the `safety` isolate in `SCP-safety.ivy`, are inductive.

Given those invariants, we can reason as follows: suppose two differ values `v`
and `v'` are confirmed committed by two intertwined nodes. By Invariant 3,
Invariant 4, and Quorum Intersection, we get that intertwined nodes cannot
confirm two different values as prepared in the same ballot, and thus by
Invariant 1 no two different values are confirmed as committed in the same
ballot.

Now suppose that `v` and `v'` are confirmed committed in ballots `n` and `n'`,
with `n < n'`. By Invariant 1 and Invariant 3, there is a quorum `Q` of an
intertwined node whose well-behaved members all accepted `(n',v')` as prepared.
Thus, by Invariant 2, no well-behaved member of `Q` ever accepts `(n,v)` as
committed. Thus, by Invariant 3 and Quorum Intersection, no intertwined node
confirmed `(n,v)` as committed, which is a contradiction.

Ivy reaches the same conclusion automatically and successfully validates that
the safety property holds.

## Liveness 

TODO: it may be better to start by explaining how SCP decides if all agree on the highest... and there is enough communication.
Then explain the conditions for agreeing on the highest...

In what follow we consider an intact set `I`. 

Informally, SCP relies on two key ingredients to achieve liveness: 
  (a) The ballot-synchronization protocol aims at simulating a synchronous
      system, i.e. a system in which intact nodes proceed from ballot to ballot
      in lock-steps and have the same view of the protocol state by the end of
      each ballot.
  (b) Given two consecutive synchronous ballots, the balloting protocol
      guarantees that all intact nodes reach a decision by the end of the
      second synchronous ballot if all intact nodes agree on their nomination
      output.

This follows the traditional approach pioneered by Dwork, Lynch, and Stockmeyer
in their seminal paper "Consensus in the Presence of Partial Synchrony" (the
DLS paper). 

Analysing the ballot-synchronization protocol to prove that, under some
eventual synchrony conditions, it satisfies (a) requires reasoning about
real-time properties involving message-propagation delay, clock skew, and timer
durations. As pointed out before, our SCP model does not allow reasoning about
such properties. Instead, we assume that there eventually comes a ballot `b0`
such that:
  (1) `b0` and `b0+1` are synchronous, meaning that any message sent by an
      intact node in ballot `b∈{b0,b0+1}` is received by all its recipients by
      the end of ballot `b`.
  (2) all nodes have the same nomination output in ballot `b0+1`. 

From those assumptions, we we discuss after the discussion of the proof, we
prove that all intact nodes confirm a value as committed in ballot `b0+1`. 

## The liveness argument

The main difficulty of this proof is that, since nodes never accept
contradictory statements, SCP could possibly reach a state in which no value
can be accepted as prepared by any quorum because, for every quorum `Q`, `Q`
contains nodes that accepted `v` as committed and other nodes that accepted
`v'≠v` as committed.

A key invariant of SCP prevents this situation from occurring: once a value
is voted committed unanimously by the intact members of a quorum intersecting
`I`, no other value can ever be accepted as prepared by intact nodes. We prove
the key invariant of this paragraph in isolate `safety_2` in the file
`SCP-safety.ivy`.

Given this invariant, it is easy to see that a value must be confirmed as
committed in `b0+1`: Since `b0` is synchronous, by the cascade theorem, all
intact nodes agree on the highest confirmed prepared value they see. If (a)
there is such a value `v`, then by the key invariant it cannot be contradicted
in ballot `b0` and below, and thus, since `b0+1` is synchronous, `v` is
confirmed committed in `b0+1`. If (b) no value is confirmed prepared by intact
nodes by the end of ballot `b0`, then any value `w` will remain un-contradicted
for the duration of `b0+1`; otherwise, this would mean that a value is accepted
as committed in a ballot `b≤b0`, in which case it must be confirmed prepared in
ballot `b≤b0`, which contradicts (b). In particular, the nomination output `vn`
of the nodes, on which they all agree, is not contradicted during `b0+1` and
thus, because `b0+1` is synchronous, `vn` is confirmed committed by the end of
`b0+1`.

By the key invariant, if `v` is the first value to be accepted as committed by
an intact node (say in ballot `bv`), then no other values `v'≠v` can ever be
accepted as committed in the future by an intact node (because that would
require accepting it as prepared first, which violates the invariant). By the
same key invariant, this value `v` will also be the highest confirmed prepared
value among intact nodes from ballot `bv` onwards. Thus, if a value is accepted
as committed by an intact node by the start of ballot `b0`, then that value is
confirmed committed by the end of `b0+1`.

## Discussion of the assumptions

### The synchrony assumption

Assumption (1) holds in an eventually synchronous system without faulty nodes.
However, as we now discuss, faulty nodes can cause intact nodes to violate
assumption (1) even if communication is timely and reliable between intact
nodes. Suppose that a value `v` is missing only faulty node's votes to reach
quorum threshold in some ballot. Then faulty nodes can send votes for `v` that
complete a quorum to a single intact node right before intact node's timers for
the round (in the ballot-synchronization protocol) are about to expire. The
target intact node is then likely to send an accept message right before the
intact's node timers expire, and its message likely does not reach all intact
nodes before they leave the ballot.

This can create a live-lock in which intact nodes never decide because they
always disagree on the highest confirmed prepared value. For example, consider
a system of 4 nodes `n1`, `n2`, `n3`, and `n4` where `n4` is the unique faulty
node.

To prevent this scenario, it must be the case that any node appearing in
a quorum of an intact node is non-faulty and timely, i.e quorums of intact
nodes must not contain any faulty node and, if they contain non-intact
well-behaved nodes, those must be timely. In practice, nodes must therefore
closely monitor the timing of nodes in their quorums and modify their slices to
eventually arrive at a configuration such that quorums of intact nodes contain
only timely well-behaved nodes.

### The nomination assumption

Assumption (2) states that all intact nodes agree on their nomination output in `b0+1`.

The justification for this assumption is that nomination uses probabilistic
leader-election which, with non-zero probability, elects a unique intact
leader. Therefore an intact leader is eventually unanimously elected by all
intact nodes, which leads to agreement on the nomination output.


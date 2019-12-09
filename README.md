This is a repository containing formal proofs about the Stellar Consensus
Protocol as described in the paper "Fast and secure global payments with
Stellar" (SOSP 2019).

With Isabelle/HOL, we formalize Federated Byzantine Agreement Systems (FBAS) and
we prove the cascade theorem and that the union of two intact sets is intact.

With Ivy, we formalize SCP in a high-level, non-executable specification, and
we prove that intact sets never disagree (SCP's main safety property) and that,
under some assumptions, every member of an intact set eventually commits
a value (SCP's main liveness property).

# Isabelle/HOL proofs

FBA.thy contains a formalization of the notion of intact set. Informally, a set
*I* is intact when (a) *I* is a quorum, and (b) even if all nodes outside *I*
are faulty, any two quorums of members of *I* intersect.

We prove that:
1. The cascade theorem holds: if `I` is an intact set, `Q` is a quorum of
   a member of `I`, and `Q⊆S`, then either `I⊆S` or there is a member of `I−S`
   that is blocked by `S∩I`.
2. The union of two intersecting intact sets is intact. This implies that
   maximal intact sets are disjoint.

Two major difference with the Stellar Whitepaper are that:
1. We do not assume that the FBAS enjoys quorum intersection. Thus there may be
   disjoint intact sets that diverge but nevertheless remain internally safe
   and live. Point 2 above implies that maximal intact sets are disjoint, and
   that an FBA system is a collection of disjoint maximal intact sets.
2. We use a new, more abstract definition of quorum for the analysis. A quorum
   is a set `Q` such that all well-behaved members of `Q` have a slice in `Q`.

Note that the new definition of quorum only relies on the slices of
well-behaved nodes, which seems natural since faulty nodes can arbitrarily
change their slices, whereas the original definition of quorum used the slices
of faulty nodes too.

We use this new definition of quorum only for the analysis of the system. In
reality, nodes do not know who is faulty and thus cannot use this new
definition of quorum, and instead just check for sets whose members all have
a slice inside the set. The abstraction we make here is safe because any set
that is deemed a quorum by a node in reality is also a quorum in the abstract
definition that we use for our analysis. Moreover, the two definitions coincide
exactly when we consider only well-behaved nodes.

To browse and check FBA.thy with Isabelle, use [Isabelle
2019](https://isabelle.in.tum.de/). The file `output/document.pdf` is a PDF
version of FBA.thy.

## Comments on the Isabelle/HOL proofs

The proofs do not follow the presentation of the Stellar Whitepaper. They are
simpler due to the reformulation of the notion of quorum. 

To prove the cascade theorem, we assume by contradiction that `I` is not
a subset of `S` but no member of `S−I` is blocked by `S∩I`. In this situation,
we note that `I−S` is a quorum of a member of `I` in the projection of the
system on `I`. Moreover, `Q` is also a quorum of a member of `I` in the
projection of the system on `I`. Thus, by the quorum intersection property of
`I`, `Q` and `I−S` must intersect. This is clearly impossible since `Q` is
a subset of `S`, and we have reached a contradiction.

To prove that the union of two intersecting intact set is intact, we reason as
follows. Take two intersecting intact sets `I₁` and `I₂`. First, note that
`I₁∪I₂` is trivially a quorum, and thus we have quorum availability. 

It remains to show that `I₁∪I₂` enjoys quorum intersection. Take a set `Q₁`
that is a quorum of a member of `I₁` in the system projected on `I₁∪I₂` and
a quorum `Q₂` that is a quorum of a member of `I₂` in the system projected on
`I₁∪I₂`. We must show that `Q₁` and `Q₂` intersect in `I₁∪I₂`. First note that
`I₂` is a quorum in the system projected on `I₁` and, by assumption,
`I₁∩I₂≠{}`. Moreover, `Q₁` is a quorum in the system projected on `I₁` and `I₁`
is intact. Thus, by the quorum intersection property of intact sets, (a) `I₂`
and `Q₁` intersect. Moreover, (b) both `Q₁` and `Q₂` are quorums in the system
projected on `I₂`. Because `I₂` is intact, by the quorum intersection property,
we get from (a) and (b) that `Q₁` and `Q₂` intersect in `I₂`, and we are done. 

# Ivy proofs

This repository contains Ivy proofs of SCP's safety property (isolate
protocol.safety in SCP-safety.ivy) and of SCP's liveness properties. The
liveness proof consists of the supporting safety invariants proved in
`SCP-safety.ivy` (isolates `protocol.safety_2` and `protocol.safety_3`) and
`SCP-safety-2.ivy`, and lemmas proved in `SCP-liveness-cascade.ivy`,
`SCP-liveness-prepare.ivy`, and `SCP-liveness-3.ivy`.

* In `SCP-liveness-cascade.ivy` we prove that, in an arbitrary given ballot, if
  all intact nodes vote to prepare the same value `v` and the ballot lasts long
  enough, then all intact nodes confirm `v` as committed.
* In `SCP-liveness-prepare.ivy`, we prove
  that if all intact nodes agree on what is confirmed prepared before a ballot
  `b`, and their nomination output is the same, then they all vote to propose
  the same value in `b`.
* In `SCP-liveness-3.ivy` we prove that if intact nodes all prepare the same
  value in a long-enough ballot, then all intact nodes confirm the value as
  committed by the end of the ballot.

As we discuss below, together, those three lemmas show that SCP is guaranteed
to produce a decision if given two long-enough consecutive ballots in which all
quorums of intact nodes are timely.

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
 
The liveness properties of SCP follow from the cascade theorem and from a key
safety property: (P1) if there is a quorum-of-intact `Q` whose intact members
all vote to commit `(b,v)`, then no value different from `v` is accepted as
prepared in later ballots. Property P1 rules out scenarios where nodes would
not be able to accept any new statements because past accepted contradictory
statements prevent them from accepting any new statement. We prove Property P1
in the isolate `safety_2` of `SCP-safety.ivy`. Relying on Property P1, we
formally prove two liveness properties that we now discuss.

In what follows, we always assume as a baseline that communication between
intact nodes is reliable (i.e. messages are never lost) but can take an
arbitrary amount of time.

Ballot-based protocols like SCP are usually live assuming a variant of eventual
synchrony. That, we assume that, eventually, the system stabilizes in some way.
For example, we might assume that the communication delay between intact nodes
eventually becomes bounded by a constant. Given such an assumption, one way to
prove the liveness of ballot-based protocols like SCP is to first prove that,
eventually, the ballot-synchronization mechanism simulates a synchronous system
in which intact nodes go from ballot to ballot in lock-steps and all receive
the same messages in a given ballot. Then, assuming that ballots eventually
become synchronous, we prove that the protocol terminates. This is roughly the
approach pioneered by Dwork, Lynch, and Stockemeyer in their seminal work
"Consensus in the presence of partial synchronony", and we also take this
approach.

We formally prove two liveness properties L1 and L2 that depend on assumptions
about the ballot-synchronization protocol; then, we informally argue that,
assuming that the ballot-synchronization protocol eventually ensures synchrony,
L1 and L2 guarantee that after two synchronous ballots all intact nodes have
confirmed a value committed. We do not formally analyse the
ballot-synchronization protocol. Doing so would require reasoning about
real-time properties involving message-propagation delay, timeout values, etc.
which is not possible with the first-order model of SCP that we use here. See
the SOSP paper for an informal discussion of the ballot-synchronization
protocol.

The first property we prove is that, (L1) if there is ever a ballot `b1` such that
(a) all intact nodes vote to prepare the same value `v` in `b1` and (b) `b1` lasts long
enough, then all intact nodes confirm `v` as committed in `b1` (regardless of
what faulty nodes do). This is not as trivial as it may seem because a node
accepts a new statement only if it has not already accepted anything
contradictory. Thus, contradictory accepted statements could prevent `v` from
being confirmed committed in `b1`. To rule out this possibility, we first prove
that if all intact nodes vote to prepare the same value `v` in `b1`, then no
intact node has or ever accepts `commit (b,v)` where `v≠v1` and `b≤b1`. In
other words, `v1` is never contradicted in ballots preceding `b1`. This holds
because, if `(b,v)`, with `b≤v1` and `v≠v1` is accepted as committed, then
there is a quorum-of-intact `Q` whose intact members all voted to commit
`(b,v)` before leaving ballot `b`. Therefore, by Property P1, no other value
can be confirmed as prepared in ballots higher than `b`, and thus one intact node
must have confirmed `(b,v)` as prepared before entering `b1`. Therefore, at least
one intact node has `(b,v)` as highest confirmed prepared value when entering
`b1`, and this node must therefore vote to prepare `v` in `b1`. This
contradicts the assumption that all intact nodes vote to prepare `v1` where
`v1≠v`. Now that we have established that `prepare (b1,v1)` cannot be
contradicted, it should be clear that given enough time for all messages sent
from intact nodes to intact nodes to be delivered, `(b1,v1)` is eventually
confirmed as committed (note that there is no need for the cascade theorem for
this, because the set of intact nodes is a quorum for all intact nodes).
We formally prove Property L1 in `SCP-liveness-3.ivy`.

It remains to show if and under what circumstances we can guarantee that there
will come a ballot `b1` such that all intact nodes vote to prepare the same
value in `b1`. Using the cascade theorem and Property P1, we show that (L2)
once an intact node accepts a value `v` as prepared in `b0`, then all intact
nodes eventually accept it as prepared and then commit it prepared. The key for
this proof is showing that the cascading effect is not blocked by contradictory
accepted statements, again using Property P1. The contrapositive of Property P1
is that if `prepare (b0,v)` is confirmed, then no value `v'≠v` can be accepted
as committed in ballots lower than `b0`. Therefore, once an intact nodes
accepts a value `v` as prepared in `b0`, `prepare (b0,v)` cannot be
contradicted and, by the cascade theorem, all intact nodes eventually accept it
as prepared and then commit it prepared.
We formally prove Property L2 in `SCP-liveness-cascade.ivy`.

Liveness Property L2 shows that, if, eventually, no new values are ever
confirmed prepared by any intact nodes, then, eventually, all intact nodes
agree on what is confirmed prepared. Thus, barring interference from non-intact
nodes, if ballots become synchronous and keep increasing in duration, there
will come a ballot that is long enough enough for all intact nodes to agree on
what is confirmed prepared by the end of the ballot. It easily follows,
assuming that nomination has converged, that all intact nodes vote to prepare
the same value in the next ballot (this is proved formally in
`SCP-liveness-prepare.ivy`), and that, by Liveness Property L1, all intact
nodes confirm a value committed in the next ballot.

Unfortunately, non-intact nodes can always interfere right before the end of
a ballot and cause disagreement on what is confirmed prepared among intact
nodes: a non-intact node can always withhold an "accept prepare" message right
until the end of a ballot (either because it is faulty or because it has bad
timing) and complete a quorum just before the ballot ends, and thereby cause
some intact nodes to confirm the corresponding value as prepared while others
do not. Thus, to ensure that all intact nodes vote to prepare the same
value in the next ballot, intact nodes must adjust their slices to make sure
that no faulty or otherwise untimely node remain in any of their quorums.

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
in commit 3a403d0. One way to ensure that the model does do something is to
prove liveness properties, e.g. than in every execution, every intact node
eventually decides. We discuss the liveness of SCP below.

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

TODO

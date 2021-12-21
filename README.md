NOTE: For the old proofs, checkout commit `803b345`. The repository at this
commit contains a full liveness proof. However, being written in Ivy 1.6, it
has a lot of hacks. The current, newer version of this repository contains
proofs written in Ivy 1.7.

This is a repository containing formal proofs about the Stellar Consensus
Protocol as described in the paper "Fast and secure global payments with
Stellar" (SOSP 2019).

Using Isabelle/HOL, we formalize the theory of Federated Byzantine Agreement
Systems (FBAS) and we prove two main results: the cascade theorem and that the
union of two intact sets is intact.

Using Ivy, we formalize SCP in a high-level, non-executable specification, and
we prove that members of intertwined sets never disagree (SCP's main safety
property) and some liveness properties.

# Isabelle/HOL proofs

FBA.thy contains a formalization of the notion of intact set. Roughly speaking,
a set *I* is intact when (a) *I* is a quorum, and (b) even if all nodes outside
*I* are faulty, any two quorums of members of *I* intersect.

We prove that:
1. The cascade theorem holds: if `I` is an intact set, `Q` is a quorum of
   a member of `I`, and `Q⊆S`, then either `I⊆S` or there is a member of `I−S`
   that is blocked by `S∩I`.
2. The union of two intersecting intact sets is intact. This implies that
   maximal intact sets are disjoint.

Note that there two major differences compared to the treatment in the Stellar
Whitepaper:
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

There is also a maintained version of the theory of FBAS and more in the
Archive of Formal Proofs:
<https://devel.isa-afp.org/entries/Stellar_Quorums.html>.

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

This repository contains a proof of SCP's safety property in Ivy (isolate
protocol.intertwined_safety in SCP.ivy) and of some of SCP's liveness properties.

## Running the proofs

To run the proof (that is, to have Ivy check them), run the following commands
(on Linux) from the root of this repository:
```
docker-compose build ivy-check
docker-compose run ivy-check
```

## Background material to understand the model and proofs

To understand the model and safety proofs: Padon, Oded, et al. "Paxos made EPR:
decidable reasoning about distributed protocols." Proceedings of the ACM on
Programming Languages 1.OOPSLA (2017): 108.
Available [here](https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=&cad=rja&uact=8&ved=2ahUKEwjp9Z3xuvX0AhXKGTQIHbfEBEIQFnoECA4QAw&url=https%3A%2F%2Farxiv.org%2Fabs%2F1710.07191&usg=AOvVaw0ffPhJjdMi3okPA41gShmn)

To understand the liveness proofs:

* Padon, Oded, et al. "Temporal prophecy for proving temporal properties of
  infinite-state systems." 2018 Formal Methods in Computer Aided Design
  (FMCAD). IEEE, 2018.
* Padon, O., Hoenicke, J., Losa, G., Podelski, A., Sagiv, M., & Shoham, S.
  (2017). Reducing liveness to safety in first-order logic. Proceedings of the
  ACM on Programming Languages, 2(POPL), 26.

## What is proved with Ivy?

### The model

First, the proofs make statements about a model of SCP written in the Ivy
language, and not about SCP's implementation or SCP's description in the
Stellar Whitepaper. This model may not reflect what the reader think SCP is
(and what SCP is may be open to interpretation since there is not agreed-upon
formal specification). The model in `SCP.ivy` could in principle be taken as
the formal specification of SCP.

**Caveat 1**: Discrepancies between the SCP model and any other notion of what
SCP is would imply that the statements proved with Ivy may not apply to that
other notion of what SCP is.

The model consists of an initial state and a collection of actions, which are
atomic steps that update the global state of the system. Actions model what
nodes do upon receiving messages or upon timers firing. Each action consists of
preconditions (expressed using `require` statements) and state updates. An
execution of the model is a sequence of global states, starting with the
initial state, and such that each successive state is obtained from the
preceding state by applying an action whose preconditions are satisfied. This
is an instance of Lamport's Standard Model, used e.g. in TLA+, which Lamport
discusses in his Turing Award lecture.

Preconditions and state updates are specified using First-Order Logic formulas.
Note that, by convention, all free upper-case variables are taken to be
universally quantified. For more details about specifying protocols in Ivy (and
proving their safety), see the [Ivy tutorial](https://microsoft.github.io/ivy/).

**Caveat 2:** It is easy to write a model that does nothing, e.g. because the
preconditions of the actions are too strong or even contradictory, and, in this
case, any proof if meaningless. One way to ensure that the model does do
something is to prove liveness properties. For example, we might want to prove
that, in every eventually synchronous execution, every intact node eventually
decides. We discuss the liveness of SCP below.

#### Abstractions

The SCP model abstracts over several aspects of SCP. First, there is no notion
of quorum slice in the model. Instead, we consider a set of nodes which each
have a set of quorums and a notion of blocking set. We then define intertwined
and intact sets using the following axioms:
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
when taken together), the proofs are meaningless. We verified 4 and 5 in
Isabelle/HOL, but there is no mechanically-checked link between the Ivy axioms
and the Isabelle/HOL theory. Thus there is still the possibility that of
a typo.

**TODO**: It should be possible to use Ivy to check that the axioms have
a model, which would rule out any inconsistency.

Abstracting slices away may see like a bold step. However, the model still
preserves the most challenging algorithmic aspect of implementing consensus in
a federated Byzantine agreement system, i.e. the fact that the notion of quorum
is different for each participant. What is not captured by the model includes
the fact that quorums are discovered dynamically (nodes know all their quorums
upfront in the model) and that quorums might change during execution as nodes
adjust their slices (quorums are fixed upfront in the model).

Second, the model does not specify the nomination protocol. Instead, we assume
that nomination can return arbitrary values, which is sound.

Finally, there is no notion of real-time in the model. Thus we cannot  make any
statements about the amount of time that things take to happen. Instead, in the
liveness properties and proofs, we make statements using Linear-Time Temporal
Logic (LTL), which allows to express that something eventually happens without
giving any bound on the actual time at which it will happen. As we explain in
the liveness section, some of the liveness assumptions that we make could be
proved from simpler assumptions, thereby increasing our confidence in the
protocol, if we could reason about real-time properties.

### Safety

We prove that intertwined nodes never disagree by providing a collection of
invariants which, together with the safety property to prove, form an
inductive invariant (i.e. they hold in the initial state and are preserved by
every action).

The key invariants are:
1. A well-behaved node does not accept `(b,v)` as committed unless it confirmed
   `(b,v)` as prepared.
2. A well-behaved node does not accept contradictory statements (where `commit
   (b,v)` and `prepare (b',v')` are contradictory when `b < b'` and `v ≠ v'`.
3. If an intertwined node confirms a statement, then there is a quorum of an
   intertwined node whose well-behaved members accepted that statement.
4. A well-behaved node does not accept different values as prepared in the same
   ballot.

Given those invariants, suppose that `v` and `v'` are confirmed committed in
ballots `n` and `n'`, with `n < n'`. By Invariant 1 and Invariant 3, there is
a quorum `Q` of an intertwined node whose well-behaved members all accepted
`(n',v')` as prepared. Thus, by Invariant 2, no well-behaved member of `Q` ever
accepts `(n,v)` as committed. Thus, by Invariant 3 and Quorum Intersection, no
intertwined node confirmed `(n,v)` as committed, which is a contradiction.

Using the auxiliary conjectures present in the `safety` isolate in
`SCP-safety.ivy`, Ivy reaches the same conclusion automatically and
successfully validates that the safety property holds.

### Liveness

We would like to prove that SCP guarantees that, under eventual synchrony,
every intact node eventually decides. Unfortunately, this does not hold, and
SCP guarantees the following, weaker liveness property: if the system is
eventually synchronous and non-intact nodes eventually stop taking steps, then
every intact node eventually decides.

To prove the liveness property, we can proceed in two steps.
* L1: by the end of a long-enough synchronous ballot in which non-intact nodes
  do not take steps, every intact node agrees on the highest confirmed-prepared
  value.
* L2: if a quorum unanimously votes to prepare a value `v` during a long-enough
  synchronous ballot, then every intact node decides `v` by the end of the
  ballot.

Note that, if intact nodes agree that the highest confirmed-prepared value is
`v`, then they all vote for `v`. Thus, once ballots become synchronous and
Byzantine nodes stop taking step, properties L1 and L2 together imply that all
intact nodes decide.

Let us know informally argue why properties L1 and L2 hold. In each cases, the
main threat is the fact nodes do not accept contradictory values, and this
could block progress. In both cases, we rule out progress being blocked in this
way using additional invariants proved in the isolate
`protocol.additional_safety`.

To see why property L1 holds, assume that an intact node has confirmed `(b,v)`
prepared during a long-enough synchronous ballot. Then, as we prove in `inv2`
in isolate `protocol.additional_safety`, no contradictory statement is ever
accepted by intact nodes. Thus, other intact nodes are never prevented from
accepting `(b,v)` as prepared, and the Cascade Theorem ensures that, given
enough communication, every intact node confirms `(b,v)` as prepared. Thus, if
ballot `b` is long enough, evey intact node confirms `(b,v)` as prepared by the
end of the ballot.

To see  why property L2 holds, assume that every intact node votes to prepare
the same value `v` during a long-enough synchronous ballot `b`. Then, as we
prove in `inv1` in isolate `protocol.additional_safety`, no contradictory
statement is ever accepted by intact nodes. Thus, given enough communication,
nothing prevents value `v` from being accepted prepared, then confirmed
prepared, then accepted committed, and finally confirmed committed by all
intact nodes. Thus, if ballot `b` is long enough, every intact node confirms
`(b,v)` as prepared by the end of the ballot.

#### What liveness properties are proved in Ivy?

An old version of this repository (commit `803b345`) contains a full liveness
proof. However, this old proof is written in Ivy 1.6 and contains many hacks.
The current repository uses Ivy 1.7 and contains cleaner liveness proofs.
However, we have so far only ported the proof of the following statement: if
a quorum of an intact node unanimously accepts `(b,v)` as prepared, then
eventually all intact nodes accept `(b,v)` as prepared. This roughly
corresponds to property L1.

#### Liveness in practice

Unfortunately, Byzantine nodes can always interfere right before the end of
a ballot and cause disagreement on what is confirmed prepared among intact
nodes and make L1 fail. More precisely, a Byzantine node can always withhold an
"accept prepare" message right until the end of a ballot (either because it is
faulty or because it has bad timing) and complete a quorum just before the
ballot ends, and thereby cause some intact nodes to confirm the corresponding
value as prepared while others do not.

In practice, to ensure that all intact nodes vote to prepare the same value in
the next ballot, intact nodes must adjust their slices to make sure that no
faulty or otherwise untimely node remain in any of their quorums.

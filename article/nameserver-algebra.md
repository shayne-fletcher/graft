# Nameserver

This note develops an algebra of namespace replication over a tree of processes. The Haskell alongside realizes it — properties checking the laws, a demo witnessing the examples. The setting: processes form a rooted tree of parent–child links; each process is named by a *PID* (opaque, flat, proved by certificate); each child *publishes* to its parent a directory of the processes in its subtree, and keeps that publication alive only as long as the link that carries it. An entry in a directory holds identity metadata and a *locator* — the adjacent next hop toward its process, rewritten at every level so each holder sees its own first edge.

## The Directory

A parent's directory is the merge of its own entry with its children's committed publications.

Merge must survive the network: publications arrive duplicated and in any order. So merging twice must equal merging once, and neither order nor grouping may change the result — idempotent, commutative, associative. Snapshots, deltas, and sequence numbers are encoding; this insensitivity is the contract.

An entry pairs identity metadata with an address; a directory is a finite partial map from PIDs to slots. A slot is either a claimed entry or `Contested`, marking a disputed claim. The partiality is semantic: "no entry" is a state in its own right — merged with any slot, it yields that slot unchanged.

Realized:

```haskell
data Entry addr = Entry
  { info :: Info,
    locator :: addr
  }

data Slot addr
  = Claimed (Entry addr)
  | Contested

newtype Directory addr
  = Directory (Map Pid (Slot addr))

merge :: Eq addr => Directory addr -> Directory addr -> Directory addr
merge (Directory a) (Directory b) =
  Directory (Map.unionWith joinSlot a b)

joinSlot :: Eq addr => Slot addr -> Slot addr -> Slot addr
joinSlot (Claimed e) (Claimed e') | e == e' = Claimed e
joinSlot _ _ = Contested
```

That `Contested` absorbs under merge is a law shape alone cannot express; the property suite is where it lives.

Three collapses from the setting. Real identity metadata (a TLS name, labels) becomes one opaque `Info`: data carried through unchanged, never inspected. The prioritized address list becomes one locator: dialing order is mechanism. And `addr` is a type parameter: nothing here depends on what an address is.

For `α`, take:

```haskell
data NextHop = Self | Parent | Child Pid
```

A locator held at a node can only ever denote that node itself, its parent, or one of its children — so the type says so. `Parent` needs no PID because a node has exactly one. And because a `NextHop` is meaningful only from where its holder stands, an entry cannot be forwarded without being rewritten into the receiver's frame — a discipline the implementation maintains by care, forced here by the type.

The laws are inherited pointwise. `Map.unionWith joinSlot` is associative, commutative, and idempotent exactly when `joinSlot` is, so each directory law reduces to a per-slot fact, and a PID present in only one directory passes through untouched — absence means no information, not denial. QuickCheck properties in the repo confirm the lift; the mathematics lives in the three lines of `joinSlot`.

In normal operation PIDs are disjoint and `joinSlot` never runs. When it does run, only two things can happen:

```text
joinSlot s s   = s ;
joinSlot (Claimed e) (Claimed e') = Contested ,   if e ≠ e' .
```

The first is a duplicate: merging twice is merging once. The second is a dispute, and the algebra declines to referee it — no winner, only the fact of disagreement. Two children's claims are never equal, for commit stamped each with the child it came through; a dispute always takes the second branch.

A parent cannot forbid what its children send. So the bad state is named rather than banned: `Contested` should never arise, and the simulator will prove it never does.

## A small example

A gateway's view, built from its own entry and the committed publication of one child, a worker:

```haskell
gateway, worker :: Pid
gateway = Pid 2
worker = Pid 5

own, published, view :: Directory NextHop
own = singleton gateway (Entry (Info "gateway") Self)
published = singleton worker (Entry (Info "worker") (Child worker))
view = merge own published
```

Printed (wrapped for the page):

```haskell
>>> view
Directory
  (fromList
     [ (Pid 2, Claimed (Entry {info = Info "gateway", locator = Self})),
       (Pid 5, Claimed (Entry {info = Info "worker", locator = Child (Pid 5)}))
     ])
```

Read it back: the gateway is here (`Self`), and the worker is reached through the worker (`Child (Pid 5)`). Delivering the publication a second time changes nothing: `merge view published == view`. And a second child claiming the worker's PID contests the slot even with identical metadata — its entry carries a different `Child` stamp:

```haskell
imposter = singleton worker (Entry (Info "worker") (Child (Pid 3)))
```

```haskell
>>> merge view imposter
Directory
  (fromList
     [ (Pid 2, Claimed (Entry {info = Info "gateway", locator = Self})),
       (Pid 5, Contested)
     ])
```

The gateway's own slot is untouched; the worker's is contested, and stays that way. The model passes this verdict:

```haskell
data Health = Sound | Disputed (Set Pid)
```

`health view` is `Sound`; `health (merge view imposter)` is `Disputed {Pid 5}`. A disputed PID yields no claim — unreachable, not arbitrarily routed — and `Sound` is the judgment the simulator must later prove every well-formed run keeps.

These equalities run as tests in the repo.

## The algebra

We merge directories, and we must tolerate duplicated messages. A duplicate means the same PID arrives on both sides of a merge, so slots get compared against slots — and the slot rule makes everything explicit: equal claims pass through, anything else is `Contested`. That rule is a join, and it creates a little lattice:

```text
⊥  ≤  Claimed _  ≤  Contested
```

`⊥` is "no entry", at the bottom because it changes nothing it meets; distinct claims sit side by side, neither below the other; `Contested` is on top because it absorbs every other term.

Directory merge is this join applied per PID, plus union of the key sets. So `Directory addr` is a join-semilattice, ordered by `d ≤ d'` when `merge d d' == d'` — `d` adds nothing to `d'`. In the model this is `leq`, and the property suite checks the laws.

A slot climbs this lattice and never descends; `Contested` keeps no memory of the claims, only of their disagreement. Forward-only is the right law for learning and the wrong one for failure: when a link dies its entries must go, and no merge can remove them — nor does `view` remember which link `published` came through. Links supply the provenance and the license to shrink. They are next.

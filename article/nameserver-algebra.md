# Nameserver

This note develops an algebra of namespace replication over a tree of processes. The Haskell alongside realizes it — properties checking the laws, a demo witnessing the examples. The setting: processes form a rooted tree of parent–child links; each process is named by a *PID* (opaque, flat, proved by certificate); each child *publishes* to its parent a directory of the processes in its subtree, and keeps that publication alive only as long as the link that carries it. An entry in a directory holds identity metadata and a *locator* — the adjacent next hop toward its process, rewritten at every level so each holder sees its own first edge.

The construction proceeds in two layers. `Directory` and `Links` establish a flat per-link publication model: a parent retains one committed publication per admitted child link and derives a view from them. `Tree` then refines what each link publishes so nested failure domains remain visible and can be finalized explicitly.

## The Directory

A parent's directory is the merge of its own entry with its children's committed publications.

A node combines several committed contributions, and that fold must not depend on their order or grouping. Repeating the same contribution must also change nothing. Directory merge is therefore idempotent, commutative, and associative. Snapshots, deltas, and sequence numbers decide which contribution from a link is current; merge combines those current contributions.

An entry pairs identity metadata with an address; a directory is a finite partial map from PIDs to slots. A slot is either a claimed entry or `Contested`, marking a disputed claim. The partiality is semantic: "no entry" is a state in its own right — merged with any slot, it yields that slot unchanged.

The snippets use the package's `GHC2024` language edition. Realized:

```haskell
import Data.List (foldl')
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

newtype Pid = Pid Int
  deriving (Show, Eq, Ord)

newtype Info = Info String
  deriving (Show, Eq)

data Entry addr = Entry
  { info :: Info,
    locator :: addr
  }
  deriving (Show, Eq)

data Slot addr
  = Claimed (Entry addr)
  | Contested
  deriving (Show, Eq)

newtype Directory addr
  = Directory (Map Pid (Slot addr))
  deriving (Show, Eq)

empty :: Directory addr
empty = Directory Map.empty

singleton :: Pid -> Entry addr -> Directory addr
singleton pid entry = Directory (Map.singleton pid (Claimed entry))

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
  deriving (Show, Eq)
```

A locator held at a node can only ever denote that node itself, its parent, or one of its children — so the type says so. `Parent` needs no PID because a node has exactly one. And because a `NextHop` is meaningful only from where its holder stands, an entry cannot be forwarded without being rewritten into the receiver's frame — a discipline the implementation maintains by care, forced here by the type.

The laws are inherited pointwise. `Map.unionWith joinSlot` is associative, commutative, and idempotent exactly when `joinSlot` is, so each directory law reduces to a per-slot fact, and a PID present in only one directory passes through untouched — absence means no information, not denial. QuickCheck properties in the repo confirm the lift; the mathematics lives in the three lines of `joinSlot`.

In normal operation PIDs are disjoint and `joinSlot` never runs. When it does run, only two things can happen:

```text
joinSlot s s   = s ;
joinSlot (Claimed e) (Claimed e') = Contested ,   if e ≠ e' .
```

The first is a duplicate: merging twice is merging once. The second is a dispute, and the algebra declines to referee it — no winner, only the fact of disagreement. Two children's claims are never equal, for commit stamped each with the child it came through; a dispute always takes the second branch.

`Contested` makes conflicting ownership explicit rather than leaving `merge` partial. A well-formed protocol must prevent such a publication from becoming active, giving the simulator a precise invariant to check: every reachable view is `Sound`.

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
  deriving (Show, Eq)

contested :: Directory addr -> Set Pid
contested (Directory entries) =
  Map.keysSet (Map.filter isContested entries)
  where
    isContested Contested = True
    isContested (Claimed _) = False

health :: Directory addr -> Health
health directory
  | Set.null disputes = Sound
  | otherwise = Disputed disputes
  where
    disputes = contested directory
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

```haskell
leq :: Eq addr => Directory addr -> Directory addr -> Bool
leq d d' = merge d d' == d'
```

A slot climbs this lattice and never descends; `Contested` keeps no memory of the claims, only of their disagreement. Forward-only is the right law for learning and the wrong one for failure: when a link dies its entries must go, and no merge can remove them — nor does `view` remember which link `published` came through. Links supply the provenance and the license to shrink. They are next.

## Links

A merged directory is only a derived view. The parent must retain each link's publication separately so it can withdraw that link's contribution later. `Contested` records only that distinct claims existed; it does not retain them. If one link later closes, the merged value alone cannot recover the claim from the link that remains live.

The parent keeps each child link's committed publication separately. A `LinkId` identifies one admitted lifetime of that relationship. Reconnection receives a fresh ID, so work admitted under an earlier lifetime cannot update its replacement.

The model records that distinction directly:

```haskell
newtype LinkId = LinkId Int
  deriving (Show, Eq, Ord)

data Attachment addr
  = Admitted Pid
  | Live Pid (Directory addr)
  | Finalized Pid
  deriving (Show, Eq)

newtype LinkTable addr
  = LinkTable (Map LinkId (Attachment addr))
  deriving (Show, Eq)
```

Admission and publication are separate transitions. Admission creates the link before it has an active publication; the first successful commit supplies that baseline. Consequently, an admitted link and a link that has committed an empty directory are different states even though neither contributes an entry to the visible view. The abstract transitions are:

```text
absent                     -- admit child ----------> Admitted child
Admitted child             -- commit publication ---> Live child first
Live child old             -- commit publication ---> Live child new
Admitted/Live child        -- finalize -------------> Finalized child
```

Publication here denotes the semantic effect of a committed update, not its wire encoding. A snapshot replaces the link's current publication, while a delta updates that publication through removals and upserts; the algebra retains only the resulting complete directory. For materialization, that directory replaces `old`; it is not merged with `old`. This is where state may shrink: a newer publication may omit a process whose descendant link failed, and retaining the old claim would keep that process reachable. A publication protocol may use sequence numbers to handle gaps and repeated messages. After it accepts an update, this model keeps only the resulting current directory for that link and merges it with the current directories from other links.

Finalizing a link terminates its publication lifetime and withdraws its complete contribution. Another publication under that `LinkId` is rejected, while replaying the finalizer changes nothing. The same child may attach again only with a fresh `LinkId`. `Finalized` retains the terminal fact while the algebra needs it; the tree model will make explicit how that finalizer is disseminated and then collected.

The visible directory is rebuilt from the local contribution and every published link:

```haskell
mapLocators :: (a -> b) -> Directory a -> Directory b
mapLocators f (Directory entries) = Directory (fmap mapSlot entries)
  where
    mapSlot (Claimed (Entry entryInfo entryLocator)) =
      Claimed (Entry entryInfo (f entryLocator))
    mapSlot Contested = Contested

materialize :: Directory NextHop -> LinkTable addr -> Directory NextHop
materialize local (LinkTable links) =
  foldl' merge local
    [ mapLocators (const (Child childPid)) childPublication
    | Live childPid childPublication <- Map.elems links
    ]
```

The rewrite is essential. A locator in the child's publication is expressed from the child's position and has no meaning at the parent. From the parent, every process in that publication is reached first through the child, so every claimed locator becomes `Child childPid`. Identity metadata passes through unchanged.

This representation can recover information that the flattened view cannot. Let one live link through the real worker publish the worker's PID. The gateway sees `Claimed worker`. Let a second child link publish the same PID; after their receiver-relative locators are stamped with different children, the gateway sees `Contested`. Finalize the second link and materialize again: the first link's untouched contribution remains, so the gateway sees `Claimed worker` once more.

```text
link 1 live                         -> Claimed worker via child 5
link 1 live + link 2 live           -> Contested
link 1 live + link 2 finalized      -> Claimed worker via child 5
```

The view changed from `Contested` to `Claimed`, but `merge` itself never removed information. Instead, the parent stopped including the finalized link's publication and recomputed the merge from the links still live. Before finalizing a link, the parent must stop accepting publication updates from its child and stop routing new traffic through that link. It then waits for traffic already using the link to finish. Only after those steps may the parent remove the link's publication from the visible directory. No late update can restore the contribution, and no packet can use a route after its directory entry has disappeared.

The flat model now explains withdrawal across one parent–child link. A child's publication lists all PIDs reachable through it but does not record the descendant links that supplied them. If one of those deeper links fails, the child's next publication simply omits its PIDs. An ancestor sees the removal, but not which failure domain ended or a finalizer that rules out later updates from it. A tree-shaped publication preserves each nested link as a named domain. Its finalizer can travel upward, remove exactly that subtree, and ensure that updates for the old domain are not accepted. A reconnection uses a new domain. Trees are next.

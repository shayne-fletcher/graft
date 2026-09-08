# Nameserver

This note develops an algebra of namespace replication over a tree of processes. The Haskell alongside realizes it — properties checking the laws, a demo witnessing the examples. The setting: processes form a rooted tree of parent–child links; each process is named by a *PID* (opaque, flat, proved by certificate); each child *publishes* to its parent a directory of the processes in its subtree, and keeps that publication alive only as long as the link that carries it. An entry in a directory holds identity metadata and a *locator* — the adjacent next hop toward its process, rewritten at every level so each holder sees its own first edge.

The construction proceeds in two layers. `Directory` and `Links` establish a flat per-link publication model: a parent retains one committed publication per admitted child link and derives a view from them. `Tree` then refines what each link publishes so nested failure domains remain visible and can be finalized explicitly.

## The Directory

A parent's directory is the merge of its own entry with its children's committed publications.

A node combines several committed contributions, and that fold must not depend on their order or grouping. Repeating the same contribution must also change nothing. Directory merge is therefore idempotent, commutative, and associative. Snapshots, deltas, and sequence numbers decide which contribution from a link is current; merge combines those current contributions.

An entry pairs identity metadata with an address; a directory is a finite partial map from PIDs to slots. A slot is either a claimed entry or `Contested`, marking a disputed claim. The partiality is semantic: "no entry" is a state in its own right — merged with any slot, it yields that slot unchanged.

In Haskell:

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

For the executable model, instantiate `addr` as `NextHop`:

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

`LinkTable` preserves one level of provenance: it records which immediate child link supplied each flat publication. The publication itself still collapses every deeper link into one directory. To preserve provenance at every level, apply the same structure recursively: a live contribution contains that child process's own entry and a table of its child contributions. That recursive link table is a tree.

## Trees

The flat model stores one whole-subtree `Directory` for each live child. The tree model replaces that directory with a `Summary (Directory ())`:

```text
flat contribution:
  Directory { entries from this node and every descendant }

tree contribution:
  Live {
    local = Directory { this process's PID ↦ its own entry },
    children = Forest { one Summary for each child domain }
  }
  or Finalized
```

The directory has not disappeared. It has become the local part of a larger value. In a complete nameserver summary, that directory is a singleton containing the entry for the process represented by this domain. Entries for descendant processes move into `Forest`, where each child domain has its own `Summary`. Every live child summary makes the same split between its process's entry and its children; that repetition is the recursion. A finalizer can therefore remove one named subtree without flattening or enumerating it.

The `DomainId` stays with its map entry when the tree is forwarded to an ancestor. It names the same attachment lifetime everywhere that subtree appears and is never reused.

For example, let `A → B → C` mean that A is B's parent and B is C's parent. When C attaches to B, that attachment lifetime receives a domain ID. The examples abbreviate it as `BC`. This is only a readable name for an otherwise opaque ID; it is not a pair of PIDs or a route. B publishes its own subtree to A, with C's subtree nested under the key `BC`. If C disconnects, the later entry `BC ↦ Finalized`—read “domain `BC` maps to `Finalized`”—identifies the same subtree as ended. A reconnection receives a different domain ID, written `BC'`.

The recursive representation is:

```haskell
newtype DomainId = DomainId Int
  deriving (Show, Eq, Ord)

data Summary payload
  = Live payload (Forest payload)
  | Finalized
  deriving (Show, Eq)

newtype Forest payload
  = Forest (Map DomainId (Summary payload))
  deriving (Show, Eq)
```

A published tree has one root domain and may contain one domain for every descendant link lifetime. Each `Live` summary contains a `Forest`: the map of that domain's immediate child domains. Those entries are siblings of one another, but the important relationship is that they are children of the domain containing the forest. Each map entry pairs a child's `DomainId` with the `Summary` for that child domain.

`Summary payload` therefore describes one domain within the larger tree. `Live` contains that domain's local state and the summaries of its child domains. `Finalized` records only that the domain's publication lifetime has ended; its former payload and complete child forest are no longer needed. When a node receives another report for a domain it already knows, live payloads merge, child entries with the same domain ID combine recursively, and `Finalized` replaces the live state. The enclosing map supplies the domain ID, so `Summary` does not repeat it.

For the nameserver, substitute `Directory ()` for `payload`. In a complete live summary, this directory has one key: the PID of the process represented by that domain. Its value is that process's own entry. A later partial update may use the empty directory when that entry has not changed; merging the update into the stored summary retains the existing singleton. The type remains generic because the same recursive structure can carry mergeable state other than a nameserver directory.

A nameserver tree is well formed only when each PID originates in exactly one live domain. An implementation must reject or explicitly represent duplicate ownership; route materialization must never choose between competing domains. The algebra below assumes this invariant without prescribing how it is enforced.

A tree publication deliberately carries no usable locators. The directory carries process identity metadata, while the tree position carries provenance; neither tells the receiver which adjacent process is its next hop. The unit locator in `Directory ()` marks that absence. Materialization turns the tree into the receiver's `Directory NextHop`. For each immediate child—say B—the receiver flattens B's live subtree and assigns every resulting entry the locator `Child B`. At this nameserver instantiation, the projection has this type:

```haskell
materializeThrough ::
  Pid ->
  Summary (Directory ()) ->
  Directory NextHop
```

`NextHop` is the executable model's locator type. A system that routes directly by datagram endpoint would instead supply the immediate child's `DatagramAddr` and materialize `Summary (Directory ())` as `Directory DatagramAddr`.

The implementation below generalizes the input locator type because it replaces every incoming locator regardless of its value.

`Admitted` remains local protocol state before the first publication and does not appear in the published tree.

A published tree has one root domain. Every other domain appears once, in exactly one parent's child map. A finalizer can therefore identify one unambiguous subtree by its `DomainId`.

The flat model treats each accepted publication as the link's new complete directory. The recursive algebra instead permits a receiver to store a complete summary and merge later reports into it. A later report may be sparse: it can use the empty local payload and mention only child domains for which it carries new information. Merging that report preserves every omitted branch, while a child entry set to `Finalized` becomes terminal. The model defines how such reports combine, but not how a sender computes, sequences, or transports them. When a direct attachment ends, its parent marks the corresponding domain `Finalized` and publishes that fact upward. Finalization is now replicated state rather than only a local link-table transition.

### Recursive merge

Two reports for the same `DomainId` merge into one summary. Live summaries merge their local payloads and then merge their child forests by domain ID. A finalizer dominates every live summary for its domain:

```haskell
mergeSummary ::
  Semigroup payload =>
  Summary payload ->
  Summary payload ->
  Summary payload
mergeSummary Finalized _ = Finalized
mergeSummary _ Finalized = Finalized
mergeSummary (Live local children) (Live local' children') =
  Live (local <> local') (children <> children')

mergeForest ::
  Semigroup payload =>
  Forest payload ->
  Forest payload ->
  Forest payload
mergeForest (Forest domains) (Forest domains') =
  Forest (Map.unionWith mergeSummary domains domains')
```

The two uses of `(<>)` select different merge operations from their operand types. For the nameserver payload, `local <> local'` means `merge local local'`. For the child forests, `children <> children'` means `mergeForest children children'`.

Absence from a forest is the bottom value for a domain. A summary from an unknown domain is inserted; summaries with distinct IDs remain separate; summaries with the same ID merge recursively. These merge operations are joins in the information order. If payload merge is associative, commutative, and idempotent, summary and forest merge inherit those laws.

`Finalized` is the greatest value for one domain:

```text
Live payload children  ≤  Finalized
```

Merging a delayed live update after the finalizer therefore still yields `Finalized`. The update cannot restore the domain's payload or descendants. A reconnect does not move backward from `Finalized` to `Live`; it publishes under a fresh domain ID.

### The borrowed view

Nameserver entries are borrowed from the domains that publish them: they remain visible only while every domain on their path is live. Materialization walks the tree, merges the payloads of live domains, and contributes nothing for a finalized domain:

```haskell
flattenSummary :: Monoid payload => Summary payload -> payload
flattenSummary Finalized = mempty
flattenSummary (Live local children) =
  local <> flattenForest children

flattenForest :: Monoid payload => Forest payload -> payload
flattenForest (Forest domains) =
  foldMap flattenSummary (Map.elems domains)

materializeThrough ::
  Eq addr =>
  Pid ->
  Summary (Directory addr) ->
  Directory NextHop
materializeThrough childPid =
  mapLocators (const (Child childPid)) . flattenSummary

materializeForestThrough ::
  Eq addr =>
  Pid ->
  Forest (Directory addr) ->
  Directory NextHop
materializeForestThrough childPid =
  mapLocators (const (Child childPid)) . flattenForest
```

`materializeForestThrough` projects a forest received through one immediate child. It flattens the live domains in that forest and rewrites every resulting locator through that child.

Merging a finalizer adds information to the summary, but its materialized directory is smaller. The receiver recomputes that directory from the updated summary; because a finalized branch contributes `empty`, the branch's entries are absent from the new result. No removal occurs inside `Directory.merge`.

### Three processes

Return to `A → B → C`. Write `AB` for the domain ID of B's attachment to A and `BC` for the domain ID of C's attachment to B. In the displays below, `AB ↦ value` means that a forest maps the domain ID `AB` to `value`; `{ B }` abbreviates a directory containing B's entry; `{}` is an empty child forest; and `⊥` is the empty payload. B publishes this summary to A:

```text
AB ↦ Live {
  local = { B },
  children = {
    BC ↦ Live {
      local = { C },
      children = {}
    }
  }
}
```

At B, C's entry materializes with `Child C` because C is B's immediate child. B does not copy that locator into the tree it sends upward; the payload carries C's identity information with a unit locator. When A receives the tree, it flattens the live `AB` subtree and assigns `Child B` to both B and C. A therefore routes both processes through its own immediate child. The nested `BC` domain preserves C's ownership and failure boundary, not a route from A directly to C.

If C's attachment fails, B merges this sparse update into its summary:

```text
AB ↦ Live {
  local = ⊥,
  children = {
    BC ↦ Finalized
  }
}
```

`⊥` says the update adds nothing to B's local payload. `Finalized` dominates the earlier live `BC` summary, so C and everything beneath it disappear from the materialized directory while B remains. B need not enumerate C's PIDs in order to withdraw them.

If B's attachment fails, A instead merges:

```text
AB ↦ Finalized
```

That one finalizer masks B's complete subtree, including C. If B later reconnects, it receives a fresh domain ID such as `AB'`. A delayed update for `AB` still merges with `Finalized` and contributes nothing; publications under `AB'` belong to the new lifetime.

The Haskell properties check that summary merge is associative, commutative, and idempotent; that `Finalized` dominates every live summary; that child and parent finalization remove the intended borrowed state; and that a late update cannot revive a finalized domain after reconnection.

The algebra retains a finalizer for as long as old summaries might still arrive. Deciding when it may be disseminated and forgotten is a protocol question, not another merge rule. That question is where induced ordering enters.

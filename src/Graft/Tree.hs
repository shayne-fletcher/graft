-- |
-- Module      : Graft.Tree
-- Description : Recursive summaries of attachment-scoped failure domains.
--
-- A flat link table preserves only the immediate link that supplied
-- each directory. A 'Forest' applies the same provenance structure
-- recursively, so a finalizer can identify and mask exactly the
-- subtree whose lifetime has ended.
--
-- Summary state grows by merge. This merge is the join in the
-- replicated information order. Its borrowed projection may shrink:
-- 'Finalized' is above every live summary in the replicated order but
-- contributes nothing to 'flattenSummary'.
module Graft.Tree
  ( -- * Domain identity
    DomainId (..),

    -- * Recursive summaries
    Summary (..),
    Forest,
    emptyForest,
    singletonDomain,
    fromDomains,

    -- * Merge
    mergeSummary,
    mergeForest,

    -- * Borrowed projection
    flattenSummary,
    flattenForest,
    materializeThrough,
    materializeForestThrough,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Graft.Directory
  ( Directory,
    NextHop (Child),
    Pid,
    mapLocators,
  )

-- | One publication lifetime. Reconnection uses a fresh domain ID.
newtype DomainId = DomainId Int
  deriving (Show, Eq, Ord)

-- | The state published for one domain. A live summary carries the
-- domain's local payload and the summaries of its immediate children.
-- Finalization masks both the payload and the complete child forest.
data Summary payload
  = Live payload (Forest payload)
  | Finalized
  deriving (Show, Eq)

-- | Sibling domains keyed by their non-reusable identities. Absence
-- from this map is the bottom value for a domain.
newtype Forest payload = Forest (Map DomainId (Summary payload))
  deriving (Show, Eq)

instance (Semigroup payload) => Semigroup (Summary payload) where
  (<>) = mergeSummary

instance (Semigroup payload) => Semigroup (Forest payload) where
  (<>) = mergeForest

instance (Semigroup payload) => Monoid (Forest payload) where
  mempty = emptyForest

-- | A forest containing no known domains.
emptyForest :: Forest payload
emptyForest = Forest Map.empty

-- | A forest containing one named domain summary.
singletonDomain :: DomainId -> Summary payload -> Forest payload
singletonDomain domain summary = Forest (Map.singleton domain summary)

-- | Build a forest by merging summaries with the same domain ID.
fromDomains :: (Semigroup payload) => [(DomainId, Summary payload)] -> Forest payload
fromDomains = foldMap (uncurry singletonDomain)

-- | Merge two observations of one domain. A finalizer dominates every
-- live summary; live summaries merge their payloads and children.
mergeSummary ::
  (Semigroup payload) =>
  Summary payload ->
  Summary payload ->
  Summary payload
mergeSummary Finalized _ = Finalized
mergeSummary _ Finalized = Finalized
mergeSummary (Live local children) (Live local' children') =
  Live (local <> local') (children <> children')

-- | Merge sibling forests by domain ID. Distinct IDs remain distinct;
-- summaries for the same ID merge recursively.
mergeForest ::
  (Semigroup payload) =>
  Forest payload ->
  Forest payload ->
  Forest payload
mergeForest (Forest domains) (Forest domains') =
  Forest (Map.unionWith mergeSummary domains domains')

-- | Materialize borrowed payload from one domain. Finalized domains
-- and all of their descendants are absent from the result.
flattenSummary :: (Monoid payload) => Summary payload -> payload
flattenSummary Finalized = mempty
flattenSummary (Live local children) = local <> flattenForest children

-- | Materialize borrowed payload from every domain in a forest.
flattenForest :: (Monoid payload) => Forest payload -> payload
flattenForest (Forest domains) = foldMap flattenSummary (Map.elems domains)

-- | Materialize one child's recursive namespace publication in the
-- holder's address frame.
materializeThrough ::
  (Eq addr) =>
  Pid ->
  Summary (Directory addr) ->
  Directory NextHop
materializeThrough childPid =
  mapLocators (const (Child childPid)) . flattenSummary

-- | Materialize several incarnations reached through the same child.
-- Finalized old incarnations contribute nothing; a live replacement
-- uses the same immediate next hop under a fresh domain ID.
materializeForestThrough ::
  (Eq addr) =>
  Pid ->
  Forest (Directory addr) ->
  Directory NextHop
materializeForestThrough childPid =
  mapLocators (const (Child childPid)) . flattenForest

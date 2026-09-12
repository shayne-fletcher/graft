-- |
-- Module      : Graft.Link
-- Description : Link lifetimes and their current publications.
--
-- Directory merge deliberately forgets where equal or competing
-- claims came from. A 'LinkTable' retains that provenance by keeping
-- one current directory publication for every live child link.
--
-- Publication replaces one link's previous contribution. Finalizing
-- the link removes that contribution from the projection and records
-- the terminal fact: a reconnect must use a new 'LinkId'.
module Graft.Link
  ( -- * Link identity
    LinkId (..),

    -- * Link table
    LinkTable,
    LinkError (..),
    emptyLinks,
    attach,
    publish,
    finalize,

    -- * Projection
    materialize,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Graft.Directory
  ( Directory,
    NextHop (Child),
    Pid,
    mapLocators,
    merge,
  )

-- | One admitted incarnation of a parent-child relationship. A link
-- ID is never reused after finalization.
newtype LinkId = LinkId Int
  deriving (Show, Eq, Ord)

-- | The state retained for one link ID. Admission and the first
-- committed publication are distinct states.
data Attachment addr
  = Admitted Pid
  | Live Pid (Directory addr)
  | Finalized Pid
  deriving (Show, Eq)

-- | The state of every admitted link incarnation, including terminal
-- finalizers that prevent an old ID from being reused.
newtype LinkTable addr = LinkTable (Map LinkId (Attachment addr))
  deriving (Show, Eq)

-- | A transition rejected by the link-lifetime state machine.
data LinkError
  = LinkIdCollision LinkId
  | ChildAlreadyAttached Pid
  | UnknownLink LinkId
  | FinalizedLink LinkId
  deriving (Show, Eq)

-- | A link table with no known incarnations.
emptyLinks :: LinkTable addr
emptyLinks = LinkTable Map.empty

-- | Admit one child under a fresh link ID. An exact replay before
-- finalization is harmless; a finalized ID cannot be admitted again.
attach ::
  LinkId ->
  Pid ->
  LinkTable addr ->
  Either LinkError (LinkTable addr)
attach link childPid table@(LinkTable links) =
  case Map.lookup link links of
    Just (Finalized _) -> Left (FinalizedLink link)
    Just existing
      | attachmentChild existing == childPid -> Right table
      | otherwise -> Left (LinkIdCollision link)
    Nothing
      | any (isAttachedChild childPid) (Map.elems links) ->
          Left (ChildAlreadyAttached childPid)
      | otherwise ->
          Right (LinkTable (Map.insert link (Admitted childPid) links))

-- | Replace the current committed publication for one admitted link.
-- The first publication moves the link out of the admitted-only state.
-- Ordering successive replacements belongs to the protocol above this
-- state machine.
publish ::
  LinkId ->
  Directory addr ->
  LinkTable addr ->
  Either LinkError (LinkTable addr)
publish link nextPublication (LinkTable links) =
  case Map.lookup link links of
    Nothing -> Left (UnknownLink link)
    Just (Finalized _) -> Left (FinalizedLink link)
    Just attachment ->
      Right
        ( LinkTable
            ( Map.insert
                link
                (Live (attachmentChild attachment) nextPublication)
                links
            )
        )

-- | Finalize a link and withdraw its complete publication. Replaying
-- finalization is harmless; the terminal ID cannot publish again.
finalize ::
  LinkId ->
  LinkTable addr ->
  Either LinkError (LinkTable addr)
finalize link table@(LinkTable links) =
  case Map.lookup link links of
    Nothing -> Left (UnknownLink link)
    Just (Finalized _) -> Right table
    Just attachment ->
      Right
        ( LinkTable
            -- Map.insert replaces the value because this key already exists.
            (Map.insert link (Finalized (attachmentChild attachment)) links)
        )

-- | Derive the holder's directory from its local contribution and
-- every published child contribution. Admitted and finalized links
-- contribute nothing. All entries learned through a child acquire
-- that child as their next hop.
materialize :: Directory NextHop -> LinkTable addr -> Directory NextHop
materialize local (LinkTable links) =
  foldl'
    merge
    local
    [ mapLocators (const (Child childPid)) childPublication
    | Live childPid childPublication <- Map.elems links
    ]

attachmentChild :: Attachment addr -> Pid
attachmentChild (Admitted childPid) = childPid
attachmentChild (Live childPid _) = childPid
attachmentChild (Finalized childPid) = childPid

isAttachedChild :: Pid -> Attachment addr -> Bool
isAttachedChild childPid (Admitted attachedPid) = childPid == attachedPid
isAttachedChild childPid (Live attachedPid _) = childPid == attachedPid
isAttachedChild _ (Finalized _) = False

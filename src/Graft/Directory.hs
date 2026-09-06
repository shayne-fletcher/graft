-- |
-- Module      : Graft.Directory
-- Description : Directories and their lawful merge.
--
-- A directory is the namespace payload: a map from process identities
-- to entries, each entry carrying inert identity metadata and a
-- locator. Merging directories is the one operation replication
-- needs, and it must be associative, commutative, and idempotent so
-- that duplicated and reordered deliveries cannot corrupt state.
--
-- The algebra is address-generic: a directory is parameterized by its
-- locator address type @addr@, is only ever carried opaquely, and no
-- law depends on what an address is. The pure model instantiates
-- @addr@ with 'NextHop' — an address relative to the holding node.
--
-- A 'Pid' claimed by two different entries is an ownership error, not
-- a conflict to resolve: the slot becomes 'Contested', 'Contested' is
-- absorbing under merge, and no winner is ever chosen.
module Graft.Directory
  ( -- * Identity
    Pid (..),
    Info (..),

    -- * Entries
    Entry (..),
    NextHop (..),

    -- * Directories
    Slot (..),
    Directory (..),
    empty,
    singleton,
    fromList,

    -- * Merge and order
    merge,
    leq,

    -- * Projections
    claimed,
    contested,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)

-- | Process identity: an opaque, flat name. A real mesh derives it
-- from the process's TLS certificate so a peer can prove it.
newtype Pid = Pid Int
  deriving (Show, Eq, Ord)

-- | Inert identity metadata (a TLS server name, labels). Merge and
-- relocation must preserve it; nothing inspects it.
newtype Info = Info String
  deriving (Show, Eq, Ord)

-- | One directory entry: identity metadata plus a locator.
data Entry addr = Entry
  { -- | Identity metadata, preserved by every operation.
    info :: Info,
    -- | Where to go next to reach this entry's process.
    locator :: addr
  }
  deriving (Show, Eq, Ord)

-- | A next hop, relative to the node holding the directory: the node
-- itself, its parent, or one of its children by name. It stands where
-- a real mesh has a carrier address (a UDP endpoint, a Unix socket
-- path) — always the address of an adjacent neighbour, meaningful
-- only from where the holder stands. A shipped locator is therefore
-- meaningless at its receiver until rewritten into the receiver's
-- frame.
data NextHop
  = -- | The entry's process is the holder itself.
    Self
  | -- | The entry's process is reachable through the holder's parent.
    Parent
  | -- | The entry's process lives in the subtree of this child.
    Child Pid
  deriving (Show, Eq, Ord)

-- | A PID's slot in a directory.
data Slot addr
  = -- | Exactly one live claim on this PID.
    Claimed (Entry addr)
  | -- | An ownership error: distinct entries claimed one PID.
    Contested
  deriving (Show, Eq, Ord)

-- | A directory: the visible map from PIDs to slots.
newtype Directory addr = Directory (Map Pid (Slot addr))
  deriving (Show, Eq, Ord)

-- | Merge is the semigroup operation; see 'merge'.
instance (Eq addr) => Semigroup (Directory addr) where
  (<>) = merge

-- | 'empty' is the merge identity.
instance (Eq addr) => Monoid (Directory addr) where
  mempty = empty

-- | The directory with no entries.
empty :: Directory addr
empty = Directory Map.empty

-- | The directory with one claimed entry.
singleton :: Pid -> Entry addr -> Directory addr
singleton p e = Directory (Map.singleton p (Claimed e))

-- | Merge singletons; duplicate PIDs with distinct entries become
-- 'Contested'.
fromList :: (Eq addr) => [(Pid, Entry addr)] -> Directory addr
fromList = foldMap (uncurry singleton)

-- | Join two slots. Equal claims are one claim; distinct claims are
-- an ownership error; 'Contested' absorbs.
joinSlot :: (Eq addr) => Slot addr -> Slot addr -> Slot addr
joinSlot (Claimed e) (Claimed e')
  | e == e' = Claimed e
joinSlot _ _ = Contested

-- | Merge two directories, PID by PID.
--
-- Merge is associative, commutative, and idempotent, so state built
-- by merging is insensitive to duplicated and reordered deliveries.
merge :: (Eq addr) => Directory addr -> Directory addr -> Directory addr
merge (Directory a) (Directory b) = Directory (Map.unionWith joinSlot a b)

-- | The information order induced by merge: @d `leq` d'@ when @d'@
-- already contains everything @d@ says.
leq :: (Eq addr) => Directory addr -> Directory addr -> Bool
leq d d' = merge d d' == d'

-- | The claimed entries of a directory.
claimed :: Directory addr -> Map Pid (Entry addr)
claimed (Directory m) = Map.mapMaybe f m
  where
    f (Claimed e) = Just e
    f Contested = Nothing

-- | The contested PIDs of a directory.
contested :: Directory addr -> Set Pid
contested (Directory m) = Map.keysSet (Map.filter isContested m)
  where
    isContested Contested = True
    isContested (Claimed _) = False

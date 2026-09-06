module Main (main) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Graft.Directory
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests

-- PIDs are drawn from a small pool so that key collisions actually
-- occur; with unconstrained PIDs every collision property would pass
-- vacuously.
genPid :: Gen Pid
genPid = Pid <$> choose (0, 7)

genInfo :: Gen Info
genInfo = Info . pure <$> elements "abcd"

genNextHop :: Gen NextHop
genNextHop = oneof [pure Self, pure Parent, Child <$> genPid]

genEntry :: Gen (Entry NextHop)
genEntry = Entry <$> genInfo <*> genNextHop

genDirectory :: Gen (Directory NextHop)
genDirectory = genDirectoryOver [0 .. 7]

-- | A directory whose PIDs are drawn from the given pool. Locators
-- range over the full pool either way; only the keys are confined.
genDirectoryOver :: [Int] -> Gen (Directory NextHop)
genDirectoryOver pool =
  fromList <$> listOf ((,) . Pid <$> elements pool <*> genEntry)

forAllDirs2 ::
  (Testable prop) =>
  (Directory NextHop -> Directory NextHop -> prop) ->
  Property
forAllDirs2 f = forAll genDirectory (forAll genDirectory . f)

tests :: TestTree
tests =
  testGroup
    "Graft.Directory"
    [ testGroup
        "merge laws"
        [ testProperty "associative" $
            forAll genDirectory $ \a -> forAllDirs2 $ \b c ->
              merge a (merge b c) == merge (merge a b) c,
          testProperty "commutative" $
            forAllDirs2 $
              \a b -> merge a b == merge b a,
          testProperty "idempotent" $
            forAll genDirectory $
              \d -> merge d d == d,
          testProperty "empty is identity" $
            forAll genDirectory $
              \d -> merge empty d == d
        ],
      testGroup
        "induced order"
        [ testProperty "merge is an upper bound of both arguments" $
            forAllDirs2 $ \a b ->
              leq a (merge a b) && leq b (merge a b),
          testProperty "leq is reflexive" $
            forAll genDirectory $
              \d -> leq d d,
          -- Every upper bound of a and b equals merge (merge a b) u
          -- for some u (take u itself), so c below ranges over all of
          -- them.
          testProperty "merge is least among upper bounds" $
            forAll genDirectory $ \a -> forAllDirs2 $ \b c ->
              leq (merge a b) (merge (merge a b) c)
        ],
      testGroup
        "conflict"
        [ testProperty "disjoint merges introduce no contested slots" $
            forAll (genDirectoryOver [0 .. 3]) $ \a ->
              forAll (genDirectoryOver [4 .. 7]) $ \b ->
                contested (merge a b)
                  == Set.union (contested a) (contested b),
          testProperty "contested keys of a merge are exactly disagreements" $
            forAllDirs2 $ \a b ->
              contested (merge a b)
                == Set.unions
                  [ contested a,
                    contested b,
                    disagreements a b
                  ]
        ],
      -- The worked example from article/nameserver-algebra.md.
      testGroup
        "a small example"
        [ testCase "view claims both PIDs" $
            Map.keysSet (claimed view) @?= Set.fromList [gateway, worker],
          testCase "duplicate delivery changes nothing" $
            merge view published @?= view,
          testCase "a second claimant contests exactly the worker" $
            contested (merge view imposter) @?= Set.singleton worker
        ]
    ]
  where
    gateway = Pid 2
    worker = Pid 5
    own = singleton gateway (Entry (Info "gateway") Self)
    published = singleton worker (Entry (Info "worker") (Child worker))
    view = merge own published
    imposter = singleton worker (Entry (Info "worker") (Child (Pid 3)))

-- | PIDs claimed in both directories with distinct entries.
disagreements :: Directory NextHop -> Directory NextHop -> Set.Set Pid
disagreements a b =
  Map.keysSet
    (Map.filter id (Map.intersectionWith (/=) (claimed a) (claimed b)))

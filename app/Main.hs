-- | The worked example from @article/nameserver-algebra.md@, runnable:
-- a gateway's view, a duplicate delivery, an imposter, and the
-- verdicts. The article's printed values are this program's output.
module Main (main) where

import Graft.Directory
import Graft.Link
import Graft.Tree qualified as Tree

gateway, worker, leaf :: Pid
gateway = Pid 2
worker = Pid 5
leaf = Pid 7

own, published, view, imposter :: Directory NextHop
own = singleton gateway (Entry (Info "gateway") Self)
published = singleton worker (Entry (Info "worker") (Child worker))
view = merge own published
imposter = singleton worker (Entry (Info "worker") (Child (Pid 3)))

firstLink, secondLink :: LinkId
firstLink = LinkId 1
secondLink = LinkId 2

workerPublication :: Directory ()
workerPublication = singleton worker (Entry (Info "worker") ())

leafPublication :: Directory ()
leafPublication = singleton leaf (Entry (Info "leaf") ())

oneLink, disputedLinks, recoveredLinks :: LinkTable ()
oneLink =
  commit $ do
    links <- attach firstLink worker emptyLinks
    publish firstLink workerPublication links
disputedLinks =
  commit $ do
    links <- attach secondLink (Pid 3) oneLink
    publish secondLink workerPublication links
recoveredLinks = commit (finalize secondLink disputedLinks)

parentDomain, childDomain, replacementDomain :: Tree.DomainId
parentDomain = Tree.DomainId 10
childDomain = Tree.DomainId 11
replacementDomain = Tree.DomainId 12

liveTree, treeAfterChildFinalization :: Tree.Summary (Directory ())
liveTree =
  Tree.Live
    workerPublication
    ( Tree.singletonDomain
        childDomain
        (Tree.Live leafPublication Tree.emptyForest)
    )
treeAfterChildFinalization =
  Tree.mergeSummary
    liveTree
    ( Tree.Live
        empty
        (Tree.singletonDomain childDomain Tree.Finalized)
    )

forestAfterReconnect :: Tree.Forest (Directory ())
forestAfterReconnect =
  Tree.mergeForest
    ( Tree.mergeForest
        (Tree.singletonDomain parentDomain Tree.Finalized)
        ( Tree.singletonDomain
            replacementDomain
            (Tree.Live workerPublication Tree.emptyForest)
        )
    )
    (Tree.singletonDomain parentDomain liveTree)

commit :: (Show error) => Either error value -> value
commit = either (error . ("invalid example: " <>) . show) id

demo :: (Show a) => String -> a -> IO ()
demo expr value = do
  putStrLn (">>> " <> expr)
  print value
  putStrLn ""

main :: IO ()
main = do
  demo "view" view
  demo "merge view published == view" (merge view published == view)
  demo "merge view imposter" (merge view imposter)
  demo "health view" (health view)
  demo "health (merge view imposter)" (health (merge view imposter))
  demo "health (materialize own oneLink)" (health (materialize own oneLink))
  demo
    "health (materialize own disputedLinks)"
    (health (materialize own disputedLinks))
  demo
    "health (materialize own recoveredLinks)"
    (health (materialize own recoveredLinks))
  demo
    "Tree.materializeThrough worker liveTree"
    (Tree.materializeThrough worker liveTree)
  demo
    "Tree.materializeThrough worker treeAfterChildFinalization"
    (Tree.materializeThrough worker treeAfterChildFinalization)
  demo
    "Tree.materializeThrough worker (Tree.mergeSummary liveTree Tree.Finalized)"
    ( Tree.materializeThrough
        worker
        (Tree.mergeSummary liveTree Tree.Finalized)
    )
  demo
    "Tree.materializeForestThrough worker forestAfterReconnect"
    (Tree.materializeForestThrough worker forestAfterReconnect)

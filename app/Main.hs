-- | The worked example from @article/nameserver-algebra.md@, runnable:
-- a gateway's view, a duplicate delivery, an imposter, and the
-- verdicts. The article's printed values are this program's output.
module Main (main) where

import Graft.Directory
import Graft.Link

gateway, worker :: Pid
gateway = Pid 2
worker = Pid 5

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

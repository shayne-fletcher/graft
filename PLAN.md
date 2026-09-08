# Graft Plan

## Direction

Develop the algebra on its own terms, using implementation details only as private consistency checks. The article should present one progression from directories, through link-scoped provenance, to hierarchical failure domains. It should not narrate implementation history.

## Current State

- `Directory` defines the flat directory merge and its induced order.
- `Links` retains each link's contribution so the visible directory can shrink when a contribution is finalized.
- `Tree` preserves nested domains, makes finalization dominant, and projects live borrowed state into a visible directory.
- The accompanying Haskell exercises the directory, link, and tree laws and includes a three-node failure and reconnection example.
- `Protocol.hs` and `Simulate.hs` remain empty.

## Review-Readiness Milestone

The following foundation is now present for reviewing the hierarchical-replication proposal:

1. `Links` is complete.
   - `Admitted` is the protocol state preceding the first publication.
   - `Live` carries a link's current complete publication.
   - `Finalized` is terminal for that link incarnation.
   - Live publications and finalization have an explicit algebraic relationship.
2. `Tree` is implemented.
   - Recursive live summaries retain nested failure-domain provenance.
   - Finalizers dominate live summaries for the same domain.
   - Recursive summaries materialize into a visible directory.
3. The essential laws are checked in Haskell.
   - Summary merge is associative, commutative, and idempotent.
   - A finalizer dominates every earlier summary for its domain.
   - Finalizing a child removes exactly that child's subtree from the borrowed view.
   - Finalizing a parent removes all of its descendants from the borrowed view.
   - Reconnection under a fresh domain cannot revive a finalized domain.
4. A three-node example traces publication, child failure, finalization, and reconnection.

The model is now sufficient for a meaningful review of the proposal's claims about hierarchical failure domains, induced ordering, and resurrection prevention.

## Later Work

The following are not prerequisites for beginning that review:

- coverage and negative knowledge;
- retained versus absorbed state;
- finalizer dissemination and collection;
- epochs and garbage collection;
- the complete wire protocol;
- the deterministic simulator;
- SQLite replication;
- backpressure and isolation.

Questions found during the review should determine which of these areas the article and model develop next.

## Verification

Run `source ~/.ghcup/env && cabal test all` after each coherent model change.

# Graft Plan

## Direction

Develop the algebra on its own terms, using implementation details only as private consistency checks. The article should present one progression from directories, through link-scoped provenance, to hierarchical failure domains. It should not narrate implementation history.

## Current State

- `Directory` defines the flat directory join and its induced order.
- `Links` retains each link's contribution so the visible directory can shrink when a contribution is finalized.
- The accompanying Haskell exercises directory laws and link lifecycle behavior.
- `Tree.hs`, `Protocol.hs`, and `Simulate.hs` remain empty.

## Review-Readiness Milestone

Complete the following before reviewing the hierarchical-replication proposal:

1. Finish `Links`.
   - Explain `Admitted` as protocol state preceding the first publication.
   - Define `Live` as the state carrying a link's current complete publication.
   - Define `Finalized` as the terminal state for that link incarnation.
   - State the algebraic relationship between live publications and finalization.
2. Write `Tree`.
   - Define recursive live summaries that retain nested failure-domain provenance.
   - Define finalizer dominance.
   - Define materialization of a recursive summary into a visible directory.
3. Check the essential laws in Haskell.
   - Join is associative, commutative, and idempotent.
   - A finalizer dominates every earlier summary for its domain.
   - Finalizing a child removes exactly that child's subtree from the borrowed view.
   - Finalizing a parent removes all of its descendants from the borrowed view.
   - Reconnection under a fresh domain cannot revive a finalized domain.
4. Add one three-node example that traces publication, child failure, finalization, and reconnection.

Once these steps are complete, the model is sufficient for a meaningful review of the proposal's claims about hierarchical failure domains, induced ordering, and resurrection prevention.

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

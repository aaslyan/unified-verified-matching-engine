# STATUS-v2

## Phase 0 — Inventory and freeze

**Date:** 2026-09-27. **Base commit:** `4811a13`. **Phase commit:** see `git log -- docs/plan-v2`.

**Files added or changed**
- `docs/plan-v2/INVENTORY.md` (deliverable)
- `docs/plan-v2/PLAN.md`: plan v2 verbatim, so later sessions read it from the repo
- `docs/plan-v2/STATUS-v2.md` (this file)
- `docs/c-verification-plan.md`: marked superseded by v2

**Theorems proved:** none (inventory phase).

**`sorry` count**
- Deliverables: none (documents only).
- Project: 2, both in `lean/Bridge/ForwardSimulation.lean` (`insert_forward_sim`, `match_step_forward_sim`). Both are replaced in Phase 4.

**Tests:** not run; no code changed. `lake build` is clean at the base commit (86 jobs).

**Decisions settled from the repo**
- In scope: limit (GTC), market (IOC), IOC limit, post-only, cancel, all four STP modes plus NONE.
- `process` has no result code and no trade timestamps. `Obs` is proposed in INVENTORY §2, with `rejectedPostOnly` decided by the same test `process` uses.
- Two account-0 orders may trade, in both the spec and C.
- EngineDb gaps for Phase 1: no finite live set (so no `count`), allocation may fail at any time, no class `EngineDb S`, and no functional instance.
- `CSubset` programs cannot allocate: the heap exists in the memory model, but no syntax reaches it.
- `CSubset` arithmetic wraps; §4 wants overflow as an error.

**⚑ decisions needing Ara**
1. Spec-only request types (FOK, DAY, stop limit and stop market, market-to-limit, iceberg, minimum quantity, amend): confirm they stay out of the generated matcher, per the §4 default. This does not block Phase 1, because Phase 1's `processB` takes the C request type, which cannot express them.
2. Where the memory-free fragment lives. Extending `CSubset` changes the AMCC dependency, where 35 files import it and its proofs recurse over `Stmt`/`Expr`. The alternative is a separate language in this repository. **Blocks Phase 2**; not Phase 1.

**Deviations from the plan**
- `PLAN.md` was added so the plan persists across sessions; this is not in the Phase 0 deliverable list.
- STATUS lives at `docs/plan-v2/STATUS-v2.md`, next to the other v2 documents.

**Next phase:** Phase 1 — Contract. First task: add a finite live set to `Db` (so `count` is computable), then the class `EngineDb S` with `capacity`, `count`, and allocation that fails iff full.

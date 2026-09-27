# STATUS-v2

## Phase 1 — Contract

**Date:** 2026-09-27. **Base commit:** `c57f173`. **Phase commit:** see `git log -- lean/Bridge/ProcessB.lean`.

**Files added or changed**

| File | Change |
|---|---|
| `lean/Bridge/EngineDbApi.lean` | `Db` gains finite live sets `oLive`/`lLive`; `Db.count`, `Db.levelUsed`; four new `WF` clauses; alloc/free contracts maintain the live sets; new class `EngineDb S` (operations as functions, `capacity`, `view`, `init`, one law per operation). |
| `lean/Bridge/EngineDbApiLaws.lean` | WF preservation extended to the live sets; new section "Handle validity" (per-operation validity laws, lookups return valid handles). |
| `lean/Bridge/EngineDbAbs.lean` | Satisfiability witness: `instance EngineDb (AbsStore cap)` with every law proved. |
| `lean/Bridge/ProcessB.lean` | New: `Req`, `ResultCode`, `qmax`, `processB`, `Obs`/`obs`/`obsSpec`, `cancelOrder_preserves_ProcessInv`, transfer lemmas, reachable-state corollary. |
| `lean/UnifiedVerifiedMatchingEngine.lean` | Imports `Bridge.ProcessB`. |
| `docs/plan-v2/INVENTORY.md`, `PLAN.md`, `FRAGMENT.md` | Decisions 1 and 2 recorded; §7 supported-request list; Phase 6 linking note. |

**Theorems proved**
- `EngineDb (AbsStore cap)` instance: every contract law holds for an executable store; allocation fails exactly when `count ≥ capacity`, leaving the store unchanged.
- Handle validity: `orderAlloc_valid`/`levelAlloc_valid` (new handle valid, others unchanged), `orderFree_valid`/`levelFree_valid` (freed handle invalid, others unchanged), `*_full` (failed allocation changes nothing), frame lemmas for every other operation, and `hashFind_valid`, `tFind_valid`, `tBest_valid`, `qFirst_valid`, `qNext_valid`, `owner_valid`.
- `qmax_bound`: `(cap + 1) * qmax cap < 2^64`.
- `processB_cases`, `processB_rejected`: every rejection returns the input book and no trade.
- `cancelOrder_preserves_ProcessInv`: new; the spec had no invariant theorem for `cancelOrder`.
- Transfer: `processB_preserves_ProcessInv`, `processB_BookInvariant`, `processB_AllInv`, `processB_trades_ok` (INV-11, INV-12), `runB_BookInvariant` (every book reachable by any request sequence satisfies §13).

`#print axioms`: every transfer lemma and the instance use `[propext, Classical.choice, Quot.sound]` or fewer; no `sorryAx`, no axiom declarations.

**`sorry` count:** 0 in all five deliverable files. Project total unchanged: 2 in `ForwardSimulation.lean` (Phase 4).

**Tests:** full `lake build` clean (87 jobs); Lean `runAllTests` 18/18. `processB` evaluated on representative requests: duplicate, capacity (full and may rest), IOC when full (accepted, trades), post-only crossing, unsupported code, zero quantity, STP CANCEL_NEW, cancel known and unknown id — all as specified.

**On the transfer-lemma shape.** Every rejection and the accepted-order case are one line each: rejections return the input book, and an accepted order uses the existing `ProcessInv_step`. The cancel case is not a one-liner because `cancelOrder` had no invariant theorem in the spec; `cancelOrder_preserves_ProcessInv` (about 110 lines with its list lemmas) fills that gap once. The wrapper itself is not the cause.

**Decisions settled from the repo**
- Decision 1 is realised on C's request language: order-type codes outside LIMIT/MARKET/IOC/POST_ONLY give `rejectedUnsupported`; other malformed requests give `rejectedInvalid`.
- Check order in `processB`: unsupported, invalid (incl. `qty > qmax cap`), duplicate id, capacity, post-only crossing, then accept. The Phase 3 matcher must use the same order, since the result code is observable.
- Capacity counts resting orders plus dormant stops (`bookSize`); C never creates stops, so this is the resting-order count.
- The level pool uses the same `capacity` as the order pool (`levelAlloc` fails iff `levelUsed ≥ capacity`). Levels in the book are non-empty, so they never exceed resting orders.
- `Obs` as proposed in INVENTORY §2; the matcher side `obs` decodes its final store with `absBook`.

**⚑ decisions needing Ara:** none new.

**Deviations from the plan**
- `processB` is in `lean/Bridge/ProcessB.lean`, not `Spec/ProcessB.lean`: it takes the C request type, which lives in `Bridge`, and the repository has no `Spec/` directory.
- The abstract model never reuses a freed handle; the contract allows reuse, and nothing proved depends on either.
- `FRAGMENT.md` exists early, holding only the Decision 2 note; Phase 2 fills it.

**Next phase:** Phase 2 — the memory-free matcher language. First task: check whether AMCC's fixed-width arithmetic functions (`evalBin` and friends) import without the `CSubset` memory model; if not, define the language's own minimal arithmetic.

---

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

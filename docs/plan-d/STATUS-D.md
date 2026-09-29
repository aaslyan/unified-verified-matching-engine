# Plan D STATUS — Phase D0
Commits: unified 9bfceb1 (reference; D0 commit adds docs only), amcc 5e0dbf8 (unchanged)   lake build: clean (115 jobs) / clean (60 jobs; 13 pre-existing linter warnings)   sorry: 0/0

## Done
- `docs/plan-d/PLAN-D.md`: the prompt, verbatim.
- `docs/plan-d/D0-INVENTORY.md`, sections 1–8:
  1. the 41-row contract table;
  2. AMCC state, verified from source at `5e0dbf8`;
  3. draft client schema, with front-end acceptance;
  4. `view` design (ghost-state subtype carrier);
  5. initialisation;
  6. tree options, recommending (a);
  7. cost and phase order;
  8. linking.
- No code in either repository.

## Laws discharged / pending (by structure)
Nothing is discharged yet; this phase is the inventory. Of the 41 calls:
- 4 need no store theorem.
- 15 are field reads/writes, which need instance lemmas plus one composition lemma for writes.
- 10 are partial: an AMCC theorem exists for a narrower configuration (root-only Llist, u32 Thash key, Inlary pool, success branch only).
- 12 are MISSING: pool free ×2, pool failure ×2, hash remove, and the 8 tree calls.

The 24 `count_*`/`levelsUsed_*` frames follow from the ghost update. By structure:

| Structure | Status |
|---|---|
| pools | partial (alloc success only; Free/Init/failure/completeness MISSING; heap pool MISSING) |
| queue | partial (one root list per program; per-parent MISSING) |
| hash | partial (u32 keys; Remove MISSING) |
| owner | Upptr get/set exists; the owning-list invariant MISSING |
| tree | MISSING (stubs) |
| init | MISSING |

## Evidence re-run (suite, scale, result)
None. No C was changed. The last full run was `tests/run_all.sh` on the merged tree `a14da7e`: exit 0.

## Deviations from PLAN-D.md (what, why)
- **§0 overstates AMCC in two places:**
  - `alloc_correct` "with `RowFresh`": `RowFresh` is a hypothesis that nothing establishes.
  - "Pool/Inlary" as a basis: Pool has no Free, Init or failure theorem.
  - Everything else in §0 was confirmed.
- **§4 D1 ("generate and measure") cannot run first.** No AMCC generator can emit the client schema:
  - one field per reftype;
  - no per-parent Llist;
  - u64 Thash keys rejected;
  - Tpool ill-typed;
  - Atree stubs.

  The proposed order is in D0-INVENTORY §7. D1 becomes generator work without theorems, followed by generation, the Phase 5 suites and the benchmark. The proofs follow in D2–D7.

## Findings
- **`lean/Bridge/ForwardSimulation.lean:22-31` overclaims.** Its module docstring says Pool/Inlary refinement is "Completed … `RowFresh`" and Llist is completed with `insert_success`. Pool lacks Free/Init/failure theorems, and `RowFresh` is never established. Its theorem (`mini_queue_insert_forward_sim`) is correctly scoped. The file is outside Plan D's writable set, so it is recorded here only.
- **AMCC's own stale prose:**
  - `Thash.lean:479-508` says "Still owed", but `Find` is proved in `ThashFind.lean`.
  - `CSubset/Syntax.lean:20-32` says "no null literal".
  - `Ssim.supported`'s docstring says "eight of them", but all 36 reftypes are accepted.
  - `Spec/Rbtree.lean`'s docstring claims O(log N), which is not proved.
  - `Conformance.verdictOfReftype` labels reftypes that have no template as `.generated`.
- **`MiniDb.genC` is not schema-generic.** It hard-codes `id`/`qty`, and its theorems are for `miniDb`/`miniDb3` only.
- **The contract fixes list orders** (`oLive`, `hash` and `tree t` prepend) by exact `Db` equality. Memory does not record these orders, so the instance needs ghost state (D0-INVENTORY §4).
- **The matcher never calls a store operation with its precondition false.** `runExt` checks every `pre` and traps otherwise, and both matcher proofs show no trap. So a guarded instance operation (C run under `pre`, identity otherwise) never takes its fallback on any run the theorem covers.
- **The adapter's `total_qty` is private state** outside the contract. The generated store drops it.

## ⚑ Questions for Ara
1. **Pool route.**
   - `GOALS.md`'s standing rule names "a pool over a static arena rather than do the heap work" as a broken rule. The heap route is `Stmt.alloc`/`free` + an allocator oracle in CSubset, plus a heap pool (Tpool) with Reserve/Alloc/Free. Init reserves `capacity` rows per pool, and that reservation's success is the single trusted step.
   - It is the largest item: about 3.5–6k lines of AMCC, and it reopens every exhaustive `Stmt` proof.
   - The alternative is Inlary (about 1k lines, no allocation), which contradicts `GOALS.md`.
   - Recommendation: the heap route.
2. **Tree.** Recommendation: (a) Atree/AVL, correctness only, about 4–7k lines of AMCC. Confirm, or choose (c), which changes the spec.
3. **Phase order.** Generator work first (D1 without theorems), then the proofs D2–D7 (D0-INVENTORY §7). Confirm. D1 also updates AMCC's `PLAN.md`: Atree, Tpool and `Stmt.alloc` move from deferred to now.
4. **Carrier.** A subtype of `(Mem, ghost Db, Rep)`, with operations as guarded CSubset runs (noncomputable). Confirm this reading of "operations are CSubset's semantics of the generated functions".
5. **`writeOrder` vs per-field setters.** Prove the instance lemma "`writeOrder` of a one-field update = the single generated setter". This keeps the printer's `setO f ↦ ME_order_set_f` a name translation. Confirm, or accept it as printer trust instead.
6. **Composition generator.** Recommendation: a schema-generic `genDb` in AMCC (definition of done: every accepted schema), with the client-specific composed `Rep` and laws in `lean/Bridge/`. Confirm the split.

## Next phase, first step
Pending the answers to ⚑1–3. If they are confirmed as recommended, D1 starts in AMCC by generalising the generators to more than one field per reftype on the root. Every generator currently uses `fields.find?`. That generalisation is needed for two pools and two trees, and it comes before the per-parent Llist emission.

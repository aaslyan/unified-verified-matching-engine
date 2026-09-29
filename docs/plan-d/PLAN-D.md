# Plan D — discharging the storage contract (Verification Plan v2, Phase 6)

Prompt for a Claude Code session with two checkouts side by side: `amcc` (github.com/aaslyan/amcc) and `unified-verified-matching-engine` (whose `lakefile.toml` requires `../amcc`). D0 is an inventory with no code, ending in a report and a stop. Later phases alternate between the two repositories; every STATUS says which.

## 0. Where things stand

The unified repository proves, on `main` (reference commit: the current head; record it):

```lean
theorem matcher_refines {S : Type} [EngineDb S] (hcap : CapOk S)
    {s : S} (hI : Inv s) (req : Req) : Refines s req
theorem matcher_run_refines (hcap : CapOk S) (qs : List Req) : ...   -- over request sequences
```

for **every** store `S` satisfying the `EngineDb` contract (`EngineDbApi.lean`, `EngineDbApiLaws.lean`: ~50 law fields over init, order/level alloc and free, reads and writes, hash find/insert/remove, queue insertTail/remove/first/next, tree find/insert/remove/best, and the `count_*`/`levelsUsed_*` frame laws). The model store `AbsStore` proves every law (`EngineDbAbs.lean`), so the contract is satisfiable. The *production* data layer — `c/src/matching_engine_gen.c` (434 lines: chunked pools, an intrusive doubly-linked FIFO per price level, an id hash, and an unbalanced binary search tree per side) behind `c/gen/engine_db_adapter.c` (125 lines) and the 41 `ME_*` calls of `c/gen/engine_db.h` — is only *tested* against the contract (1.8M operations, mutants). That test is the last empirical link in the chain; Plan D turns it into a theorem.

AMCC is the home of the container proofs. As of late September it has: a certified array table (`MilestoneTheorem`); the `Llist` template fully refined (elems decoder, `TailListInv`, `insertTail_correct`, `remove_correct` with tail preservation, FIFO stepping theorems); `Pool`/`Inlary` (`allocDef`, `PoolInv`, `alloc_correct` with `RowFresh`); `Thash` with `RepInv`, lookup soundness and `insert_success` (no remove); `Upptr` without refinement laws; and `mini_insert_forward_sim` — `execStmt` on generated C preserving a composed two-structure `DbRepInv` and matching the abstract operation. There is no `Atree`. `GOALS.md` is canonical and binding; `PLAN.md` is updated in the same commit as any route change. AMCC stays a general generator; the matching engine is one client schema. Confirm all of this at D0 rather than assuming it.

## 1. Goal

An `EngineDb` instance whose carrier is the state of an AMCC-generated data layer and whose operations are CSubset's semantics of the generated functions, with every law proved from AMCC's template theorems. Then `matcher_run_refines` instantiates at that store, giving:

> If the initial allocation succeeds, every request returns exactly what the bounded specification returns, for every request sequence.

After that, what is still trusted: the two printers (matcher language → C, CSubset → C), the C calling convention across `engine_db.h` where the two printed fragments meet, gcc/clang, single-threaded use, and the initial `malloc`. Nothing about the data layer's logic.

Not goals: changing the matcher, `Program.lean`, `processB`, or any contract law (a law that turns out unprovable for the generated store is a ⚑, because changing the contract re-opens both matcher proofs); balance of the price tree (a performance property, proved separately or never); C-to-assembly.

## 2. Ground rules

- Unified repo: new files under `lean/Bridge/` (the instance), `lean/Store/` if a client-side layer is needed, `c/gen/` (generated data layer and adapter), `docs/plan-d/`, and the schema file. Read-only: everything the walk experiment and Plan v2 marked read-only, plus `lean/Walk/`.
- AMCC repo: templates, decoders and template theorems are the work product. No matching-engine narrative in AMCC's docs; the requirement is stated as "client schema needs". Route changes: `GOALS.md` and `PLAN.md` in the same commit.
- Every phase: `lake build` clean in both repositories, no `sorry`, standard axioms only, commit (prefix `d:`), push both, `docs/plan-d/STATUS-D.md`, stop. ⚑ = stop and ask Ara.
- Evidence runs early: the existing Phase 5 suites (`tests/contract/`, `tests/differential/`, `tests/run_all.sh`) are written against `engine_db.h`; they run against the generated data layer unchanged and are the first check on every phase that touches C.
- Copy this file to `docs/plan-d/PLAN-D.md` in the first commit.

## 3. D0 — Inventory (no code; report and stop)

Produce `docs/plan-d/D0-INVENTORY.md` with:

1. **Contract table.** One row per `ME_*` call (41): its contract law(s); the C function behind it in `matching_engine_gen.c`/the adapter; the AMCC template and operation that would implement it (`Pool` alloc/free/read/write; `Llist` insertTail/remove/first/next; `Thash` find/insert/remove; the price tree; `Upptr` or a plain field for `owner`); the existing AMCC theorem that discharges the law, or `MISSING`. Frame laws (`count_*`, `levelsUsed_*`) included.
2. **AMCC state, verified from source.** For each template: files, the abstract model, the decoder, the theorems (names, statements), the shape of `mini_insert_forward_sim`, and whether the theorems are schema-generic (instantiable at a client schema) or specific to the toy schema. Whether `execStmt` in CSubset is typed-field or byte-level, and what that costs the decoder. How generated code represents handles (row indices?) and how that matches the contract's opaque handles with validity laws.
3. **The schema.** A draft ssim/dmmeta-style schema for the client: `Order` and `Level` records with their fields (exactly what `engine_db.h` reads and writes — use the widened `uint64_t` fields), a `Pool` for each, an `Llist` of orders per level (tail insert, remove, first, next), a `Thash` of orders by id, a price tree per side, `owner` from order to level. What AMCC's front end accepts today and what it does not.
4. **`view`.** A design for `view : GenStore → AbstractView` — the same `AbstractView` type the contract uses, so `Inv`, `CapOk` and the theorem apply unchanged — built from the templates' decoders. Which contract laws follow directly from template theorems, which need a composition lemma (as `mini_insert_forward_sim` composes two structures), and which need new template work.
5. **Initialisation.** How the generated store is allocated (one `malloc` per pool at init, or one arena), what the `init_*` laws need, and where "initial allocation succeeds" enters the theorem as the single trusted step.
6. **The tree.** Three options, each with what it costs and what it touches:
   - (a) `Atree` as an AVL template (OpenACR's `Atree` is AVL): correctness only (BST ordering invariant; rotations preserve in-order), balance later or never. Deletion is the bulk. No spec change.
   - (b) a red-black template on the same terms. Same proof shape; note any Lean 4 functional red-black model that could serve as the abstract side (Batteries has one; it is functional, and the imperative array version is the actual proof burden).
   - (c) a price ladder with bitmaps: no rotations, O(1) best; but a bounded price range, so `tInsert` gains a failure mode, `processB` gains a range check, and both matcher proofs are touched at their entry lemmas. Smallest proof, only option that changes the spec.
   Recommend one, with the estimate. The default is (a); (c) needs Ara's decision.
7. **Cost and order.** Per structure: template work in AMCC (new theorems needed), instance work in the unified repo (laws to prove), risk. Proposed phase order (default: pools and fields → queue → hash → tree → init → closing theorem), with what evidence runs after each.
8. **Linking.** State the two-level picture precisely: at the Lean level the instance composes the matcher's semantics with CSubset's semantics of the generated functions (a theorem); at the C level the two printed fragments meet through `engine_db.h` (a trust item, covered by the linked differential). Anything that does not fit this picture is a ⚑.

STATUS-D.md, commit (unified repo only, docs), push, stop.

## 4. Phases after D0 (adjust from the inventory; say so in STATUS)

- **D1 — Generate and measure.** Schema in the unified repo; AMCC generates the data layer and (if feasible) the adapter; build against `engine_db.h`; run `tests/contract/run.sh`, `tests/differential/run.sh`, `make test-gen` against the generated store — all green before any proof. Benchmark generated vs handwritten data layer under the generated matcher on random and on monotone price streams (the handwritten tree is unbalanced); record in `docs/plan-d/BENCH-D.md`. A performance surprise is reported here, not discovered after the proofs.
- **D2 — Instance skeleton and pool laws.** `lean/Bridge/EngineDbGen.lean`: the carrier, `view`, the operations as CSubset runs, and the pool/field laws (`orderAlloc/Free`, `levelAlloc/Free`, `read*/write*`, `levelCount`, `owner`, the `count_*`/`levelsUsed_*` frames) from AMCC's `Pool` theorems; remaining laws stated with their proofs deferred by *structure*, tracked in STATUS, never by `sorry` in a committed file — keep undischarged laws in a separate `Pending` structure that the instance does not yet claim.
- **D3 — Queue laws** from `Llist`. **D4 — Hash laws** from `Thash`, adding `remove` to the template in AMCC first. **D5 — Tree laws** from the template chosen at D0. Each: the template theorem in AMCC, the law in the unified repo, the contract suite re-run.
- **D6 — Init.** The `init_*` laws and the initial-allocation model; the statement of the trusted step in `PLAN-D.md`'s trust boundary.
- **D7 — Closing.** The full `EngineDb GenStore` instance; `engine_run_refines := matcher_run_refines (S := GenStore)`, stated verbatim and `#print axioms`; the slogan as a corollary with the initial allocation as its hypothesis; every Phase 5 suite green against the generated store; both semantics suites (matcher language, and AMCC's for CSubset if it has one) re-run; `docs/plan-d/EVIDENCE-D.md`; the trust boundary written out. Stop.

## 5. STATUS-D.md template

```
# Plan D STATUS — Phase Dx
Commits: unified <sha>, amcc <sha>   lake build: clean/clean   sorry: 0/0
## Done
## Laws discharged / pending (by structure)
## Evidence re-run (suite, scale, result)
## Deviations from PLAN-D.md (what, why)
## Findings
## ⚑ Questions for Ara
## Next phase, first step
```

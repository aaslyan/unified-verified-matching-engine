# Walking-spec experiment — a spec that walks the book the way the C does

Prompt for a fresh Claude Code session in `unified-verified-matching-engine`. This is a separate experiment from Verification Plan v2. v2 is complete on `main` (Phases 0–5, zero `sorry`); this work lives on its own branch, adds files only, and re-proves v2's headline theorem by a different proof architecture so the two can be compared lemma for lemma.

## 0. What exists, and what this is

Current state on `main` (v2 Phases 0–5 done; read `docs/plan-v2/STATUS-v2.md`, `docs/plan-v2/LOOP-INVARIANT.md` and `docs/plan-v2/EVIDENCE.md` first):

- Reference spec: `process` (Lean 4, no `sorry`, full §13 invariant suite: Uncrossed, Sorted, FIFO, No ghosts, No resting market orders, STP, Post-only). Never edited, by anyone, for any reason.
- `processB` in `lean/Bridge/ProcessB.lean`: bounded wrapper. Entry checks in order — unsupported request type → `RejectedUnsupported`, invalid, duplicate id, capacity → `RejectedCapacity` (pessimistic: rejects when `count = capacity` even if the order would never rest), post-only crossing (confirm at A0 whether this is decided at entry or inside `process`) — then `process` or `cancelOrder`.
- Storage contract: `EngineDbApi.lean`, `EngineDbApiLaws.lean` (class `EngineDb S`; one law per operation; handle-validity laws; allocation fails iff full and changes nothing), executable witness `EngineDbAbs.lean`.
- Memory-free matcher language: `lean/Matcher/` — u64, enum codes (equality only), bool, opaque handles with a null-test construct; executable semantics `execStmt` that errors on contract violation, invalid handle, overflow, or exhausted loop bound; printer to C11 over `c/gen/engine_db.h`.
- The program: `lean/Matcher/Program.lean` (`matcherProgram`), printed to `c/gen/matcher.c` (443 lines, `scripts/gen_matcher.sh --check` confirms it is current). Loops bounded by `capacity + 1`. Trades leave through `ME_trade_emit` (buffer lives in the adapter).
- Evidence: Lean differential — matcher under `execStmt` on the model store vs `processB` on the `Obs` triple (result code, trades, visible book); 72,000 requests at capacities 2, 6, 20; 0 mismatches. Phase 5: contract laws tested against the linked adapter + data layer (1.8M operations), spec-oracle differential (180,000 steps), semantics test Lean vs gcc/clang (12,000 runs, exact trap classes, plus the valid-handle generator `SemValid`), printer reparse.
- The headline theorem is **proved on `main`** (v2 §2; commit 40e3816), with the run-level version `matcher_run_refines` in `lean/Matcher/Run.lean` (e7a28b3):

```lean
theorem matcher_refines [EngineDb S] (hcap : CapOk S) {s : S} (hI : Inv s) (req : Req) : Refines s req
-- Refines s req: the run returns .ok, stays within both loop bounds of capacity + 1,
-- its result code, trades and book view equal processB's on decode s, and Inv s' holds.
```

- The direct loop proof (v2 Phase 4, about 4,500 lines in seven files) uses a *continuation invariant*: after k inner iterations the store and locals correspond to an intermediate state σ_k of the reference's `doMatch`, and the rest of the spec run from σ_k equals the whole run. Its lemma chain is `inner_body → inner_loop → outer_body → outer_loop → resting step and result code → matcher_refines`; the invariant is written up in `LOOP-INVARIANT.md`. Facts it established that this experiment reuses by import, never re-proves: `Inv` (between requests: store decodes to a book, count = book size ≤ capacity, no empty level, hashed ids = book ids), `InvM` (inside an outer iteration: the current level may be empty), `decode`, the per-construct decode lemmas, `stopX` (at loop exit no contra level crosses the order's price — needed for uncrossedness after resting), `doMatch_fuel_stable` (any fuel above the measure gives the same result), and `processB_congr` (two stop-free books with equal views give equal results and equal-view new books). Also known: no result code distinguishes a fully filled order from one cancelled by self-trade prevention, so "cancelled" is folded into `remaining = 0`; and `bookView` drops `postOnly`, `status`, `timestamp` of orders and `lastTradePrice`, `nextId`, `clock` of the book.

**The question this experiment answers.** The direct proof works, so this is no longer a rescue; it is a measurement. `process` is functional — it computes a new book from an old one, with a matching recursion driven by a computed fuel — while the C walks a store and mutates it, one resting order per inner iteration. The direct route bridged that with an *invented* invariant. The walk route replaces the invention with a definition: does the same theorem cost less, and is the loop part of the proof structural, when the spec is first restated in the shape of the program?

**The move.** Add an intermediate spec, `Walk.process`, whose matching is a bounded loop over an explicit `Walk.step`, where `Walk.step` is, by definition, one iteration of the printed loop body transliterated to act on the abstract `Book`. Then:

- `Walk.refines` — the program refines `Walk.process`. Structural: the loop case is "one iteration = one `Walk.step`", and the relation between (store, locals) and the walk state is the identity on the walk's own fields. Nothing to invent.
- `Walk.process_eq_processB` — the walk means what the reference means. Lean-only, over Lean data, with Lean tools. This is where the content lives.
- `matcher_refines` follows as a corollary.

The spec of record stays `process`. `Walk.process` has no authority of its own; the equivalence theorem is what certifies it. The claim wording (v2 §7) does not change. This is proof architecture, not a new spec.

Ara's framing: the matcher should be one-to-one with the Lean. It is one-to-one with *this* Lean by construction, and equal to the reference by theorem. His longer-term aim, which this serves: proofs closer to the implementation, with invariants derived compositionally from data-structure operations rather than monolithic transition-level proofs.

## 1. Goal, non-goals

Goal — three deliverables, in order:

1. `Walk.process`: executable, over the reference `Book`, same signature and result type as `processB`.
2. `Walk.process_eq_processB`.
3. `Walk.refines`, and `matcher_refines` as its corollary.

Plus the measurement: A4 compares the walk route against the direct proof on `main`, lemma for lemma and line for line, over the same infrastructure.

Non-goals: everything v2 §1 excludes (pool/allocator correctness, C-to-assembly, data-layer representation); changing the program or the printed C; changing the claim; replacing the direct proof — if this route is shorter or clearer, that is a separate decision Ara makes after A4.

## 2. Ground rules

- Branch `walk-spec` off `main` at 285b0a6 or later. Recommended: `git worktree add -b walk-spec ../uvme-walk main` and run this session in `../uvme-walk`, so the main checkout stays free.
- New files only, under `lean/Walk/` and `docs/walk-spec/`. Read-only: the reference spec, `lean/Bridge/ProcessB.lean`, `EngineDbApi*.lean`, `EngineDbAbs.lean`, everything in `lean/Matcher/` including `Program.lean`, `Run.lean` and the Phase 4 proof files, everything under `c/` and `tests/`, `docs/plan-v2/`.
- Reuse by import, never re-prove: `Inv`, `InvM`, `decode`, the per-construct decode lemmas, `stopX`, `doMatch_fuel_stable`, `processB_congr`, the differential harnesses. The experiment measures the loop proof and the equivalence, not the infrastructure both routes need. If a reused definition is stated in a way that does not fit the walk (for example `Inv` mentions the direct proof's σ), say so in STATUS and wrap it; do not fork it.
- If the experiment seems to *need* a change to `Program.lean` (for example the loop body is not a clean single step), do not make it. ⚑ report exactly what and why. The experiment must show that the program as it stands is one-to-one with a walking spec; a program that has to be reshaped to fit is itself a finding.
- No `sorry` in deliverables. Standard axioms only. `lake build` clean before and after every phase. Commit with prefix `walk:`. Push. Write `docs/walk-spec/STATUS-W.md`. One phase per session; stop at the end of each phase.
- ⚑ = stop and ask Ara.
- Copy this file to `docs/walk-spec/PLAN-W.md` in the first commit.

## 3. Definitions (targets, not code — adjust only after the A0 inventory, and say so)

```lean
namespace Walk

structure State where
  book      : Book         -- the reference Book type, not a new one
  remaining : Qty          -- the incoming order's quantity left (reference types, not u64)
  trades    : List Trade   -- emitted so far, in emission order

inductive Next
  | more (st : State)      -- loop continues
  | done (st : State)      -- loop exits

-- The printed matcher has TWO nested loops: an outer loop over contra price levels and
-- an inner loop over the orders of the current level, with the emptied level freed after
-- the inner loop. On the abstract Book there are no levels, so the outer loop is pure
-- representation: level fetch and cleanup are the identity under decode (the direct proof
-- records "an outer iteration's level cleanup is zero spec steps"). Walk.step is therefore
-- ONE INNER iteration, and Walk.run is flat over fills; the nesting reappears only in the
-- A3 loop lemma.
-- Derived from the inner loop body in Program.lean / c/gen/matcher.c, statement by statement:
--   every store call in the body      → a Book primitive
--   every local                       → a State field or a let
--   every break                       → .done
--   every continue                    → .more with the book changed and remaining unchanged
--   ME_trade_emit t                   → trades := trades ++ [t]
def step (agg : Order) (st : State) : Next        -- agg: the incoming order; its live qty is st.remaining

-- Mirror the language's bounded-loop construct exactly as Program.lean uses it:
-- same bound (cap + 1), same exit test, same order of tests.
def run (agg : Order) : Nat → State → State
  | 0,     st => st
  | n + 1, st =>
      if st.remaining = 0 then st else
      match step agg st with
      | .done st' => st'
      | .more st' => run agg n st'

-- Entry checks in exactly processB's order, then cancel, or run (cap + 1) followed by
-- resting what remains (limit only; IOC and market never rest) — again transliterated
-- from the program, not designed from the paper.
def process (cap : Nat) (b : Book) (req : Req) : Result × List Trade × Book

end Walk
```

Book primitives the step needs — small total functions over the reference `Book`, one per store call the body makes: best resting order on the opposite side, pop it, reduce it by a quantity, insert a resting order, remove by id, find by id, count. These are the "underlying data-structure operations"; the equivalence proof will need lemmas relating them to whatever list/map operations the reference uses internally.

Fuel: `cap + 1`, from the argument, matching `ME_capacity()` — not the reference's computed fuel. Each `.more` step either pops a resting order or (partial fill of the maker) leaves `remaining = 0`, so `cap + 1` iterations suffice whenever `count ≤ cap`. Prove that as `run_fuel_sufficient` in A1. On the reference side, `doMatch_fuel_stable` on `main` already gives fuel-independence above the measure; import it.

Theorem shapes:

```lean
-- State the weakest hypothesis the proof actually needs; ideally none, otherwise the
-- reference's own well-formedness predicate (the one §13 shows process preserves), and
-- stop-freeness, which the run-level proof on main already carries along the chain.
-- Whatever it is, Inv on main must imply it for decode s — check, don't extend Inv.
theorem Walk.process_eq_processB (cap b req) (hwf : WF b) :
  Walk.process cap b req = processB cap b req
-- or equality on the Obs projection if processB's result type is richer — say which;
-- processB_congr on main is the tool if the walk's book differs only in dropped fields.

theorem Walk.refines {S} [EngineDb S] : ∀ s req, Inv s →
  ∃ s' r, execStmt matcherProgram (s, req) = .ok (s', r)
        ∧ obs r s' = obsSpec (Walk.process (capacity S) (decode s) req)
        ∧ Inv s'

theorem matcher_refines ... := by  -- corollary of the two, no new content
```

## 4. Phases

### A0 — Inventory (no code; report and stop)

1. Reference spec: module path; the `Book`, `Order`, `Trade` definitions (how each side is stored; whether price levels are explicit; full field lists); `process` / `processOrder`; the matching function (Ara's notes call it `doMatch` with `computeMatchFuel` — confirm), its recursion scheme (fuel? structural on a list? on what?), and what one recursive call does (one fill? one level? one order?); `cancelOrder`; the existing fuel-sufficiency lemma(s) and the reference's well-formedness predicate(s).
2. `processB`: signature, result type, entry-check order, where post-only is decided, how it calls `process` / `cancelOrder`, what `obsSpec` projects.
3. The loops: quote both matching loops from `Program.lean` (AST form) and from `c/gen/matcher.c`. For the inner body list, in order, every store call, every local, every break/continue, and the exit test. That list *is* `Walk.step`; the inner exit test and bound *are* `Walk.run`. For the outer body list the level fetch, the inner loop, and the cleanup, and confirm that under `decode` the outer body is zero or more inner steps and nothing else. Say whether each inner iteration performs exactly one fill.
4. The direct proof, as the baseline for A4: for each of `inner_body`, `inner_loop`, `outer_body`, `outer_loop`, the resting-step and result-code lemmas, and `matcher_refines` itself — file, line count, and which reusable facts (§2) it depends on. Also the line counts of `Inv`, `InvM`, `decode` and the per-construct lemmas, so the reused infrastructure is measured once and excluded from both sides of the comparison.
5. The differential harnesses (`scripts/matcher_lean_diff.sh` and the Phase 5 spec-oracle differential): how the oracle is wired in, how to swap in a new one, how seeds are fixed.
6. Obstacles to using the reference `Book` as `State.book`: the best-opposite operation is not a cheap head/lookup; the C tracks something the reference book doesn't, or vice versa; the reference `Trade` record differs from what `ME_trade_emit` receives. If a separate `Walk.Book` with an abstraction to `Book` looks unavoidable, say so and stop — don't build it.
7. Proposed concrete signatures for `State`, `Next`, `step`, `run`, `process`, the Book primitives, and the `WF` hypothesis (if any) for the equivalence, with the check that `Inv` on `main` implies it.

STATUS-W.md, commit, push, stop.

### A1 — The walk: executable, differential (Lean only)

1. `lean/Walk/Spec.lean`: the definitions of §3 as agreed at A0. `step` is transliterated from the loop body, statement by statement, with a comment table `C line ↔ Lean line` beside it. Do not design `step` from the paper or from the reference; the program is its source.
2. Sanity lemmas in `lean/Walk/Basic.lean`: `run_fuel_sufficient`; `run` is stable once it exits; each `.more` step decreases the opposite side's count or sets `remaining = 0`.
3. Differential 1: `Walk.process` vs `processB` on the `Obs` triple. Same harness and seeds as Phase 3 (72,000 requests; capacities 2, 6, 20), plus capacity 1, plus runs where the book fills so `RejectedCapacity` and the pessimistic reject are exercised; every result code hit. Expected: 0 mismatches.
4. Differential 2: matcher under `execStmt` on the model store vs `Walk.process`. Expected: 0 mismatches.

A mismatch is a finding, not something to fix by bending `Walk.step`:
- D2 ≠ 0 → the transliteration is wrong. Fix it, re-run both.
- D1 ≠ 0 with D2 = 0 → the program disagrees with `processB` in a way Phase 3 didn't catch. ⚑ immediately, with the failing trace. Do not touch the program.

STATUS-W.md, commit, push, stop.

### A2 — Equivalence with the reference (Lean only; the content)

Prove `Walk.process_eq_processB` in `lean/Walk/Equiv.lean`. Suggested decomposition:

1. Entry checks and cancel: unfold both sides; one lemma per branch.
2. Fuel: both sides are fuel-independent above sufficiency — `cap + 1` suffices for the walk (A1 lemma), and `doMatch_fuel_stable` on `main` gives it for the reference — so it is enough to relate the two loops at any sufficient fuel.
3. One `Walk.step` ↔ one unfolding of the reference's matching recursion, on a book satisfying `WF`: applying `step` to `(b, q, ts)` equals one recursive call of the reference's matcher, modulo the reference's representation of the intermediate state. This is where the Book primitives earn their lemmas — pop / reduce / insert against the reference's list or map operations. This is the risk in the whole experiment.
4. Assemble.

Order of work: 1, 2, then 3 — have the frame in place before the risky part. If 3 is blocked after a serious full-session attempt, ⚑ with the exact blocking lemma statement and what the two sides compute differently (for example: the reference matches per level, the walk per order; the reference's trade record carries a field the walk's does not; the reference reorders trades). Do not weaken the theorem and do not touch the reference to get past it. Ara then chooses between continuing, a fallback (prove the §13 invariants directly on `Walk.process`, compositionally from the primitives — a different kind of correctness, with `processB` demoted to a differential voice), or stopping the experiment. That choice is his, not this session's.

STATUS-W.md, commit, push, stop.

### A3 — Refinement of the program to the walk

Prove `Walk.refines` in `lean/Walk/Refine.lean`, then `matcher_refines` as a corollary.

1. Reuse `Inv`, `InvM`, `decode`, `CapOk` and the per-construct decode lemmas from `main` as they are. Nothing in this phase re-proves a store-level fact; if one is missing, add it in `lean/Walk/` and mark it in STATUS as infrastructure, so A4 can exclude it from the comparison.
2. Inner body lemma: one execution of the inner loop body from (store, locals) related to `st` yields (store', locals') related to `Walk.step st`, the relation being `decode store = st.book ∧ remaining = st.remaining ∧ emitted = st.trades`, under `InvM`. This is the one-to-one claim made precise. If it doesn't go through by unfolding both sides, the transliteration at A1 was wrong somewhere: find it, don't patch around it. (This lemma plus A1's Differential 2 replace the checkpoint v2 put in front of its loop proof — here the invariant is the identity relation.)
3. Inner loop lemma, generic over the language's bounded-loop construct: `execStmt (loop n body)` relates to `Walk.run n` given the body lemma and the exit test.
4. Outer body and outer loop: an outer iteration (level fetch, inner loop, cleanup) relates to a prefix of the flat `Walk.run` — the fills of that level — and restores `Inv` from `InvM`; the outer loop folds this with its bound. This is the one place the walk route has to pay for the nesting; keep it as its own lemma so A4 can compare it with `outer_body`/`outer_loop` on `main`.
5. Entry checks, cancel, resting and result code: statement by statement, same style; `stopX` from `main` is the fact the resting step needs.
6. Overflow: `remaining - q` with `q ≤ remaining`; fills are `min` of two in-range quantities; no sums across orders in the matcher. Say explicitly where the `0 < qty ≤ Qmax` bound is used and where it is not.
7. Assemble `Walk.refines`; derive `matcher_refines` (the statement on `main`, verbatim) from it and `Walk.process_eq_processB`, and check with `#print axioms` that nothing beyond propext, Classical.choice and Quot.sound was used.

STATUS-W.md, commit, push, stop.

### A4 — Write-up for Ara (short)

`docs/walk-spec/RESULT-W.md`, built on the A0 baseline:

- A table, one row per lemma of the direct loop proof (`inner_body`, `inner_loop`, `outer_body`, `outer_loop`, resting step, result code, `matcher_refines`), with its line count on `main` and the walk-route lemma(s) that replace it with their line counts; then the rows the walk route adds (`Walk.process_eq_processB` and its parts) with theirs. Reused infrastructure appears once, outside the table.
- Totals for both routes over the same scope, and sessions per phase.
- What went through by unfolding and what needed thought, named by lemma.
- Where the difficulty moved: the direct route's invariant clauses versus the walk route's equivalence lemmas — which is easier to state, to check, and to maintain when the program changes.
- A recommendation: keep the direct proof, replace it, or keep both with one as the record — and why.

## 5. STATUS-W.md template

```
# Walk-spec STATUS — Phase Ax
Commit: <sha>   Branch: walk-spec   lake build: clean | not   sorry count under lean/Walk: 0

## Done
## Deviations from PLAN-W.md (what, why)
## Findings (things now known about the reference spec, the program, or the contract that were not known before)
## ⚑ Questions for Ara
## Next phase, first step
```

## 6. If it works — a note for later (not a task)

Once `Walk.refines` is proved by unfolding, the two sides are visibly the same function applied to two representations: the walk over `Book`, the program over `S`. The systematic version is one definition, parametric in a small `BookOps` interface, with two instances — and a third, syntactic instance whose "run" produces the AST, so that `matcherProgram` is `Walk.process` evaluated at syntax and refinement becomes one generic soundness theorem for the syntactic instance instead of a per-program proof. That is the true endpoint of "one-to-one". Decide after A4 whether it is worth doing.

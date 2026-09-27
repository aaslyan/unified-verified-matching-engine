# C Engine Verification Plan

> **Superseded** by plan v2 (`docs/plan-v2/PLAN.md`) for the method and the steps. Kept as the record of Prompts 1–3.

## Target

The verified artifact is not the handwritten `c/src/matching_engine.c`. It is
a `CSubset` program: a C syntax tree that lives in Lean. The shipped C file is
printed from that tree, and every theorem is about running that exact tree
under the formal semantics (`execStmt`):

```
Lean spec (process)                          what should happen
   ↑  refinement theorem (Prompt 4b)
CSubset program, run by execStmt             the object the proofs are about
   ↓  printer: round-trip proof (Prompt 6)
matching_engine C file (generated)
   ↓  gcc: differential tests (Prompt 5)
binary
```

The memory is hidden behind the EngineDb API (`lean/Bridge/EngineDbApi.lean`):
the matching logic is proved against the API contract with no memory model,
and the generated data structures are separately proved to meet that contract.

The handwritten C stays as the porting reference, the differential-testing
baseline and the performance baseline. It is outside the verified part, as are
the test and benchmark drivers.

**What the final claim trusts:** `CSubset` behaves like real C (evidence:
Prompt 5), the printer's grammar is read by C compilers the way the parser
reads it (Prompt 6 reduces this to one small grammar), gcc, and `malloc`
returning NULL or fresh memory. **What it assumes about inputs:** order ids are
never reused (D1), per-level totals stay below 2^64 (D8), a non-NULL engine
(D10), single-threaded use. Everything else is proved.

**Out of scope for this plan, next phase:** proving the generated data
structures (Pool, Llist, Thash, Atree) meet `EngineDbApi` over the heap, and
the linking theorem that a concrete run of the client matches an abstract run.

## Status

| Prompt | Track | Status |
|---|---|---|
| 1 CancelOrder use-after-free | C fixes | Done |
| 2 C versus spec divergences | Spec alignment | Done; decisions recorded in `docs/c-vs-spec-divergences.md` |
| 3 Abstraction map, STP spec change | Proof | Next |
| 4a Port the client to CSubset | Implementation | After 3 |
| 4b Refinement theorem | Proof | After 4a |
| 5 Differential testing of CSubset | Trust base | Independent, any time |
| 6 Printer round-trip proof | Trust base | Independent, any time |

Each step is a self-contained prompt. After each one, the tester checks the
acceptance criteria before the next step starts. No step commits.

---

## Prompt 1: Fix the CancelOrder use-after-free (done)

> In `c/src/matching_engine.c`, `MatchingEngine_CancelOrder` calls
> `EngineDb_order_pool_Free(ord)` and afterwards reads `ord->side` to choose
> the tree to remove the emptied level from. That read is a use-after-free.
>
> 1. Fix it by reading every field needed from `ord` before any call that
>    frees it. Keep the change minimal and in the existing code style.
> 2. Audit the rest of `matching_engine.c` for the same pattern: any read or
>    write through an `Order*` or `PriceLevel*` after it was passed to
>    `EngineDb_order_pool_Free` or `EngineDb_level_pool_Free`. Report each
>    location with file:line, and fix any real ones.
> 3. Add tests to `c/tests/test_correctness.c` that cancel the last order of a
>    bid level and the last order of an ask level, and check that the level is
>    removed from the correct tree (best bid/ask and `MatchingEngine_CheckInvariants`).
> 4. Run `make test`. Do not modify generated files (`*_gen.c`, `*_gen.h`).
>    Do not commit.
>
> Report: the diff, the audit findings, and the `make test` output.

**Acceptance:** no field of a freed row is accessed after the free call;
the audit lists every `Free` call site with a verdict; new tests pass;
`make test` passes; generated files untouched.

---

## Prompt 2: C versus spec divergence report (done)

> Compare the matching behaviour of `c/src/matching_engine.c`
> (`MatchingEngine_ProcessOrder`, `MatchingEngine_CancelOrder`) with the Lean
> spec `lean/MatchingEngine/Process.lean` (`process`, `doMatch`, `dispose`)
> restricted to the order kinds the C engine supports: LIMIT, MARKET, IOC,
> POST_ONLY, with the five STP modes. Do not change any code.
>
> Produce `docs/c-vs-spec-divergences.md` with one entry per behavioural
> difference: C file:line, Lean file:line, a concrete request sequence on
> which the two produce different books or trades, and which side looks
> wrong. Cover at least: order-type mapping (C `order_type` versus spec
> `orderType`/`tif`/`postOnly`), the STP trigger (C `account_id` versus spec
> `stpGroup`), each STP mode, post-only rejection, IOC and MARKET remainders,
> duplicate-id rejection, rejection reporting, trade emission fields, cancel
> of an unknown id, and integer overflow (`uint64_t` versus `Nat`).
>
> For each difference, check it by running both sides where possible: the C
> engine through a small driver, the Lean spec through `#eval`.

**Acceptance:** every entry has both locations and a reproducing input that
was actually run on both sides; no code changed. The user decides each
entry before Prompt 3.

---

## Prompt 3: Abstraction map and client invariant

> Using the decisions recorded in `docs/c-vs-spec-divergences.md`
> (section "Decisions"):
>
> 0. Change the STP rule in the Lean spec (`lean/MatchingEngine/STP.lean`
>    and the order fields it needs) to C's rule: a conflict exists when both
>    orders share a nonzero account and the incoming order's STP mode is not
>    NONE. Re-prove every theorem that breaks, weakening the STP guarantee
>    (INV-12) only by "unless the incoming order opted out". Keep all other
>    theorems' statements unchanged.
>
> Then create `lean/Bridge/EngineDbAbs.lean`:
>
> 1. The C request type and the spec it must refine. Either a map from C
>    requests into `MatchingEngine.Order` with `MatchingEngine.process` as the
>    spec, or a small `cStep` spec proved equal to `process` on mapped requests.
> 2. `absBook : EngineDbApi.Db → BookState`: each tree's levels sorted by
>    price (bids descending, asks ascending), each level's queue as its orders.
> 3. `ClientInv : Db → Prop`: levels in trees are non-empty; every queued
>    order is hashed and vice versa; each order's price and side match its
>    level and tree; `totalQty` is the sum of remaining quantities; remaining
>    quantity is positive; each level's queue is its only owner.
> 4. Prove `ClientInv Db.empty`, and that `ClientInv db ∧ db.WF` implies
>    `AllInv (absBook db)` and `BookInvariant (absBook db)`.
>
> No `sorry`. `lake build` must pass. Do not commit.

**Acceptance:** builds with no `sorry`; `#print axioms` shows only standard
axioms; `absBook Db.empty = BookState.empty` (up to the fields the C engine
does not have); the existing theorems still build with unchanged statements
apart from the STP guarantee.

---

## Prompt 4a: Port the client to CSubset

> Write `MatchingEngine_ProcessOrder` and `MatchingEngine_CancelOrder` as a
> `CSubset` program in Lean (`lean/Bridge/EngineClientC.lean`), using the
> handwritten `c/src/matching_engine.c` as the reference. This program becomes
> the source of truth; the C file is printed from it.
>
> 1. The program touches EngineDb only through the generated API functions of
>    `c/include/matching_engine_gen.h` and through payload fields, following
>    `EngineDbApi.lean`: no writes to key fields (`Order.id` while hashed,
>    `PriceLevel.price` while in a tree), no writes to link fields or
>    `orders_n`, `total_qty` adjusted only on fills. State this discipline as
>    a checkable predicate on the syntax tree and prove the program satisfies
>    it.
> 2. `CSubset` only has `forN` with a literal trip count. Bound the matching
>    loops by the pool capacities, and prove later (4b) that the bound is
>    never reached, as was done for the Lean spec's fuel.
> 3. The `on_trade` callback is probably not expressible. Replace it with a
>    trade buffer the caller reads after each call, and adapt the handwritten
>    test and benchmark drivers to it.
> 4. The program must pass `CSubset`'s well-formedness checks. Print it with
>    `Print.program` into `c/src/matching_engine_client_gen.c`.
> 5. Differential test: link the printed client with the generated data
>    structures, and run it against the handwritten engine on at least 100,000
>    random request sequences covering every order type, STP mode, cancels
>    and invalid requests. Books, trades and return values must match
>    exactly. Also run `c/tests/test_correctness.c` against it.
>
> Keep the handwritten engine building. No `sorry`. Do not commit.

**Acceptance:** the program passes the well-formedness checks and the API
discipline predicate; the printed file compiles with
`-std=c11 -Wall -Wextra -Werror`; zero mismatches against the handwritten
engine; the tester re-runs the differential test with a fresh seed.

---

## Prompt 4b: Refinement theorem for the CSubset client

> Prove that the `CSubset` client from 4a refines the spec, against the
> abstract API only.
>
> 1. Define an abstract interpretation of the client's syntax tree: the same
>    tree, run with every `EngineDb_*` call and every payload access
>    interpreted by `EngineDbApi`'s `pre`/`post` over `Db`, instead of by the
>    generated function bodies over memory. This is a semantics of the same
>    object, not a hand-written model of it.
> 2. Prove every API call happens within its `pre`, given
>    `db.WF ∧ ClientInv db` and the input assumptions D1, D8, D10.
> 3. Prove the refinement theorem: every abstract run from `db` on request
>    `req` ends in `db'` with `db'.WF ∧ ClientInv db'`,
>    `absBook db' = (spec step on absBook db req).book`, trades equal to the
>    spec's trades, and a return value that is `false` exactly when the spec
>    rejects the request (D9).
> 4. Prove the loop bounds from 4a are never reached, and that allocation
>    failure leaves the book unchanged (D6).
> 5. Compose with the reachable-state theorems: for any request sequence
>    satisfying the assumptions, every state of the abstract run satisfies
>    `BookInvariant` and every trade satisfies the post-only and STP
>    guarantees.
>
> No `sorry`. `lake build` must pass. Do not commit.

**Acceptance:** builds with no `sorry`; standard axioms only; the theorem is
stated about the 4a syntax tree itself, so no line-by-line comparison with
handwritten code is needed; the tester checks that the stated assumptions are
exactly D1, D8, D10 plus single-threaded use.

---

## Prompt 5: Differential testing of CSubset against gcc

Independent of Prompts 1–4. Works in the AMCC repository (`../amcc`), which
owns the semantics.

> Every proof about the C engine is a proof about `CSubset`
> (`Amcc/CSubset/Eval.lean`: `execStmt`, `callFun`, `runCalls`). Nothing proves
> that gcc compiles the printed C (`Amcc/Codegen/Print.lean`) to something
> that behaves the same. Today the only evidence is `scripts/smoke.sh`, which
> replays a few hand-written call sequences per template against transcribed
> expectations. Build a randomized differential harness that makes this
> evidence systematic.
>
> 1. **Program generator (Lean).** Generate random programs that pass
>    `CSubset`'s well-formedness checks (`Wf.lean`, `WfChecks.lean`). Cover
>    every constructor of `Expr`, `Stmt`, `BinOp`, `UnOp`, every `ScalarTy` and
>    cast, structs, arrays, `forN`, calls, and dynamic storage (allocation,
>    free, null checks). Bias values towards edge cases: 0, 1, the maximum of
>    each unsigned type, and values that overflow on `+`, `-`, `*` and casts.
>    Include narrow types (`uint8_t`, `uint16_t`) in arithmetic and
>    comparisons, where C's integer promotion to `int` applies. Seeded and
>    reproducible.
> 2. **Oracle (Lean).** Run each program's call sequence with `runCalls` and
>    serialize the results and the final global state in a fixed text format.
>    Semantic errors (index out of range, null dereference, freed block) are
>    results too; a well-formed program that raises one is itself a finding.
> 3. **Compiled side (C).** Print with `Print.program`, generate a driver that
>    makes the same calls and prints the same format, compile with gcc at `-O0`
>    and `-O2`, and with clang if available, all with
>    `-std=c11 -Wall -Wextra -Werror`. Also build one variant with
>    `-fsanitize=address,undefined`: any sanitizer report on a program the
>    Lean side accepts is a finding.
> 4. **Allocation failure.** Find out how `CSubset` decides whether an
>    allocation fails, and make the C side fail at exactly the same calls
>    (for example by wrapping `malloc` with `-Wl,--wrap=malloc`), so failure
>    paths are compared too, not only the success path.
> 5. **Template fuzzing.** Separately, drive each generated template
>    (Pool, Llist, Thash, Atree, ...) with long random call sequences on both
>    sides, not only the transcribed ones.
> 6. **Script.** Add `scripts/difftest.sh <seed> <count>` that runs all of the
>    above and prints a per-construct coverage table and every mismatch with a
>    minimized reproducer. Do not add it to `lake build`.
>
> Every mismatch is triaged: a bug in the Lean semantics, the printer, or the
> generator, or a C behaviour the subset must exclude. Fix what is clearly a
> bug; report the rest. Do not commit.

**Acceptance:** 10,000 random programs and 10,000 template call sequences
run on every compiler and optimisation level with zero untriaged mismatches;
the coverage table shows every syntax constructor and every scalar type
exercised; the tester re-runs the script with a fresh seed and gets the same
result; the "no `malloc`/`free`" row at the top of `Amcc/CSubset/Syntax.lean`,
which is now out of date, is corrected.

---

## Prompt 6: Round-trip proof for the printer

Independent of Prompts 1–5. Works in the AMCC repository (`../amcc`).

> `Amcc/Codegen/Print.lean` turns a `CSubset` `Program` into C text. It is
> currently trusted and only checked by eye and by `scripts/smoke.sh`. Replace
> that trust with a proof that the printer loses and changes nothing.
>
> 1. **Grammar.** Write down, in `docs/`, the exact concrete grammar the
>    printer emits: fully parenthesised expressions, suffixed literals,
>    declarator forms, statement forms. It should be small enough that a
>    reader can check a C compiler reads it the same way.
> 2. **Parser.** Implement `Amcc/Codegen/Parse.lean`: a parser for exactly
>    that grammar, `parse : String → Option Program`. It does not need to
>    accept any C beyond what the printer emits. Keep lexing and parsing
>    simple and structural so the proof stays tractable.
> 3. **Round trip.** Prove
>    `∀ p, WellFormed p → parse (print p) = some p`, using `CSubset`'s
>    existing well-formedness predicate. As a corollary, prove the printer is
>    injective on well-formed programs.
> 4. **Goldens.** Check that every file under `scripts/gen/` parses back to
>    the syntax tree its generator produced, and do the same for the client
>    from Prompt 4a when it exists.
> 5. **Trust statement.** Update the header of `Print.lean`: what remains
>    trusted is that a C compiler reads the documented grammar the way `parse`
>    does, and that is what Prompt 5 tests.
>
> No `sorry`. `lake build` must pass. Do not commit.

**Acceptance:** the round-trip theorem builds with no `sorry` and standard
axioms only; every golden parses back exactly; the grammar document is short
enough to review by eye; the tester mutates the printer (drops a pair of
parentheses, swaps two operands) and confirms the proof breaks.

---

## Prompt 3 notes (2026-09-27)

- **STP rule (D2/D3).** `selfTradeConflict inc rest` is now
  `inc.stpPolicy.isSome ∧ inc.stpGroup = rest.stpGroup = some _`. WF-16 is
  relaxed to `stpPolicy.isSome → stpGroup.isSome`. `Trade` gains
  `aggStpPolicy`, and INV-12 (`STPGuarantee`, `TradeOk`) requires distinct
  groups only when `aggStpPolicy.isSome`. No other theorem statement changed.
- **Mapping.** `stpGroup := some account` if `account ≠ 0`. `stpPolicy :=`
  the mode's policy if `account ≠ 0`, else `none` (account 0 never conflicts
  on either side, and this keeps WF-16). `CRequest.toSpec` is `none` exactly
  on C's static rejections (`toSpec_none_iff`), and otherwise well formed
  (`toSpec_wellFormed`).
- **Ids (D1).** `processWithId b o := process { b with nextId := o.id } o`,
  equal to `process` when `b.nextId = o.id`.
- **Fields C lacks.** `postOnly`, `status`, `timestamp` (orders) and
  `lastTradePrice`, `nextId`, `clock` (book) are synthesized in `absBook`
  and forgotten by `bookView`. Timestamps are queue positions and the clock
  is `1 + #resting orders`, so `BookOk` holds. See the table in
  `lean/Bridge/EngineDbAbs.lean`.
- **Results.** `ClientInv_empty`, `absBook_empty` (literal equality),
  `absBook_AllInv`, `absBook_BookInvariant`, `absBook_ProcessInv`.

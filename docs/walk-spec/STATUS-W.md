# Walk-spec STATUS — Phase A1 (the walk: executable, differential)

Commit: see `git log -1 -- docs/walk-spec/STATUS-W.md`   Branch: walk-spec   lake build: clean (default target, 102 jobs; `lake build Walk`, 28 jobs), before and after   sorry count under lean/Walk: 0

The A0 inventory, the A4 baseline, is now `A0-INVENTORY.md`.

**Summary:**
- `Walk.process` exists and is transliterated from `c/gen/matcher.c`, with a C line ↔ Lean line table.
- Fuel sufficiency is proved.
- Both differentials report 0 mismatches over 144,000 steps. Every result code was hit, and the pessimistic capacity reject was exercised 10,279 times.
- No change to the program was needed or made.

## A0 decisions (Ara, recorded)

1. The walk is nested: `innerStep`/`outerStep`, `innerRun`/`outerRun`.
2. The A3 relation holds up to `bookView`, plus the two derived-local clauses (`best` = head contra level, `passive` = its head order).
3. A2 is stated as equality of `obsSpec`.
4. A2 may import the spec-only lemmas of `Matcher/SpecStep.lean`. They count as shared, and every use is listed here and in A4. **None were used in A1.**
5. `run` returns `Option`: `none` means the bound was exhausted with the test still true. Fuel sufficiency is a theorem.
6. `stopX`: the walk states its own exit clause and reuses `stopX_of_best` (A3).
7. One `lakefile.toml` entry for the `Walk` library (below).

**Addition to A4 (Ara):**
- For every lemma in the comparison table, on both routes, split its lines into three categories:
  - **store-side:** `InvM` preservation, frame, count and handle facts;
  - **spec-relation:** the clause or lemma that ties store state to the reference;
  - **glue:** statement evaluation, dispatch, assembly.
- Report the split per route and in total.
- List which store operations recur in the most branches. Popping one resting order is three contract calls (`queue_remove`, `hash_remove`, `order_free`).

## Done

| File | Lines | What |
|---|---|---|
| `lean/Walk/Spec.lean` | 426 (335 + 91-line table) | Book primitives, `Ctx`, `State`, `innerTest`/`innerStep`/`innerRun`, `outerTest`/`outerStep`/`outerRun`, `restOrder`/`rest`, `sideProc`, `processOrder`, `cancel`, `process`; the C line ↔ Lean line table at the end |
| `lean/Walk/Basic.lean` | 335 | Sanity lemmas (below) |
| `lean/Walk/Check.lean` | 138 | D1 and D2 on three chains, plus the `genFill` stream generator |
| `lean/Walk/CheckRun.lean` | 6 | `#eval` runner; not a library root |
| `docs/walk-spec/walk_diff.sh` | 14 | Runs all differential configurations |

**Book primitives: one per store call.**
- `tBest` = `*_best`, `qFirst`, `levelCount`, `getAccount`.
- `setHeadRem` = `order_set_remaining` on the head order.
- `popHead` = `queue_remove` + `hash_remove` + `order_free` of the head.
- `dropBest` = `*_remove` + `level_free` of the best level.
- `count`, `levelsUsed`, `hashFind`, `owner`, `qRemove`, `qRemoveTail`, `tRemove`, `tFind`.
- `tInsertNew` = `level_alloc` + `level_set_price` + `*_insert`.
- `qInsertTail`.
- All are total list functions on the reference `BookState`, reached through `sideL`/`setSideL` indexed by the contract's `Tree`.

**`Basic.lean`, no `sorry`, axioms `propext` and `Quot.sound` only:**
- `innerStep_shape`: one inner iteration changes only the head level. Either `rem = 0`, or the head order is gone and at most one trade was emitted.
- `innerStep_isSome`: an inner iteration traps only on a full trade buffer.
- `innerStep_progress`: an inner iteration whose test holds either sets `rem = 0` or removes exactly one contra order.
- `innerRun_exit`/`outerRun_exit`, `innerRun_stable`/`outerRun_stable`: a loop whose test is false returns its state, and more fuel than a finished run used changes nothing.
- `innerRun_ok`, `outerRun_ok`: at bound `cap + 1`, neither loop exhausts its bound and the emit buffer never fills. The potential is `trades.length + contra orders ≤ cap` while `rem > 0`.
- **`run_fuel_sufficient`:** `cap + 1 < 2^64`, `count b ≤ cap` and no empty level together imply `(Walk.process cap b req).isSome`.

**Differentials: 0 mismatches and 0 traps everywhere.** Three chains (`processB`, `Walk.process`, and the matcher on the model store) are stepped on the same stream. Each feeds its own output state to its next step.

| Stream | Seed | Streams × length | Cap | Steps | D1 (walk vs `processB`) | D2 (matcher vs walk) | Pessimistic capacity rejects |
|---|---|---|---|---|---|---|---|
| `genReq` (Phase 3) | 7 | 400 × 60 | 2 | 24,000 | 0 | 0 | 2,571 |
| `genReq` | 7 | 400 × 60 | 6 | 24,000 | 0 | 0 | 1,254 |
| `genReq` | 7 | 400 × 60 | 20 | 24,000 | 0 | 0 | 0 |
| `genReq` | 7 | 400 × 60 | 1 | 24,000 | 0 | 0 | 2,288 |
| `genFill` | 11 | 200 × 60 | 1 | 12,000 | 0 | 0 | 1,061 |
| `genFill` | 11 | 200 × 60 | 2 | 12,000 | 0 | 0 | 1,431 |
| `genFill` | 11 | 200 × 60 | 6 | 12,000 | 0 | 0 | 1,312 |
| `genFill` | 11 | 200 × 60 | 20 | 12,000 | 0 | 0 | 362 |
| **Total** | | | | **144,000** | **0** | **0** | **10,279** |

- All eight result codes appear (0–7; see the `genReq` cap 2 and cap 6 rows).
- A pessimistic reject is a code-5 result on a marketable request, meaning a MARKET order or a contra best that crosses.
- **Harness check:** two deliberately wrong transliterations were caught at once by both D1 and D2, then reverted. The two bugs were: `CANCEL_BOTH` not zeroing `rem`, and the level cleanup never firing.
- Run with `docs/walk-spec/walk_diff.sh`, about 45 s.

## Deviations from PLAN-W.md (what, why)

1. **No `Next` type.**
   - The program has no `break` and no `continue`; every loop exits through its test. `Next.done` would never be produced.
   - So `innerStep : Ctx → State → Option State`, where `none` is the one in-body trap, a full trade buffer (`me_trap(3)`).
2. **`Walk.process` returns `Option (ResultCode × ProcessResult)`.** `none` means the program traps:
   - bound exhausted, `me_trap(2)`;
   - trade buffer full, `me_trap(3)`;
   - `cap + 1` does not fit `uint64_t`, `me_trap(1)`.

   This extends A0 ⚑5 from `run` to `process`. `run_fuel_sufficient` shows `none` never happens on a C-reachable book. So A2 will state `Walk.process cap b req = some w ∧ obsSpec w = obsSpec (processB cap b req)`.
3. **`Ctx` carries the raw `CRequest`, not a spec `Order`.**
   - The program's parameters are the request fields, so the walk tests the raw codes as the C does (`otype = 3`, `stp = 1`, …).
   - The five extra fields of a reference `Trade` are built from the request and the passive order's STP group (`mkTrade`). The trade list is intended to equal the reference's element for element, not only under `tradeObs`; A2 will confirm.
4. **`count` is `(allBookOrders b).length`, not `bookSize`.** The C has no stops. The two agree on every book with `stops = []`, which covers every decoded book and every book `processB` reaches from empty.
5. **More primitives than proposed at A0.**
   - `modAt`, `qRemoveTail`, `tInsertNew`, `tFind`, `levelsUsed` and `owner` are needed by the rest block and cancel, including the unreachable failure branches (level-pool full, hash-insert duplicate). Those are transliterated, not dropped.
   - `qRemoveTail` is `queue_remove(lvl, ord)` for the order just appended; that it is the tail is a fact about the program, noted beside it.
6. **The differential runner uses `#eval`.**
   - `Matcher.CheckLean` defines `main`, so a module that imports it (to reuse `genReq` and `matcherStep` unchanged) cannot define its own.
   - `lean/Walk/CheckRun.lean` evaluates `Walk.Check.runIO`, with parameters from `WALK_*` environment variables. The speed is the same as `lean --run` (both interpret).
7. **The runner script is `docs/walk-spec/walk_diff.sh`,** not under `scripts/`. `scripts/` is outside the directories this experiment may add to.
8. **Build targets.**
   - The `lakefile.toml` entry is the only edit outside `lean/Walk/` and `docs/walk-spec/`: `[[lean_lib]] name = "Walk"`, with `roots = ["Walk.Spec", "Walk.Basic", "Walk.Check"]`, which keeps the `#eval` runner out of the library.
   - The Walk library is not in `defaultTargets`, since that would be a second edit. So "lake build clean" here means both `lake build` and `lake build Walk`.
9. **No `walk_oracle` executable for `tests/differential/run.sh`.** A1's instructions named only the two Lean differentials, and an executable would be a second `lakefile.toml` entry. It is available on request.

## Findings

1. **The program is one-to-one with a walk on the reference `BookState` as it stands.**
   - Every store call in the matcher maps to one total list primitive.
   - Every local is a `State` field, a `let`, or a derived head (`best`, `passive`, `nextp`, `victim`).
   - The transliteration passed D2 on its first run. No reshaping of `Program.lean` was needed.
2. **`Walk.process` agrees with `processB` on every tested step (D1 = 0),** including the trades list under `tradeObs` and the book view. So the equivalence A2 must prove is, on this evidence, true as stated.
3. **Phase 3's cap-20 run never exercises the capacity path:** 0 code-5 results at cap 20 with `genReq`. `genFill` covers it: 1,382 code-5 results at cap 20, 362 of them pessimistic.
4. **The trade-buffer bound (`me_trap(3)`) needs its own argument.**
   - The argument is the potential `trades + contra orders ≤ cap` while `rem > 0`. It holds because each emitted trade either removes the maker or ends the match.
   - It is not implied by the loop bounds alone: a level of `cap` orders all filled emits `cap` trades within one outer iteration.
5. **The rest block's failure returns** (order pool full → 5, level pool full → 5, hash duplicate → 4) are reachable in the walk only on books where the entry checks would have rejected already. They are kept, transliterated, for A3's one-to-one lemma. A2 will show they are dead under the entry checks.

## ⚑ Questions for Ara

1. Should the `Walk` library be added to `defaultTargets`, so a bare `lake build` covers it? That is a second one-line lakefile edit; not done.
2. Do you want a `walk_oracle` executable (a second lakefile entry) so `tests/differential/run.sh` can also be driven against `Walk.process`? Not done.

## Next phase, first step

A2, `lean/Walk/Equiv.lean`:
1. Entry checks and cancel, one lemma per branch. The first targets are `processOrder`'s checks against `processB`'s `decodeOrderType`/`toSpec`/`qmax`/`idOnBook`/`requestMayRest` ladder: `hashFind … isSome ↔ idOnBook`, and `count = bookSize` under `stops = []`.
2. Cancel: the `owner`/`qRemove`/`tRemove` sequence against `cancelOrder`'s `removeLevelOrder` on a book with unique ids.
3. Then the fuel frame (`run_fuel_sufficient` for the walk, `doMatch_fuel_stable` for the reference), before the step correspondence.

# Phase 4 checkpoint: the matching-loop invariant

Review point before any proof effort goes into the matching loop. Everything
else in `gen_process_order` and `gen_cancel_order` is proved (STATUS-v2,
Phase 4).

## Setting

An order request `r` that passes the entry checks (`staticCode = none`, id not
hashed, not rejected for capacity) reaches `gen_process_buy` or
`gen_process_sell`. Write `tc` for the contra tree (asks for a buy), `to` for
the own tree, `s₀` for the store on entry, `b := absBook (view s₀)`.

On the spec side, `processB` runs `processWithId b o` with `o := r.toSpec`. For
the in-scope types this is `process`'s Phase 5 (LIMIT, IOC, MARKET, and a
post-only order that does not cross):

```
mr  := doMatch F o' b.bids b.asks [] (clock + 1)      -- F := computeMatchFuel b side
b'' := dispose mr.incoming {b with bids := mr.bids, asks := mr.asks} mr.trades
      -- then processCascade: stops are empty, so only lastTradePrice changes
```

A crossing post-only order never reaches here (`rejectedPostOnly`, proved). A
non-crossing one goes through `process`'s Phase 2, `insertOrder`; the matcher
reaches the same book through a loop that makes zero matching steps (below).

## The spec's intermediate state

`doMatch` is a state machine on `σ = (inc, bids, asks, trades)`. The spec run
is identified with its remaining computation:

```
Spec(σ, f)  :=  doMatch F o' b.bids b.asks [] tm = doMatch f σ.inc σ.bids σ.asks σ.trades tm
                ∧  f > matchMeasure σ.contra σ.inc
```

`Spec(σ₀, F)` holds at the start (`computeMatchFuel_gt_matchMeasure`). Each
non-terminal `doMatch` step moves to `Spec(σ', f − 1)` (the step decreases the
measure: the existing progress lemmas). When `σ` is terminal,
`doMatch f σ = σ`, so the spec's `mr` is `σ`.

## The coupling: store and locals against `σ`

Between statements of the loops, with `s` the store and `rem`, `stop`, `best`,
`passive` the locals:

| | Clause |
|---|---|
| C1 | **Contra side.** `(absSide (view s) tc)` with empty levels dropped equals `σ.contra` through `levelView`. |
| C2 | **Own side** is untouched: `absSide (view s) to = absSide (view s₀) to`; `doMatch` never touches it (`doMatch_bids_of_buy` / `…asks_of_sell`). |
| C3 | **Aggressor.** If `σ.inc.status = cancelled` then `rem = 0`; otherwise `rem.toNat = σ.inc.remainingQty`. The request's other fields are unchanged in the environment. |
| C4 | **Trades.** The trade buffer is `σ.trades.map tradeObs`. |
| C5 | **Store invariant.** Every `Inv` clause holds, except that `ClientInv.level_nonempty` may fail for the single level `best`, and only inside an outer iteration. |

Inside the inner loop, additionally:

| | Clause |
|---|---|
| I1 | `best` is the best level of `tc` in `view s`. Its price crosses `r.price`, or the order is MARKET. Its orders with the queue head first are `σ.contra`'s head level, unless its queue is empty. |
| I2 | `passive = qFirst best`: null exactly when `best`'s queue is empty. |

## One iteration refines one spec step

**Inner iteration** (`passive ≠ null ∧ rem > 0`) = **exactly one `doMatch` step**,
taken at `σ.contra`'s head level on its head order `resting`:

| Matcher branch | `doMatch` branch |
|---|---|
| `account ≠ 0 ∧ account = passive.account ∧ stp ≠ NONE` | `selfTradeConflict inc resting` (group = nonzero account, policy = mode ≠ NONE) |
| · CANCEL_NEW: `rem := 0` | `cancelNewest`: `inc` cancelled, terminal |
| · CANCEL_OLD: remove `passive`, `passive := next` | `cancelOldest`: drop `resting`, recurse |
| · CANCEL_BOTH: remove `passive`, `rem := 0` | `cancelBoth`: drop `resting`, `inc` cancelled, terminal |
| · DECREMENT: `fill := min(rem, prem)`, both reduced, remove `passive` if it reaches 0 | `decrement`: `reduceQty = min(inc.rem, resting.visible)`, with visible = remaining (no icebergs), `> 0` |
| otherwise: fill, `emit`, remove `passive` if it reaches 0 | normal fill: trade appended; full fill removes, partial fill updates the head |

`doMatch` branches that cannot occur under the coupling:
- an empty head level: `σ.contra` never has one, because `doMatch` drops a level in the same step that empties it;
- a zero-visible order: `visibleQty = remaining > 0` by `ClientInv`;
- an iceberg reload: `displayQty = none`.

**Outer iteration** (`rem > 0 ∧ ¬stop`) = **the inner loop's steps, then zero spec steps**:

- `best := tBest tc`. Null means `σ.contra = []`: the spec's `| [] =>` terminal. `stop := true`.
- The price does not cross and the order is not MARKET: the spec's `!canMatchPrice` terminal. `stop := true`.
- Otherwise the inner loop runs. It exits when `rem = 0` (spec terminal: filled or cancelled) or when `passive = null`. In the second case the level is exhausted; the spec dropped it in the step that removed its last order.
- If `best`'s count is 0: `tRemove` and `levelFree`. Zero spec steps; this restores `level_nonempty` (C5).

**Exit.** When the outer loop exits, `σ` is terminal, so `mr = σ`.

## Termination and bounds (loop budget `capacity + 1`)

- **Inner:** every inner iteration that continues removes one resting order, so there are at most `count(s) + 1 ≤ capacity + 1` iterations.
- **Outer:** every outer iteration that continues ends with `passive = null`, so it frees a level. That gives at most `levels + 1 ≤ count + 1 ≤ capacity + 1` iterations, using levels ≤ orders from no empty level (`Inv.levels_eq`).
- **Trade buffer:** trades ≤ removed resting orders + 1 ≤ `capacity + 1`.
- **Overflow:** `fill ≤ rem` and `fill ≤ prem`, so every subtraction stays at or above 0. No sums are formed. The `Qmax` bound is not needed for the matcher's own arithmetic.

## After the loop: resting ↔ `dispose`

`rem > 0 ∧ otype ∉ {IOC, MARKET}` ⇔ `dispose` inserts. That is, not filled or cancelled, `tif ≠ ioc`, and `orderType ≠ market`.

- `orderAlloc` cannot fail: a resting request passed the capacity check (`count < capacity`), and matching only lowered `count`.
- `levelAlloc` cannot fail: levels ≤ orders < capacity.
- `hashInsert` cannot refuse: the id was not hashed at entry, and matching removed only other ids.

So the three failure branches are unreachable under `Inv`. The book step is `tFind` → existing level, or `levelAlloc`/`setL price`/`tInsert`, then `qInsertTail`. It matches `insertOrder` (append to the level at the price, or a new level in sorted position). The view equality uses the same sorted-permutation argument as cancel (`views_eq_of_perm`); the row matches by `restingOrder_matches_request`.

## Lemmas the loop proof needs

1. `doMatch` one-step equations for each branch above, under the coupling hypotheses.
2. Store-side effects:
   - `absSide` after writing `remaining` (partial fill);
   - after removing the head order: `qRemove` + `hashRemove` + `orderFree`, reusing the cancel lemmas without the level removal;
   - after `tRemove` + `levelFree` of an empty level.
3. C1 with "empty levels dropped", and C5, the weakened invariant.
4. The measure and bound lemmas; building `LoopRun` for both loops by induction on the measure.
5. Resting: `insertOrder` against the store insert.
6. Assembly:
   - `matcher_refines` for accepted orders;
   - then `matcher_refines` for every request (cases: `refines_static`, `refines_duplicate`, `refines_capacity`, accepted, `refines_cancel`);
   - then the trace corollary from `init_empty`.

## ⚑ Decisions for the reviewer

1. **Granularity of the spec side.** The coupling ties the matcher to `doMatch` through "the remaining computation is equal" (`Spec(σ, f)`). The alternative is a small-step relation extracted from `doMatch`. The first reuses the existing fuel and progress lemmas unchanged, so I recommend it.
2. **The transient empty level.** The matcher, like the handwritten C, frees an emptied level after the inner loop, so for a moment the store holds an empty level in a tree. The coupling tolerates this with C1 (empty levels dropped) and C5 (one exception). The alternative is changing `Program.lean` to free the level inside the inner loop, the moment its last order leaves. Then `ClientInv` holds at every statement, which removes C5's exception and the dropped-empty-levels clause. Observable behaviour is identical, and the Lean and C differentials would re-check it. It costs a departure from the handwritten C's structure. I recommend **changing the program**: it removes the one non-standard clause from the invariant.

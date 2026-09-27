# Phase 4: the matching-loop invariant, as proved

This started as the review point before the loop proof. It now records the
invariant that was actually proved (Lean files `lean/Matcher/SpecStep.lean`,
`StoreStep.lean`, `LoopEnv.lean`, `Inner.lean`, `Outer.lean`, `Rest.lean`,
`Accept.lean`). The decisions from the review are applied:

1. The spec side is related through its **remaining computation**, at the
   spec's own fuel. No small-step relation is extracted from `doMatch`.
2. `Program.lean` is **unchanged**: the level is freed after the inner loop.
   There are two predicates, `Inv` between requests and outer iterations, and
   `InvM s l` inside an outer iteration.

The end result is `MatcherAccept.matcher_refines`:

```
theorem matcher_refines [EngineDb S] (hcap : CapOk S) {s : S} (hI : Inv s) (req : Req) :
    Refines s req
```

with `inv_init : Inv init`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## Setting

An order request `r` that passes the entry checks reaches
`gen_process_buy`/`gen_process_sell`. Those checks are: `staticCode = none`,
the id is not hashed, and it is not a capacity rejection. Notation:

- `isBuy = (r.side = 0)`.
- The contra tree is `contraT isBuy` (asks for a buy); the own tree is `ownT isBuy`.
- `b = absBook (view s)`.
- `o1 = o1Of b o`, the order `process` hands to `processOrder`.
- `own = absSide (view s) (ownT isBuy)`.
- `tm = b.clock + 1`.

**Spec side** (`SpecStep.lean`). The accepted-order pipeline is reduced to
`doMatch`, then `dispose`, through `bookView`:

- `processWithId_match` handles a non-post-only order.
- `processWithId_postOnly` handles a non-crossing post-only order. Its matching run is empty, and `insertOrder` is what `dispose` does with an empty run.
- `processCascade_nostops` shows the cascade only sets `lastTradePrice` on a stop-free book.

A crossing post-only order uses the existing `postOnly_reject_agrees`.

## The remaining computation, at the spec's own fuel

```
dm f inc own contra trades tm := doMatch f inc (bidsOf inc.side own contra) (asksOf …) trades tm
rest inc own contra trades tm := dm (matchMeasure contra inc + 1) inc own contra trades tm
```

The fuel of `rest` is the spec's own bound for the state: `computeMatchFuel`
of the state's book is `matchMeasure + 1`. No count taken from the C iteration
counters is involved. Four lemmas carry it:

- **`doMatch_fuel_stable`** (new; the repository had no monotonicity lemma for
  `doMatch`). Any fuel above `matchMeasure` of the contra side gives the same
  result. It is proved by functional induction over all `doMatch` branches,
  including the ones the matcher never reaches: empty level, zero visible, and
  iceberg reload.
- **`rest_start`**: `mrOf b o = rest o1 own contra0 [] tm`, from
  `computeMatchFuel_gt_matchMeasure` and stability.
- **`rest_step`**: if `∀ n, dm (n+1) σ = dm n σ'` and `matchMeasure σ' < matchMeasure σ`,
  then `rest σ = rest σ'`.
- **`rest_step_done`**: the same step into a terminal state.

## Store and locals against the spec state

The locals are the record `Loc` (`sEnv r L` is the side function's
environment). The spec state is `(inc, contra, strades)`.

**Outer boundaries** (`OInv`, `Outer.lean`):

| Clause | Content |
|---|---|
| `inv` | `Inv s` (no empty level) |
| `own` | `absSide (view s) (ownT isBuy) = own` (exact) |
| `spec` | `mr = rest inc own contra strades tm` |
| `cview` | `(absSide (view s) (contraT isBuy)).map levelView = contra.map levelView` |
| `aggr` | `rem.toNat = if inc.status = cancelled then 0 else inc.remainingQty` |
| `shape` | `inc = { o1 with remainingQty, status }` (`IncShape`) |
| `trades` | the trade buffer is `strades.map tradeObs` |
| `tbound` | `trades.length + count s ≤ C0 + [rem = 0]` (the trade buffer never overflows) |
| `cnt`, `hashid`, `remle` | `count s ≤ C0`; no hashed order has the request's id; `rem ≤ qty` |
| `stopT` | `stop → mr = term inc own contra strades tm` |
| `stopX` | `stop → type ≠ MARKET → no contra level crosses the request price` (used for `uncrossed` after resting) |

**Inside an outer iteration on level `l`** (`IInv`, `Inner.lean`). Level `l`
was the best contra level at the iteration's start, where the store view was
`dbR`. The spec split its contra side as `level :: RL`.

| Clause | Content |
|---|---|
| `sinv.inv` | `InvM s l`: `Inv`, except level `l` may be empty |
| `sinv.frame` | `Frame l dbR (view s)`: only level `l`'s queue, the rows queued there, the hash and the live-order list changed |
| `sinv.empty` | `queue l = [] → contra = RL` |
| `sinv.head` | `queue l ≠ [] → contra = level' :: RL` with `levelView level' = levelView (absLevel (view s) t l)` |
| `passive` | `rem ≠ 0 → passive = (queue l).head?` |
| others | as in `OInv`: `spec`, `aggr`, `shape`, `trades`, `tbound`, `cnt`, `hashid`, `remle`, `best = some l`, `stop = false` |

`RL.map levelView = (restSide dbR t l).map levelView` is fixed for the
iteration. `restSide` is the side without `l`, and `absSide_best` splits a
side into its best level and `restSide`. `Frame` keeps `restSide` and the own
side unchanged.

**The cancelled flag.** No result code distinguishes a fully filled incoming
order from one cancelled by STP. Every accepted order returns `accepted`, and
`dispose` treats `remainingQty = 0` and `status = cancelled` alike. So the
flag is folded into `rem = 0` through `aggr`, as the review allowed. No clause
carries the flag separately.

## (a) One inner iteration is one `doMatch` step

`inner_body` rests on `head_facts`: under `IInv` with `rem ≠ 0` and
`queue l = h :: qs`, the spec's head order `resting` has the view of `h`'s row.
From that follow `AtHead`, the row facts and the self-trade test
(`conflict_iff`). Each matcher branch then maps to exactly one `doMatch`
unfolding (`SpecStep.lean`):

| Matcher branch | Spec step | Lemma |
|---|---|---|
| STP, `CANCEL_NEW`: `rem := 0` | `cancelNewest` (terminal) | `inner_cancelNew` / `step_cancelNew` |
| STP, `CANCEL_OLD`: unlink `passive`, `passive := next` | `cancelOldest` | `inner_cancelOld` / `step_cancelOld` |
| STP, `CANCEL_BOTH`: unlink, `rem := 0` | `cancelBoth` (terminal) | `inner_cancelOld` / `step_cancelBoth` |
| STP, `DECREMENT`, resting used up | `decrement`, `restRem = 0` | `inner_dec` / `step_decrement_full` |
| STP, `DECREMENT`, resting keeps some | `decrement`, head updated | `inner_dec` / `step_decrement_part` |
| no conflict, full fill | fill, head removed | `inner_fill` / `step_fill_full` |
| no conflict, partial fill | fill, head updated | `inner_fill` / `step_fill_part` |

No branch failed to map, so there is no ⚑.

Three `doMatch` branches are unreachable under the invariant:

- an empty head level: `sinv.empty` drops it;
- a zero-visible head: `order_ok` gives `remaining > 0`, and visible = remaining;
- an iceberg reload: `displayQty = none`.

## (b) The inner loop

`inner_loop` proves the loop by induction on the measure
`|queue l| + [rem ≠ 0]`. Every iteration either removes the head order or sets
`rem := 0`.

- **Bound.** The measure is at most `count + 1 ≤ capacity + 1`, so the loop never runs into its bound.
- **Exit.** On exit, `rem = 0 ∨ queue l = []`.
- **Trade buffer.** Before each emit, `trades.length < count ≤ capacity`, from `tbound`.

## (c) One outer iteration

`outer_body` covers the three ways an outer iteration can go:

- **No best level.** `tBest = none` means the tree is empty, so `contra = []`. It sets `stop`, and `rest_empty` gives `stopT`.
- **Best level does not cross.** It sets `stop`. `rest_noprice` gives `stopT`; `stopX` holds by `better`.
- **Best level crosses.** `qFirst`, then `inner_loop`, then one of:
  - `queue l = []`: `tRemove` and `levelFree` (`ev_free`). `Inv` comes back from `free_clientInv`, and the decoded contra side is `restSide` (`free_absSide`), which is the spec's `RL`.
  - `queue l ≠ []`, which forces `rem = 0`: no free. `Inv` comes from `InvM.toInv`, and `absSide_best` gives `level' :: RL`.

The measure `|contra tree| + [rem ≠ 0 ∧ ¬stop]` decreases in every case.

## (d) The outer loop

`outer_loop` proves the loop by induction on that measure, which is at most
`levels + 1 ≤ count + 1 ≤ capacity + 1` (`levels_le_count`). On exit:

- `rem = 0` gives `mr = term …` by `rest_done`;
- `stop` gives `mr = term …` by `stopT`.

So `mr.incoming = inc`, `mr.trades = strades`, `mr`'s own side is `own`, and
`mr`'s contra side is `contra` through `levelView`.

## (e) Resting, the result code, the main theorem

- **`rest_run`.** It covers `orderAlloc` and the seven field writes (`rest_prefix`), then `tFind` and either an existing level or `levelAlloc`/`setL`/`tInsert` (`ev_newLevel`), then `qInsertTail` and `hashInsert`. `hashInsert` accepts because of `hashid`. The capacity failure branches are unreachable:
  - `count < capacity` from the entry check;
  - `levelsUsed ≤ count < capacity`.
- **`rest_book`.** Through `levelView`, the own side is `insertDesc`/`insertAsc` of the old side:
  - new price: `insSpec_fresh` against `insLevel`;
  - existing price: `insSpec_exists` against `appAt`;
  - `sortLevels_map` carries both through the sort.
  The contra side is unchanged.
- **`rest_inv`.** `Inv` holds again (`join_clientInv`). The new level is uncrossed by `stopX`.
- **Assembly.** `side_cont` and `side_run` assemble the side function, including the post-only check (`wouldCross_iff`). `refines_accept` adds the entry dispatch, and `matcher_refines` adds the case split over all requests.

## Deviations from the checkpoint report

- **C1, the dropped empty level.** It is not "empty levels filtered from the decoded side". The empty level is handled structurally instead: inside an outer iteration the decoded side is split as level `l` plus `restSide`, and `sinv.empty` says the spec has dropped `l`. No filtered view appears in any statement.
- **Own side.** The own-side clause is exact equality (`absSide … = own`), not view equality. The resting step needs the spec's own list exactly, to run `insertDesc` on it.
- **`stopX`.** It was added. Without it, `uncrossed` for a newly created own level has no premise.

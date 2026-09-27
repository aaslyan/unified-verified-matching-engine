# Plan v2 — Phase 0 Inventory

Date 2026-09-27. Base commit `4811a13`. No code changed in this phase.

## 1. Request-type matrix

Spec: `lean/MatchingEngine/Order.lean` (`OrderType`, `TimeInForce`, flags),
`Process.lean` (`process`), `Cancel.lean`. C: `c/src/matching_engine.c`
(`TYPE_*` in `c/include/matching_engine.h`).

| Request | Spec (`process` / other) | C | In scope (§4 rule) |
|---|---|---|---|
| New limit, rests (GTC) | `orderType := .limit`, `tif := .gtc` | `TYPE_LIMIT` | **yes** |
| Market | `.market` with `tif := .ioc` (WF-12 also allows `.fok`) | `TYPE_MARKET` | **yes** (IOC form) |
| IOC limit | `.limit`, `tif := .ioc` | `TYPE_IOC` | **yes** |
| Post-only | `postOnly := true` on `.limit` | `TYPE_POST_ONLY` | **yes** |
| Cancel | `cancelOrder b oid` (`Cancel.lean:26`), not part of `process` | `MatchingEngine_CancelOrder` | **yes** |
| FOK | `tif := .fok`, Phase 3 pre-check | — | no ⚑ spec-only |
| DAY | `tif := .day` (same as GTC in `process`; no session end is modelled) | — | no ⚑ spec-only |
| Stop limit / stop market | `.stopLimit`, `.stopMarket`, dormant list + cascade | — | no ⚑ spec-only |
| Market-to-limit | `.marketToLimit`, Phase 4 | — | no ⚑ spec-only |
| Iceberg | `displayQty := some d`, reload on fill | — | no ⚑ spec-only |
| Minimum quantity | `minQty := some m`, Phase 3b | — | no ⚑ spec-only |
| Amend (quantity decrease) | `amendQtyDecrease` (`Cancel.lean:35`), not part of `process` | — | no ⚑ spec-only |
| STP modes | `stpPolicy`: cancelNewest / cancelOldest / cancelBoth / decrement | `STP_*` 1–4, NONE = 0 | **yes** |

No C-only request type exists. Every ⚑ row is the same decision: keep the
type out of the generated matcher (the §4 default) or add it to C first.

## 2. Return type of `process`, and the proposed `Obs`

`process : BookState → Order → ProcessResult` (`Process.lean:242`) with
`ProcessResult := { book : BookState, trades : List Trade }`. There is no result
code: a rejected order (post-only crossing, FOK or minimum quantity failing)
returns the input book and no trades. `process` also bumps `nextId` and
`clock` on every call, rejections included. `cancelOrder` returns
`Option BookState`, `none` when the id is not on the book.

`Trade` (`Order.lean:35`): `price`, `qty`, `aggressorId`, `passiveId`,
`aggressorSide`, `aggPostOnly`, `aggStpGroup`, `pasStpGroup`, `aggStpPolicy`.
No timestamp or sequence number on a trade. `Price`, `Quantity`, `OrderId`,
`Timestamp` are `Nat` (`Basic.lean:9-12`). C's `TradeEvent` has
`aggressor_id`, `passive_id`, `price`, `qty` (`uint64_t`).

C's `MatchingEngine_ProcessOrder` returns `false` for: invalid request (qty 0,
price 0 on a priced type, enum out of range), duplicate id among resting
orders, post-only crossing, order or level pool exhausted. `CancelOrder`
returns `false` for an unknown id.

Proposed `Obs`:

```lean
inductive ResultCode
  | accepted | cancelled
  | rejectedInvalid       -- static checks, incl. qty > Qmax (§4)
  | rejectedDuplicate     -- §4: id already resting
  | rejectedCapacity      -- §4: store full and the request may rest
  | rejectedPostOnly      -- post-only would cross
  | rejectedUnknownId     -- cancel of an id not on the book

structure TradeObs where
  makerId : Nat   -- = Trade.passiveId
  takerId : Nat   -- = Trade.aggressorId
  price   : Nat
  qty     : Nat

structure Obs where
  code   : ResultCode
  trades : List TradeObs     -- execution order
  book   : BookView          -- EngineDbAbs.bookView: fields C has
```

`rejectedPostOnly` is not visible in `process`'s output, so `processB` must
decide it with the same test `process` uses (`order.postOnly && wouldCross order b`).
`BookView` already drops `nextId`, `clock`, `lastTradePrice`, timestamps and
status, which C does not store.

## 3. State of the EngineDb files

| File | Contents |
|---|---|
| `lean/Bridge/EngineDbApi.lean` | Abstract store `Db` (functions `orders`, `levels`, `queue`; lists `hash`, `tree`). Operations as relational `pre`/`post`: order/level alloc and free, read/write order and level, `levelCount`, `owner`, hash find/insert/remove, queue insertTail/remove/first/next, tree find/insert/remove/best. `WF` representation invariant. |
| `lean/Bridge/EngineDbApiLaws.lean` | `WF_empty`; every state-changing operation preserves `WF`; determinism of hash find, tree find, tree best; storage laws (find after insert/remove, FIFO insertTail, head after remove, tree find after insert/remove). |
| `lean/Bridge/EngineDbAbs.lean` | C request type and `toSpec`; `processWithId`; `absBook : Db → BookState`; `bookView`; `ClientInv`; `ClientInv ∧ WF → AllInv ∧ BookInvariant` of `absBook`. |

Does the abstract model prove the laws? Partly. The laws are proved about the
relations over `Db`, but no functional implementation of the operations
exists, so there is no instance to witness that the contract is satisfiable
by running code.

Gaps against §4:

| §4 item | Gap |
|---|---|
| `capacity`, `count` | Absent. `Db.orders` is a function, so the number of live orders cannot be computed; a finite live set must be added. |
| insert returns handle or `full` | Alloc may fail at any time (`orderAlloc.post` allows `none` always). Must become: `none` iff `count ≥ capacity`, store unchanged. |
| Validity predicate | Present as `orderLive` / `levelLive`. |
| Per-operation validity laws | Derivable from the `post`s but not stated. |
| Operations plus laws as a class `EngineDb S` | Absent: `Db` is the only store, with no functions and no parameter `S`. |
| Deterministic operations | Absent: relations only. |

## 4. State of CSubset (`../amcc/Amcc/CSubset`, `Codegen/Print.lean`)

`CSubset` lives in the AMCC repository, a Lake dependency, and 35 AMCC files
import it.

| Area | Current |
|---|---|
| Statements | `skip`, `assign`, `seq`, `cond`, `forN` (literal or `u32`-local trip count), `call` (only to a `FunDef` declared earlier in the same program), `ret`. No `while`, `break`, `continue`, `goto`. |
| Expressions | literals, reads of lvalues, `un` (`lnot`, `bnot`), `bin` (`add sub mul band bor bxor eq ne lt le land lor`), `cast`, `null`, `addr`. No division, shift, `min`. |
| Types | `u8`, `u32`, `u64`, `bool`, pointers, structs, arrays. |
| Arithmetic | `add`, `sub`, `mul` **wrap** (`Eval.lean:167`). §4 wants overflow as an error. |
| Memory model | Store with globals, locals, a heap (`Heap`, `allocBlock`, `freeBlock` in `Value.lean`), `null`, freed-block errors. **No statement or expression reaches `allocBlock`/`freeBlock`:** programs cannot allocate. The header row "no `malloc`/`free`" is accurate for the language. |
| Semantics | `execStmt` (fuel), `callFun`, `runCalls`, total, in `Eval.lean`; small-step in `SmallStep.lean`. |
| Printer | `Print.program : Program → String`; fully parenthesised, suffixed literals. |

What the 414 lines of handwritten matcher logic need beyond it:

| Needed | Used in C | In CSubset |
|---|---|---|
| Calls to EngineDb operations defined outside the program | 65 call sites | no: calls only to functions in the same program |
| Opaque handle type | `struct Order *`, `struct PriceLevel *` everywhere | no: pointers are concrete paths |
| Payload get/set through a handle | 85 `->` accesses | only through concrete pointers |
| NULL handle test | `if (!ord)`, `passive != NULL` | `null` exists for pointers |
| Unbounded loops | 4 `while` | no; `forN` only |
| `break` / `continue` | 8 / 4 | no; restructure with flags or `ret` |
| Early return | 16 `return` | yes (`ret`) |
| `min` on `u64` | 5 `min_u64` | no; expressible as `cond` |
| Overflow as error | `total_trades++`, `total_volume +=` | no; wraps |
| Trade callback | `engine->on_trade(...)` | no function pointers; §4 replaces it with a static buffer |

⚑ Where to put the fragment. §5 Phase 2 says "CSubset syntax, semantics and
printer extended". Adding constructors to `CSubset`'s `Stmt`/`Expr` and making
`execStmt` store-parametric changes the AMCC dependency, and every AMCC proof
that recurses over those types would need updating. The alternative is a
separate memory-free language in this repository that reuses `CSubset`'s
scalar types, operators and printing conventions. Decision needed before
Phase 2.

## 5. `sorry` inventory (whole Lake project)

| Location | Declaration | Disposition |
|---|---|---|
| `lean/Bridge/ForwardSimulation.lean:144` | `insert_forward_sim` | replaced in Phase 4, then deleted |
| `lean/Bridge/ForwardSimulation.lean:161` | `match_step_forward_sim` | replaced in Phase 4, then deleted |

No other `sorry` in this repository. None in `../amcc/Amcc`.
`lean/AuditScratch.lean` is not in any build target and was not checked.

Retired without `sorry` but listed in §4: `c_matching_engine_end_to_end_sound`
(`lean/Bridge/EndToEndTheorem.lean`) — delete in Phase 4.

## 6. STP account-0 semantics in the spec

`stpGroupOf 0 = none` and `stpPolicyOf 0 _ = none` (`EngineDbAbs.lean:115-124`),
and `selfTradeConflict inc rest` requires `inc.stpPolicy.isSome` and both groups
`some` and equal (`STP.lean:17`). So two account-0 orders **may trade**, and an
account-0 order never triggers STP against anything. C agrees:
`req->account_id != 0 && req->account_id == passive->account_id`
(`matching_engine.c:50` and `:171`).

## ⚑ Summary

1. Spec-only request types (FOK, DAY, stop, MTL, iceberg, min quantity,
   amend): confirm they stay out of the generated matcher.
2. Where the memory-free fragment lives: extend `CSubset` in AMCC, or a
   separate language in this repository.

## Decisions taken after Phase 0 (2026-09-27)

**Decision 1 — spec-only types stay out, as a rejection.** The generated
matcher supports exactly: LIMIT (rests, GTC), MARKET (IOC), IOC limit,
POST_ONLY, and cancel, with STP modes NONE, CANCEL_NEW, CANCEL_OLD,
CANCEL_BOTH and DECREMENT. The request language is C's `OrderRequest`; every
order-type code outside those four is rejected at entry with
`rejectedUnsupported` and the store unchanged, the same path as duplicate-id
and quantity validation. The refinement theorem therefore quantifies over all
requests. FOK, DAY, stops, market-to-limit, iceberg, minimum quantity and
amend are out; the §4 amend/replace capacity question is closed.

**Decision 2 — a separate memory-free language in this repository.**
`CSubset` is not extended. Phase 2 builds a small language here (locals,
fixed-width arithmetic with overflow as an error, control flow, `forN`,
extern calls into the EngineDb contract, opaque handles with payload get/set;
no arrays, pointers or address-of), with semantics parametric in the store.
Its printer emits the same C dialect as AMCC's and calls only the functions in
`c/gen/engine_db.h`. Linking its semantics to `CSubset` is a Phase 6
obligation (`FRAGMENT.md`).

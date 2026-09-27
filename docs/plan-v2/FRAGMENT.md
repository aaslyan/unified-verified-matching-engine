# The matcher language (Phase 2)

Source: `lean/Matcher/Lang.lean` (syntax and semantics), `lean/Matcher/Print.lean`
(printer), `c/gen/engine_db.h` (the contract's C face), `lean/Matcher/Example.lean`
(a program using every construct), `scripts/matcher_fragment_check.sh`
(prints it and compiles it under gcc and clang).

A separate, memory-free language in this repository (Decision 2), not an
extension of AMCC's `CSubset`. It has no arrays, pointers or address-of:
storage is reached only through extern calls into the EngineDb contract and
through payload reads and writes on opaque handles.

## Types and values

| Type | Values | C | Notes |
|---|---|---|---|
| `u64` | `UInt64` | `uint64_t` | the one integer type: ids, prices, quantities, counts, capacity |
| `code` | `UInt8` | `uint64_t` | enumerations (side, order type, STP mode, result code); equality only |
| `bool` | `Bool` | `bool` | |
| `order` | order handle or null | `ME_OrderH` (opaque pointer) | |
| `level` | level handle or null | `ME_LevelH` (opaque pointer) | |

No narrow integer type exists, so C's integer promotion never applies.

## Expressions

| Construct | Semantics | C |
|---|---|---|
| `lit n`, `clit c`, `blit b` | the literal | `UINT64_C(n)`, `UINT64_C(c)`, `true`/`false` |
| `var x` | the local's value; `unbound` if absent | `x` |
| `un .not e` | Boolean negation | `(!e)` |
| `bin .add/.sub/.mul` on `u64` | exact result; **`overflow` error** if it leaves `[0, 2^64)` | `me_add/me_sub/me_mul(a, b)`, which trap on overflow |
| `bin .eq/.ne` | on `u64`, `code`, `bool`, and handles of one kind | `(a == b)`, `(a != b)` |
| `bin .lt/.le` | on `u64` only | `(a < b)`, `(a <= b)` |
| `bin .and/.or` | on `bool` | `(a && b)`, `(a \|\| b)` |
| `nullO`, `nullL` | the null handle | `((ME_OrderH)NULL)` |
| `isNullO e`, `isNullL e` | is the handle null | `(e == NULL)` |
| `getO e f` | field `f` of the order row; **`invalidHandle`** if null or dead | `ME_order_get_f(e)` |
| `getL e .price`, `getL e .count` | level price; queue length | `ME_level_get_price(e)`, `ME_level_get_count(e)` |

Any other operand combination is a `type` error.

## Statements

| Construct | Semantics | C |
|---|---|---|
| `skip` | nothing | nothing |
| `seq a b` | `a`, then `b` unless `a` returned | `a b` |
| `assign x e` | set an existing local; its type must not change | `x = e;` |
| `ite c a b` | branch on a `bool` | `if ((bool)c) { a } else { b }` |
| `loop n c body` | while `c`, at most `n` iterations; **`bound` error** if `c` still holds after `n` | `for (k = 0;; k++) { if (!c) break; if (k == n) me_trap(); body }` |
| `ext dst op args` | EngineDb operation `op`; its contract precondition is checked on the store's view and a violation is a **`contract` error** | a call to the matching `engine_db.h` function |
| `call dst f args` | call a function defined in the program; fresh locals; its return value | `dst = f(args);` |
| `emit m t p q` | append trade (maker, taker, price, qty); **`tradeBuffer` error** when full | `me_emit(m, t, p, q);` (traps when full) |
| `ret e` | return | `return e;` |

A function that ends without `ret` is a `noReturn` error; its printed body
ends in `me_trap()`. Call nesting is bounded by `fuel` (`fuel` error).

## Extern operations and their contract checks

| Op | Contract precondition checked | C |
|---|---|---|
| `orderAlloc`, `levelAlloc` | none; returns null when the pool is full | `ME_order_alloc()`, `ME_level_alloc()` |
| `orderFree h` | live; in no queue; not hashed | `ME_order_free` |
| `levelFree l` | live; in no tree; empty queue | `ME_level_free` |
| `setO f h v` | live; `id` only while not hashed; `v` a `u64` or a `code` as the field requires | `ME_order_set_f` |
| `setL .price l v` | live; only while in no tree | `ME_level_set_price` |
| `hashFind id` | none | `ME_hash_find` |
| `hashInsert h` | live; not hashed; returns false if the id is present | `ME_hash_insert` |
| `hashRemove h` | live; hashed | `ME_hash_remove` |
| `qInsertTail l h` | both live; `h` in no queue | `ME_queue_insert_tail` |
| `qRemove l h` | both live; `h` in `l`'s queue | `ME_queue_remove` |
| `qFirst l` | live | `ME_queue_first` |
| `qNext h` | live; in some queue | `ME_queue_next` |
| `owner h` | live | `ME_order_owner` |
| `tFind t p` | none | `ME_bids_find`, `ME_asks_find` |
| `tInsert t l` | live; in no tree; its price not already in `t` | `ME_bids_insert`, `ME_asks_insert` |
| `tRemove t l` | live; in `t` | `ME_bids_remove`, `ME_asks_remove` |
| `tBest t` | none | `ME_bids_best`, `ME_asks_best` |

These are exactly the `pre`s of `lean/Bridge/EngineDbApi.lean`, decided on the
view. A run that ends `.ok` made no contract violation, used no invalid
handle, did not overflow, and did not exhaust a loop bound.

## Semantics

`execStmt (P : Program) (fuel) (s : Stmt) (st : St S)` for any `S` with
`[EngineDb S]`: the store is a parameter, and storage is touched only through
the class's operations and `view`. `runEntry` runs an entry function from a
store and returns the result, the final store and the trades. The semantics
is executable (it ran the example on the model store) and uses no axioms.

The printed C checks overflow, loop bounds and the trade buffer, and traps on
failure. It does not re-check handle contracts; the proof rules those out
(Phase 4), and the data layer is tested against the contract (Phase 5).

## Obligations carried forward

- **Phase 4.** Level-pool sizing (`levelAlloc` fails iff `levelsUsed ≥ capacity`)
  is safe only under "no empty level in the store", hence levels ≤ orders.
  Both go into `Inv`, and the Phase 3 matcher must free a level when its last
  order leaves.
- **Phase 4.** Overflow stays an error in the semantics. It is discharged from
  the Phase 1 bounds (`qty ≤ qmax cap`, `(cap + 1) · qmax cap < 2^64`): fills are
  at most both operands, so subtractions never underflow; sums are bounded by
  the product; prices and ids are only compared.
- **Phase 3.** The handwritten data layer stores `side` and `stp_mode` as
  `uint8_t` and keeps `total_qty`. Behind `engine_db.h` the side and STP-mode
  fields are widened to `uint64_t` (an edit to list in STATUS, not a range
  check), and `ME_order_set_remaining` must maintain the owner level's
  `total_qty`, which the contract no longer mentions.
- **Phase 6.** Linking this semantics to `CSubset`: running the matcher program
  with the store instantiated by the AMCC-generated data layer must equal
  running the whole generated C program under `CSubset` semantics. Until then,
  the claim is about this language's semantics. Both printers emit the same
  dialect (`<stdint.h>` types, `UINT64_C` literals, full parenthesisation), so
  the two halves link through `engine_db.h`.

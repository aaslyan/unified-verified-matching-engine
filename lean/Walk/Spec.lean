import Bridge.ProcessB

/-!
# The walking spec

`Walk.process` is the printed matcher (`c/gen/matcher.c`, from
`MatcherProgram.program`) transliterated, statement by statement, to act on
the reference `BookState` instead of the store. It has no authority of its
own: `Walk.process_obs_eq` (A2) ties it to `processB`, the spec step of
record.

Transliteration rules (PLAN-W §3, as agreed at A0):

* every store call → a Book primitive below, one per call;
* every local → a `State` field or a `let`; the handle locals are derived:
  `best` is the head level of the contra side, `passive` its head order
  (they are that while the inner loop test holds; STATUS-W A0 §3);
* `ME_trade_emit` → `trades := trades ++ [t]`, `t` a reference `Trade`;
* the bounded loop → `innerRun` / `outerRun`, with the language's order of
  tests: test, then bound; the bound exhausted with the test still true is
  `none` (the program's `me_trap(2)`); a full trade buffer is `none`
  (`me_trap(3)`); a `cap + 1` that does not fit `uint64_t` is `none`
  (`me_add` traps, `me_trap(1)`).

The program has no `break` and no `continue`: every loop exits through its
test. So one inner iteration is `State → Option State`, `none` only for a
trap; PLAN-W's `Next.done` would never be produced.

Quantities are `Nat`. The program's `me_sub(rem, fill)` and
`me_sub(get_remaining(passive), fill)` subtract `fill = min(rem, remaining)`
and cannot underflow; they are Nat subtraction here (A3 discharges it).

The C line ↔ Lean line table is at the end of the file.
-/

namespace Walk

open EngineDbApi EngineDbAbs ProcessB

-- ============================================================================
-- Book primitives: one per store call
-- ============================================================================

/-- The levels of one tree, best first. -/
def sideL (b : BookState) : Tree → List PriceLevel
  | .bids => b.bids
  | .asks => b.asks

def setSideL (b : BookState) : Tree → List PriceLevel → BookState
  | .bids, ls => { b with bids := ls }
  | .asks, ls => { b with asks := ls }

/-- Change the head level of a list. -/
def modHead (f : PriceLevel → PriceLevel) : List PriceLevel → List PriceLevel
  | [] => []
  | l :: ls => f l :: ls

/-- Change the first level at price `p`. -/
def modAt (p : Nat) (f : PriceLevel → PriceLevel) : List PriceLevel → List PriceLevel
  | [] => []
  | l :: ls => if l.price = p then f l :: ls else l :: modAt p f ls

/-- `ME_asks_best` / `ME_bids_best`. -/
def tBest (b : BookState) (t : Tree) : Option PriceLevel := (sideL b t).head?

/-- `ME_queue_first(best)`. -/
def qFirst (l : PriceLevel) : Option Order := l.orders.head?

/-- `ME_level_get_count`. -/
def levelCount (l : PriceLevel) : Nat := l.orders.length

/-- `ME_order_get_account`: the row's account. The Book keeps it as the STP
    group, `stpGroupOf account` (`none` exactly for account 0). -/
def getAccount (o : Order) : Nat := o.stpGroup.getD 0

/-- `ME_order_set_remaining` on the head order of the best level. The C row
    has one quantity field; the Book order has `remainingQty` and
    `visibleQty`, equal on every order the C can hold, so both are written. -/
def setHeadRem (b : BookState) (t : Tree) (q : Nat) : BookState :=
  setSideL b t <| modHead (fun l =>
    { l with orders := match l.orders with
      | [] => []
      | o :: os => { o with remainingQty := q, visibleQty := q } :: os }) (sideL b t)

/-- `ME_queue_remove(best, head); ME_hash_remove(head); ME_order_free(head)`:
    pop the head order of the best level. The level stays, possibly empty,
    until the outer loop's cleanup. The hash and the pool have no Book
    counterpart beyond the order leaving the queue. -/
def popHead (b : BookState) (t : Tree) : BookState :=
  setSideL b t (modHead (fun l => { l with orders := l.orders.tail }) (sideL b t))

/-- `ME_*_remove(best); ME_level_free(best)`: drop the best level. -/
def dropBest (b : BookState) (t : Tree) : BookState :=
  setSideL b t (sideL b t).tail

/-- `ME_order_count()`: live order rows, the orders on the levels. -/
def count (b : BookState) : Nat := (allBookOrders b).length

/-- Live level rows: the levels in the two trees. -/
def levelsUsed (b : BookState) : Nat := b.bids.length + b.asks.length

/-- `ME_hash_find(id)`: the order with that id, bids searched first. -/
def hashFind (b : BookState) (id : Nat) : Option Order :=
  (allBookOrders b).find? (·.id = id)

/-- `ME_order_owner(ord)`: the tree and level whose queue holds `o`. A handle
    names one order; on the Book an order is named by its id, which the hash
    keeps unique. -/
def owner (b : BookState) (o : Order) : Option (Tree × PriceLevel) :=
  match b.bids.find? (fun l => l.orders.any (·.id = o.id)) with
  | some l => some (.bids, l)
  | none => (b.asks.find? (fun l => l.orders.any (·.id = o.id))).map (.asks, ·)

/-- `ME_queue_remove(lvl, ord)`, `lvl` the level at price `p` of tree `t`. -/
def qRemove (b : BookState) (t : Tree) (p : Nat) (o : Order) : BookState :=
  setSideL b t (modAt p (fun l => { l with orders := l.orders.eraseP (·.id = o.id) }) (sideL b t))

/-- `ME_queue_remove(lvl, ord)` for the order just appended at the tail. -/
def qRemoveTail (b : BookState) (t : Tree) (p : Nat) : BookState :=
  setSideL b t (modAt p (fun l => { l with orders := l.orders.dropLast }) (sideL b t))

/-- `ME_*_remove(lvl); ME_level_free(lvl)`, `lvl` the level at price `p`. -/
def tRemove (b : BookState) (t : Tree) (p : Nat) : BookState :=
  setSideL b t ((sideL b t).eraseP (·.price = p))

/-- `ME_*_find(price)`. -/
def tFind (b : BookState) (t : Tree) (p : Nat) : Option PriceLevel :=
  (sideL b t).find? (·.price = p)

/-- `lvl = ME_level_alloc(); ME_level_set_price(lvl, p); ME_*_insert(lvl)`:
    an empty level at price `p`, in tree order. -/
def tInsertNew (b : BookState) (t : Tree) (p : Nat) : BookState :=
  setSideL b t (insLevel t { price := p, orders := [] } (sideL b t))

/-- `ME_queue_insert_tail(lvl, ord)`, `lvl` the level at price `p`. -/
def qInsertTail (b : BookState) (t : Tree) (p : Nat) (o : Order) : BookState :=
  setSideL b t (modAt p (fun l => { l with orders := l.orders ++ [o] }) (sideL b t))

-- ============================================================================
-- The matching phase
-- ============================================================================

/-- The parameters of `gen_process_buy` / `gen_process_sell`, and the side. -/
structure Ctx where
  cap   : Nat
  r     : CRequest
  isBuy : Bool

def Ctx.contra (c : Ctx) : Tree := if c.isBuy then .asks else .bids
def Ctx.own (c : Ctx) : Tree := if c.isBuy then .bids else .asks

/-- `crosses bp` of `sideFun`: best contra price `bp` is marketable against
    the order's limit price. -/
def Ctx.crosses (c : Ctx) (bp : Nat) : Bool :=
  if c.isBuy then decide (bp ≤ c.r.price.toNat) else decide (c.r.price.toNat ≤ bp)

/-- The value of the bound `capacity + 1`; `none` where `me_add` traps. -/
def Ctx.bound (c : Ctx) : Option Nat :=
  if c.cap + 1 < 2 ^ 64 then some (c.cap + 1) else none

/-- The loop state: the locals the loops write, over the Book. -/
structure State where
  book   : BookState
  rem    : Nat
  stop   : Bool
  trades : List Trade

/-- The reference trade for a fill of `q` against resting `p` at `price`.
    `ME_trade_emit` receives `(get_id(passive), id, get_price(best), fill)`;
    the other five fields are the aggressor's, from the request, and the
    passive's STP group. -/
def mkTrade (c : Ctx) (p : Order) (price q : Nat) : Trade :=
  { price := price, qty := q, aggressorId := c.r.id.toNat, passiveId := p.id,
    aggressorSide := if c.isBuy then .buy else .sell,
    aggPostOnly := c.r.orderType = 3,
    aggStpGroup := stpGroupOf c.r.account, pasStpGroup := p.stpGroup,
    aggStpPolicy := stpPolicyOf c.r.account c.r.stpMode }

/-- The inner loop test: `passive ≠ NULL ∧ 0 < rem`. -/
def innerTest (c : Ctx) (st : State) : Bool :=
  ((tBest st.book c.contra).bind qFirst).isSome && decide (0 < st.rem)

/-- One inner iteration (C:111-153). `none`: the trade buffer is full. -/
def innerStep (c : Ctx) (st : State) : Option State :=
  match tBest st.book c.contra with
  | none => some st                                    -- unreachable under innerTest
  | some best =>
  match qFirst best with
  | none => some st                                    -- unreachable under innerTest
  | some passive =>
  if c.r.account ≠ 0 ∧ c.r.account.toNat = getAccount passive ∧ c.r.stpMode ≠ 0 then
    if c.r.stpMode = 1 then
      some { st with rem := 0 }
    else if c.r.stpMode = 2 ∨ c.r.stpMode = 3 then
      let b1 := popHead st.book c.contra
      if c.r.stpMode = 3 then some { st with book := b1, rem := 0 }
      else some { st with book := b1 }
    else
      let fill := min st.rem passive.remainingQty
      let rem := st.rem - fill
      let prem := passive.remainingQty - fill
      let b1 := setHeadRem st.book c.contra prem
      let b2 := if prem = 0 then popHead b1 c.contra else b1
      some { st with book := b2, rem := rem }
  else
    let fill := min st.rem passive.remainingQty
    let rem := st.rem - fill
    let prem := passive.remainingQty - fill
    let b1 := setHeadRem st.book c.contra prem
    if st.trades.length < c.cap + 1 then
      let trades := st.trades ++ [mkTrade c passive best.price fill]
      let b2 := if prem = 0 then popHead b1 c.contra else b1
      some { st with book := b2, rem := rem, trades := trades }
    else none

/-- The inner loop with `n` iterations left. -/
def innerRun (c : Ctx) : Nat → State → Option State
  | 0, st => if innerTest c st then none else some st
  | n + 1, st => if innerTest c st then (innerStep c st).bind (innerRun c n) else some st

/-- The outer loop test: `0 < rem ∧ ¬stop`. -/
def outerTest (st : State) : Bool := decide (0 < st.rem) && !st.stop

/-- One outer iteration (C:100-162). -/
def outerStep (c : Ctx) (st : State) : Option State :=
  match tBest st.book c.contra with
  | none => some { st with stop := true }
  | some best =>
  if c.r.orderType ≠ 1 ∧ ¬ c.crosses best.price then some { st with stop := true }
  else do
    let n ← c.bound
    let st' ← innerRun c n st
    -- `best` is still the head: the inner loop edits only its queue.
    match tBest st'.book c.contra with
    | some best' =>
      if levelCount best' = 0 then some { st' with book := dropBest st'.book c.contra }
      else some st'
    | none => some st'                                -- unreachable

/-- The outer loop with `n` iterations left. -/
def outerRun (c : Ctx) : Nat → State → Option State
  | 0, st => if outerTest st then none else some st
  | n + 1, st => if outerTest st then (outerStep c st).bind (outerRun c n) else some st

/-- The row C writes when the remainder rests (C:170-176), as a Book order.
    Fields the row does not have take the values decoding gives them. -/
def restOrder (c : Ctx) (rem : Nat) : Order :=
  { id := c.r.id.toNat, stpGroup := stpGroupOf c.r.account,
    side := if c.r.side = 0 then .buy else .sell,
    stpPolicy := stpPolicyOf c.r.account c.r.stpMode,
    price := some c.r.price.toNat, qty := c.r.qty.toNat,
    remainingQty := rem, visibleQty := rem,
    orderType := .limit, tif := .gtc, stopPrice := none, minQty := none,
    displayQty := none, postOnly := false, status := .new_, timestamp := 0 }

/-- Rest the remainder (C:164-205): the result code and the book. -/
def rest (c : Ctx) (st : State) : ResultCode × BookState :=
  if 0 < st.rem ∧ c.r.orderType ≠ 2 ∧ c.r.orderType ≠ 1 then
    if c.cap ≤ count st.book then (.rejectedCapacity, st.book)
    else
      let o := restOrder c st.rem
      let p := c.r.price.toNat
      let placed : Option (BookState × Bool) :=
        match tFind st.book c.own p with
        | some _ => some (st.book, false)
        | none =>
          if c.cap ≤ levelsUsed st.book then none
          else some (tInsertNew st.book c.own p, true)
      match placed with
      | none => (.rejectedCapacity, st.book)
      | some (b1, isnew) =>
        let b2 := qInsertTail b1 c.own p o
        if (hashFind st.book c.r.id.toNat).isSome then
          let b3 := qRemoveTail b2 c.own p
          let b4 := if isnew ∧ ((tFind b3 c.own p).map levelCount) = some 0
            then tRemove b3 c.own p else b3
          (.rejectedDuplicate, b4)
        else (.accepted, b2)
  else (.accepted, st.book)

/-- The post-only test's book part (C:89-90): `best = ME_*_best()`, then
    `best ≠ NULL ∧ crosses(get_price(best))`. -/
def postOnlyCross (c : Ctx) (b : BookState) : Bool :=
  match tBest b c.contra with
  | some best => c.crosses best.price
  | none => false

/-- `gen_process_buy` / `gen_process_sell`. -/
def sideProc (c : Ctx) (b : BookState) : Option (ResultCode × ProcessResult) :=
  if c.r.orderType = 3 ∧ postOnlyCross c b = true then
    some (.rejectedPostOnly, { book := b, trades := [] })
  else do
    let n ← c.bound
    let st ← outerRun c n { book := b, rem := c.r.qty.toNat, stop := false, trades := [] }
    let (code, b') := rest c st
    some (code, { book := b', trades := st.trades })

-- ============================================================================
-- Entry points
-- ============================================================================

def reject (code : ResultCode) (b : BookState) : Option (ResultCode × ProcessResult) :=
  some (code, { book := b, trades := [] })

/-- `gen_process_order`: the entry checks, then the side. -/
def processOrder (cap : Nat) (b : BookState) (r : CRequest) : Option (ResultCode × ProcessResult) :=
  if ¬ (r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3) then
    reject .rejectedUnsupported b
  else if ¬ (r.side = 0 ∨ r.side = 1) then reject .rejectedInvalid b
  else if ¬ (r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4) then
    reject .rejectedInvalid b
  else if r.qty = 0 then reject .rejectedInvalid b
  else if r.orderType ≠ 1 ∧ r.price = 0 then reject .rejectedInvalid b
  else if ¬ (cap + 1 < 2 ^ 64) then none
  else if qmax cap < r.qty.toNat then reject .rejectedInvalid b
  else if (hashFind b r.id.toNat).isSome then reject .rejectedDuplicate b
  else if (r.orderType = 0 ∨ r.orderType = 3) ∧ cap ≤ count b then reject .rejectedCapacity b
  else sideProc { cap := cap, r := r, isBuy := r.side = 0 } b

/-- `gen_cancel_order`. -/
def cancel (b : BookState) (id : UInt64) : ResultCode × ProcessResult :=
  match hashFind b id.toNat with
  | none => (.rejectedUnknownId, { book := b, trades := [] })
  | some o =>
  match owner b o with
  | none => (.rejectedUnknownId, { book := b, trades := [] })
  | some (t, lvl) =>
    let side := o.side
    let b1 := qRemove b t lvl.price o
    let b2 :=
      if (tFind b1 t lvl.price).map levelCount = some 0 then
        tRemove b1 (if side = .buy then .bids else .asks) lvl.price
      else b1
    (.cancelled, { book := b2, trades := [] })

/-- The walking spec step. `none`: the program traps. -/
def process (cap : Nat) (b : BookState) : Req → Option (ResultCode × ProcessResult)
  | .order r => processOrder cap b r
  | .cancel id => some (cancel b id)

/-!
## C line ↔ Lean line

C lines are `c/gen/matcher.c` at `gen_process_buy` (C:56-207); `gen_process_sell`
is the same text with the trees swapped (`Ctx.contra` / `Ctx.own`). Lean lines
are this file. Store calls with no Book effect (`ME_hash_remove`,
`ME_order_free` after a queue removal, `ME_level_free` after a tree removal) are
folded into the primitive of the call before them.

### Inner iteration (`innerStep`, C:111-153)

| C | statement | Lean |
|---|---|---|
| 109 | loop test `passive ≠ NULL ∧ 0 < rem` (`passive` = head of `best`) | 180-181 `innerTest` |
| 110 | `me_k1 == me_n1 → me_trap(2)` | 218 `innerRun 0` → `none` |
| 111 | STP test: `account ≠ 0 ∧ account = get_account(passive) ∧ stp ≠ NONE` | 185-191 (`tBest`, `qFirst`, `getAccount`) |
| 112-113 | `CANCEL_NEW`: `rem = 0` | 192-193 |
| 115 | `CANCEL_OLD ∨ CANCEL_BOTH` | 194 |
| 116-120 | `victim = passive; passive = next; queue_remove; hash_remove; order_free` | 195 `popHead` |
| 121-122 | `CANCEL_BOTH`: `rem = 0` | 196-197 |
| 126 | `fill = min(rem, get_remaining(passive))` | 199 |
| 127 | `rem = me_sub(rem, fill)` | 200 |
| 128 | `prem = me_sub(get_remaining(passive), fill)` | 201 |
| 129 | `set_remaining(passive, prem)` | 202 `setHeadRem` |
| 130, 137 | `nextp = queue_next(passive)`; `passive = nextp` | derived (head of `best`) |
| 131-134 | `prem = 0`: `queue_remove; hash_remove; order_free` | 203 `popHead` |
| 141 | `fill = min(rem, get_remaining(passive))` | 206 |
| 142 | `rem = me_sub(rem, fill)` | 207 |
| 143 | `prem = me_sub(get_remaining(passive), fill)` | 208 |
| 144 | `set_remaining(passive, prem)` | 209 `setHeadRem` |
| 145 (39-43) | `me_emit(get_id(passive), id, get_price(best), fill)`; buffer full → `me_trap(3)` | 210-211, 214 `mkTrade` |
| 146, 153 | `nextp = queue_next(passive)`; `passive = nextp` | derived |
| 147-150 | `prem = 0`: `queue_remove; hash_remove; order_free` | 212 `popHead` |

### Outer iteration (`outerStep`, C:98-162) and the loops

| C | statement | Lean |
|---|---|---|
| 97, 108 | bound `me_add(ME_capacity(), 1)` (`me_trap(1)` on overflow) | 158-159 `Ctx.bound`; 231 |
| 98 | loop test `0 < rem ∧ ¬stop` | 222 `outerTest` |
| 99 | `me_k0 == me_n0 → me_trap(2)` | 242 `outerRun 0` → `none` |
| 100 | `best = ME_asks_best()` | 226 `tBest` |
| 101-102 | `best == NULL`: `stop = true` | 227 |
| 104-105 | `otype ≠ MARKET ∧ ¬(get_price(best) ≤ price)`: `stop = true` | 229 (`Ctx.crosses`, 154-155) |
| 107 | `passive = ME_queue_first(best)` | derived (`qFirst`) |
| 108-155 | the inner loop | 232 `innerRun` |
| 156 | `get_count(best) == 0` (`best` still the head level) | 234-236 `levelCount` |
| 157-158 | `ME_asks_remove(best); ME_level_free(best)` | 236 `dropBest` |

### Matching phase (`sideProc`, C:88-96, 164-205) and rest (`rest`)

| C | statement | Lean |
|---|---|---|
| 88-93 | post-only: `best = ME_asks_best()`; crossing → `return 6` | 283-286 `postOnlyCross`, 290-291 |
| 96 | `rem = qty` | 294 |
| 97-163 | outer loop | 294 `outerRun` |
| 164 | `0 < rem ∧ otype ≠ IOC ∧ otype ≠ MARKET` | 258 |
| 165-167 | `ord = ME_order_alloc()`; `NULL` (iff `capacity ≤ count`) → `return 5` | 259 `count` |
| 170-176 | `ME_order_set_{id,account,side,stp_mode,price,qty,remaining}` | 261 `restOrder` (247-254) |
| 177 | `lvl = ME_bids_find(price)` | 264 `tFind` |
| 179-182 | `ME_level_alloc()`; `NULL` (iff `capacity ≤ levelsUsed`) → `order_free; return 5` | 267, 270 `levelsUsed` |
| 185-187 | `level_set_price; ME_bids_insert; isnew = true` | 268 `tInsertNew` |
| 190 | `ME_queue_insert_tail(lvl, ord)` | 272 `qInsertTail` |
| 191 | `ok = ME_hash_insert(ord)` (fails iff the id is hashed) | 273 `hashFind` |
| 193 | `ME_queue_remove(lvl, ord)` | 274 `qRemoveTail` |
| 194-196 | `isnew ∧ get_count(lvl) = 0`: `ME_bids_remove; ME_level_free` | 275-276 `tRemove` |
| 199-200 | `order_free; return 4` | 277 |
| 205 | `return 0` | 278-279 |

### Entry points (`processOrder`, C:362-416; `cancel`, C:418-453)

| C | statement | Lean |
|---|---|---|
| 374-375 | `me_ntrades = 0; ME_trade_reset()` | `trades := []` (294, 303) |
| 376-377 | order type not LIMIT/MARKET/IOC/POST_ONLY → `return 2` | 307-308 |
| 380-381 | side out of range → `return 3` | 309 |
| 384-385 | STP mode out of range → `return 3` | 310-311 |
| 388-389 | `qty == 0` → `return 3` | 312 |
| 392-393 | `otype ≠ MARKET ∧ price == 0` → `return 3` | 313 |
| 396-397 | `me_add` traps; `qmax < qty` → `return 3` | 314, 315 |
| 400-402 | `ME_hash_find(id) ≠ NULL` → `return 4` | 316 `hashFind` |
| 405-406 | `(LIMIT ∨ POST_ONLY) ∧ capacity ≤ ME_order_count()` → `return 5` | 317 `count` |
| 409-414 | dispatch on side | 318 |
| 428-430 | `ord = ME_hash_find(id)`; `NULL` → `return 7` | 322-323 `hashFind` |
| 433-435 | `lvl = ME_order_owner(ord)`; `NULL` → `return 7` | 325-326 `owner` |
| 438 | `side = get_side(ord)` | 328 |
| 439-441 | `queue_remove(lvl, ord); hash_remove; order_free` | 329 `qRemove` |
| 442-448 | `get_count(lvl) == 0`: remove from the tree of `side`; `level_free` | 330-333 `tRemove` |
| 451 | `return 1` | 334 |
-/

end Walk

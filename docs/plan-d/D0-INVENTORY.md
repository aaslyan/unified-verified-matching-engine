# Plan D — D0 inventory

Reference commits: unified `9bfceb1` (main), amcc `5e0dbf8` (main). Everything below was read from source at those commits. `file:line` references into AMCC are relative to `amcc/Amcc/`.

Headline: AMCC has proved pieces of three of the five structures the contract needs, for toy schemas or with a single instance per program. No generator can emit the client schema today. The tree does not exist beyond stub code.

---

## 1. Contract table

Lean operations and laws are in `lean/Bridge/EngineDbApi.lean:316-412`. The C calls are `c/gen/engine_db.h` (41 calls), implemented by `c/gen/engine_db_adapter.c` over `c/src/matching_engine_gen.c`.

"Template theorem" means the existing AMCC theorem that would discharge the law once instantiated. `MISSING` means no such theorem exists. "partial" means a theorem exists but covers only part of the law or a narrower configuration (noted).

| # | `ME_*` call | Contract op / law(s) | C today | AMCC template.op | Template theorem |
|---|---|---|---|---|---|
| 1 | `ME_capacity` | `EngineDb.capacity` (a class constant); `.capacity` expr in `Matcher/Lang.lean` | `g_cap` (adapter) | client constant / schema attr | none needed (a constant) |
| 2 | `ME_order_count` | `count`; `init_count`; the 12 `count_*` frames | `order_pool_n` | pool `N` | partial: `Pool.size_correct` (`Templates/Pool.lean:211`), Inlary only; heap pool MISSING |
| 3 | `ME_trade_reset` | none (matcher output, not store) | adapter buffer | — | out of scope: printer/linking trust (§8) |
| 4 | `ME_trade_emit` | none (as 3) | adapter buffer | — | out of scope (§8) |
| 5 | `ME_order_alloc` | `orderAlloc_law` (post, and `none ↔ capacity ≤ count`); `count_orderAlloc`; `levelsUsed_orderAlloc` | free list / bump; NULL if `n ≥ cap` | pool `Alloc` + capacity guard | partial: `Pool.alloc_correct` (`Pool.lean:244`), success with a non-empty free list only. Failure branch and `none ↔ full` MISSING (`PoolInv` has no completeness clause). `RowFresh` (`:159`) is never established. Heap pool MISSING |
| 6 | `ME_order_free` | `orderFree_law`; `count_orderFree`; `levelsUsed_orderFree` | push on free list | pool `Free`/`Delete` | MISSING (`freeDef` `Pool.lean:115` has no theorem) |
| 7 | `ME_level_alloc` | `levelAlloc_law` (`none ↔ capacity ≤ levelsUsed`); `levelsUsed_levelAlloc`; `count_levelAlloc` | as 5 | second pool `Alloc` | as 5. Also MISSING: a second pool per root (generators take the first field of a reftype) |
| 8 | `ME_level_free` | `levelFree_law`; `levelsUsed_levelFree`; `count_levelFree` | as 6 | second pool `Free` | MISSING |
| 9–15 | `ME_order_get_{id,account,side,stp_mode,price,qty,remaining}` | `readOrder_law` (unconditional: `readOrder s h = (view s).orders h`) | field read | plain `Val` field through the row pointer (amc emits no getter) | no template. Needs an instance lemma: the row fields decode to the ghost row (§4) |
| 16–22 | `ME_order_set_{…}` (7) | `writeOrder_law` (whole row; `id` frozen while hashed); `count_writeOrder`; `levelsUsed_writeOrder` | field write; `set_remaining` also adjusts `total_qty` | plain `Val` field write | no template. Needs an instance lemma, plus a composition lemma: a payload write preserves `TailListInv`, `Thash.RepInv` (keys only for chained rows) and the tree invariant. MISSING |
| 23 | `ME_level_get_price` | `readLevel_law` | field read | `Val`/`Pkey` field | as 9 |
| 24 | `ME_level_get_count` | `levelCount_law` (= queue length) | `orders_n` | per-parent `Llist` `N` | partial: `Llist.size_correct` (`Templates/Llist.lean:878`) is for the root list only. Per-parent MISSING |
| 25 | `ME_level_set_price` | `writeLevel_law` (price frozen while in a tree); frames | field write | `Pkey` field write | as 16 |
| 26 | `ME_hash_find` | `hashFind_law` | chain walk | `Thash.Find` | partial: `find_hit_unique` / `find_miss_unique` (`Templates/ThashRefine.lean:134/168`) take **u32** keys only. u64 MISSING (`genThash` rejects u64: `Thash.lean:348`, check `:745`) |
| 27 | `ME_hash_insert` | `hashInsert_law` (duplicate id → false, unchanged); frames | chain push | `Thash.InsertMaybe` | partial: `insert_success` (`ThashRefine.lean:1015`), `insert_duplicate_reject` (`:215`), `insert_inlist_reject` (`:201`). u32 only. `insert_success` also takes `hfits` (bucket length < cap) as a hypothesis |
| 28 | `ME_hash_remove` | `hashRemove_law`; frames | chain unlink | `Thash.Remove` | MISSING (only `remove_noop`, `Thash.lean:450`) |
| 29 | `ME_queue_insert_tail` | `qInsertTail_law`; frames | intrusive DLL append; sets `p_price_level` | per-parent `Llist.InsertTail` + `Upptr.Set` | partial: `Llist.insertTail_correct` (`Llist.lean:2879`) for the root list, plus `Upptr.get_set` (`Templates/Upptr.lean:333`). Per-parent MISSING |
| 30 | `ME_queue_remove` | `qRemove_law`; frames | DLL unlink | per-parent `Llist.Remove` + `Upptr.Set NULL` | partial: `Llist.remove_correct` (`:2905`), root list. Per-parent MISSING |
| 31 | `ME_queue_first` | `qFirst_law` | `orders_head` | per-parent `Llist.First` | partial: `first_correct` (`:863`), root list |
| 32 | `ME_queue_next` | `qNext_law` (`nextIn`) | `orders_next` | `Llist.Next` | partial: `next_correct` (`:949`); needs the per-parent invariant |
| 33 | `ME_order_owner` | `owner_law` (`some l ↔ h ∈ queue l`) | `inlist ? p_price_level : NULL` | `Upptr.Get` + inlist flag | partial: `Upptr.get_correct` (`:272`). The invariant "Upptr = owning list" is MISSING (composition) |
| 34–37 | `ME_bids_{find,insert,remove,best}` | `tFind_law`, `tInsert_law`, `tRemove_law`, `tBest_law` (best = highest); `count_t*`, `levelsUsed_t*` | unbalanced BST | `Atree` `Find`/`Insert`/`Remove`/`Last` | MISSING (`Templates/Atree.lean` emits stub bodies, no theorems) |
| 38–41 | `ME_asks_{…}` | same laws; best = lowest | unbalanced BST | second `Atree`, `First` | MISSING; also a second Atree field per root |

Contract items with no `ME_*` call:
- `init` / `init_view` / `init_count` / `init_levelsUsed` correspond to `ME_adapter_init(capacity)`, which is not in the header (§5).
- `levelsUsed` has no C getter; it is used only in proofs.

Frame laws. There are 24: 12 `count_*` and 12 `levelsUsed_*`, some unconditional (e.g. `count_levelFree : ∀ s l, count (levelFree s l) = count s`, with no precondition). With the carrier of §4, all 24 follow from the ghost update and need no template theorem. They are listed per row above.

Totals over the 41 calls:
- 4 need no store theorem (rows 1, 3, 4, and the trade sink's shape).
- 15 are field reads/writes, which need instance lemmas only, plus one composition lemma for writes.
- 10 are partial (a template theorem exists for a narrower configuration: root list, u32 key, Inlary pool, success branch only).
- 12 are MISSING outright:
  - pool free ×2;
  - pool failure ×2;
  - hash remove;
  - the 8 tree calls (collapsed into rows 34–41 above).

---

## 2. AMCC state, verified from source

Global:
- `grep -rn sorry Amcc` returns 0 hits.
- The only `axiom` text is a string literal emitted into exported Lean (`Codegen/ExportLean.lean:39`), not an axiom of the development.
- `#print axioms` on `mini_insert_forward_sim`, `mini_insert_forward_sim3`, `Thash.insert_success` and `Thash.genWellFormed` gives `[propext, Classical.choice, Quot.sound]`.
- `lake-manifest.json` has no packages (no Batteries, no Mathlib).

### CSubset (the semantics)

- **Typed at field level, not bytes** (`CSubset/Value.lean:9`).
  - `Path = root (.glob id | .blk n) + steps (.fld | .idx)` (`:38-67`). `Path.overlaps` is a prefix test (`:74`).
  - `Value = u8 | u32 | u64 | bool | null | ptr Path | strct | arr` (`:121`).
  - `Store{glb, loc, hp, next}` (`:460`), `Mem{glb, hp, next}` (`:610`).
- Errors: `oob | typeErr | unbound | depth | nullDeref | useAfterFree` (`Eval.lean:41`).
- Fuel is call depth only: `execStmt p d`, and `callFun` uses `p.funs.length` (`Eval.lean:365/383`). Loops are `forN` with a bound evaluated once.
- **`Stmt` = `skip | assign | seq | cond | forN | call | ret`** (`Syntax.lean:336`).
  - There is **no `Stmt.alloc` / `Stmt.free`**.
  - `Store.allocBlock` / `freeBlock` (`Value.lean:590/595`) are never called.
  - Every emitted pool is therefore an inline array on a global.
- `SmallStep.lean`: `step_det` (`:158`), `execStmt_sound` (`:352`), `exec_iff_steps` (`:370`). This is soundness plus determinism; there is no completeness direction.

What field-level typing costs the decoder:
- Nothing for layout. Decoders read typed `Value`s by `Path`, so no byte encoding, alignment or aliasing through casts arises.
- The price is at the printer: CSubset structs → C structs is a trust item (§8).

### Pool (`Templates/Pool.lean`, 465 lines)

- **Storage:** over `Inlary`, with fixed capacity. Rows are `⟨.glob g_D, [.fld f, .idx i]⟩`.
- **Emitted functions:** Init / Alloc / Free / N / Max (`initDef :88`, `allocDef :101`, `freeDef :115`, `sizeDef :126`, `maxDef :133`, `genPool :419`).
- **Invariants:** `PoolInv` (`:142-156`) has 11 clauses and no completeness clause. `RowFresh` (`:159`) is never established.
- **Theorems:**
  - `alloc_correct` (`:244`): the free list is `q :: free_rest`.
  - `size_correct` (`:211`) and `max_correct` (`:225`).
  - None for Free, Init, the failure branch, or `NULL ↔ full`.
  - No `genPool` resolution theorem and no Pool `genWellFormed`.
- **Other pool files:**
  - `Tpool.lean` (149 lines): no theorems, fails `Wf.check` with 10 errors, never allocates.
  - `Lary.lean` (187 lines): bump allocation, no free, no theorems.
- **The abstract model is disconnected.** `Spec/Pool.lean` (531 lines) proves a free-list model with Nat handles (`objStore_laws :351`, `reserve_sound :392`, `grow_frame :370`, `liveRecs_alloc :453`). No `Templates/` or `CSubset/` file imports `Amcc.Spec`.
- **Handles:** a row handle is a `Path` into a global array, i.e. effectively the row index `i`. Use-after-free is not observable on glob-rooted rows. Slot reuse holds by construction, with no theorem.

### Llist (`Templates/Llist.lean` 3156, `LlistWf.lean` 941, `CSubset/Chain.lean` 730)

- **Emitted functions:** 10, including `Insert` (head) and `InsertTail`.
- **Decoder:** `elems` (`:537`).
- **Invariant:** `TailListInv` (`:798`, 10 clauses).
- **Theorems:**
  - `insertTail_correct` (`:2879`): `TailListInv m nm rows qs` and a row with `inlist = false` give `TailListInv m' … (qs ++ [q]) ∧ elems m' … = some (qs ++ [q])`.
  - `remove_correct` (`:2905`): the same shape with `qs.erase q`. Tail preserved via `RemoveUnlinks` (`:1172`, proved at `:2460`).
  - FIFO stepping: `llist_fifo_first` (`:2927`), `llist_fifo` (`:2943`), `llist_fifo_step` (`:2976`).
  - Readers: `first_correct` (`:863`), `size_correct` (`:878`), `next_correct` (`:949`).
  - `init_correct` (`:988`) does not reset the tail and establishes no invariant.
- **Schema-generic** through `laws_apply` (`LlistWf.lean:888`) and `genWellFormed` (`:810`).
- **One list per program.** Head, tail and count live on the root global `g_D`, and `genLlist` takes the first `Llist` field of the root. **A list per parent row (amc's `zdl_` on a parent ctype) is not supported.**

### Thash (`Templates/Thash.lean`, `ThashFind.lean`, `ThashRefine.lean`, `ThashWf.lean`)

- **Emitted functions:** Init / Find / InsertMaybe / Remove / N (`initDef :124`, `findDef :162`, `insertDef :196`, `removeDef :235`, `sizeDef :263`).
- **Hash:** `key & (NB-1)`, with NB a power of two. No rehash.
- **Chains:** intrusive, through `f_next` and `f_inhash`.
- **Key:** the element's `Pkey` field, which must be `u32` (`:348`).
- **Decoder:** `elems m key chains : List (UInt32 × Path)` (`ThashRefine.lean:71`).
- **Invariant:** `RepInv` (`:37-67`) holds over an arbitrary `rows : List Path`.
- **Theorems:** `findCorrect` (`ThashFind.lean:418`), `find_hit`/`find_miss` (`:439/457`), `find_hit_unique`/`find_miss_unique`, `insert_success`, `insert_duplicate_reject`, `insert_inlist_reject`, `insert_noop`/`remove_noop` (`Thash.lean:423/450`).
- **Generic** over every accepted schema: `genWellFormed` (`ThashWf.lean:799`) and `laws_apply` (`:910`), which gives `cap = nb`.
- **No `Remove` refinement and no `Init` theorem.**
- The "Still owed" docstring at `Thash.lean:479-508` is stale: `Find` is proved.

### Upptr (`Templates/Upptr.lean` 483, `UpptrWf.lean` 279)

- **Emitted functions:** Init / Get / Set / Test.
- **Coverage:** `genUpptr` is total and covers every Upptr field of every ctype, with no root needed.
- **Theorems:** `get_correct` (`:272`), `init_correct` (`:298`), `get_set` (`:333`, with frame), `test_null` / `test_ptr` (`:374/395`), `genWellFormed` (`UpptrWf.lean:189`).
- **Laws:** operational read/write/frame laws only. No `RepInv`, no decoder.
- Not used in MiniDb.

### Forward simulation (`Templates/MiniDb.lean`, 3159 lines)

- **Generator:** `genC (d : Dmmeta.Db)` (`:51`) builds Pool + Llist + optional Thash + `<Db>_Insert`. The insert body hard-codes the fields `id`/`qty` and their types.
- **Schemas proved:** only `miniDb cap` (`:27`) and `miniDb3 cap nb` (`:1488`), via `genC_miniDb … := rfl` (`:199/1501`).
- **Version 1:**
  - `DbRepInv` (`:213`) composes `Pool.PoolInv`, `Llist.TailListInv`, freshness, payload and disjointness.
  - `absDb` (`:225`) decodes the queue and maps `readOrder`.
  - `mini_insert_forward_sim` (`:542`): `DbRepInv m cap free_rest live_qs queue_es → free_rest ≠ [] → fuel ≥ … → ∃ m' …, execStmt (genMiniDb cap) fuel (insertStmt v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal) ∧ DbRepInv m' … ∧ absDb m' fuel = some ((absDb m fuel).getD [] ++ [v])`.
- **Version 2:**
  - `DbRepInv3` (`:1509`) adds `Thash.RepInv` over `Pool.poolRows`, six disjointness facts, and `hash_queue_match : q ∈ chains.flatten ↔ q ∈ queue_es`.
  - `absDb3` (`:1533`) decodes the queue only.
  - `mini_insert_forward_sim3` (`:1611`) adds hypotheses for key freshness (`h_fresh`) and bucket room (`hfits`).
- **Coverage:** insert only (the allocation success branch). No free, no remove, no failure branch.
- **The pattern the instance needs:** one composed invariant; each generated call proved to preserve it and to perform the abstract operation.

### Trees

- **`Spec/Rbtree.lean`** (139 lines) is a pure model, with no insert, delete or lookup.
  - Theorems: `empty_is_rbtree`, `rotate_{left,right}_equiv` (in-order preserved), `rotate_left_preserves_bst`, `min_size_black_height`.
  - The module docstring's "O(log N)" is not proved.
- **The templates are stubs:**
  - `Templates/Rbtree.lean` (260 lines, not wired into `Main.lean`).
  - `Templates/Atree.lean` (224 lines): plain BST layout, with no AVL balance field.
  - `Templates/Bheap.lean` (182 lines).
  - Their bodies are placeholders: `Find`/`First`/`Last` return `root`, and the rotations are no-ops.
  - Their only checks are `Dmmeta.check` and `Wf.check`.

### Handles vs the contract

- **Contract:** `OrderH = LevelH = Nat` (`EngineDbApi.lean:54-55`), with validity through `oLive`/`lLive`.
- **Generated code:** a handle is a `Path`, and a pool row is `g_D.pool[i]`, so the handle map is `h ↦ i` (Inlary) or `h ↦` the h-th reserved row (heap pool).
- **Mismatch 1 — list order.** The contract's `view` equalities fix list order: `orderAlloc.post` prepends to `oLive`, `hashInsert.post` prepends to `hash`, `tInsert.post` prepends to `tree t`. Chain order in a Thash, or in-order in a tree, is not the contract's list order. §4 resolves this with ghost state.
- **Mismatch 2 — field widths.** `OrderRow.side`/`stpMode` are `UInt8` (`EngineDbApi.lean:61-62`), while the C fields are `uint64_t`. The decoder truncates. Writes always come from `UInt8`, so the invariant "C field = zero-extended ghost byte" holds. This is not a ⚑.

---

## 3. The schema

This is a draft in AMCC's ssim dialect. The heads AMCC reads are `dmmeta.ctype`, `dmmeta.field`, `dmmeta.inlary`, `dmmeta.smallstr` and `amcc.root` (`Ssim/Schema.lean:17-26`). The fields are exactly what `engine_db.h` reads and writes, widened to `u64`.

```
dmmeta.ctype  ctype:order  comment:""
dmmeta.ctype  ctype:level  comment:""
dmmeta.ctype  ctype:EngineDb  comment:""
dmmeta.field  field:order.id          arg:u64    reftype:Pkey    comment:""
dmmeta.field  field:order.account_id  arg:u64    reftype:Val     comment:""
dmmeta.field  field:order.side        arg:u64    reftype:Val     comment:""
dmmeta.field  field:order.stp_mode    arg:u64    reftype:Val     comment:""
dmmeta.field  field:order.price       arg:u64    reftype:Val     comment:""
dmmeta.field  field:order.qty         arg:u64    reftype:Val     comment:""
dmmeta.field  field:order.remaining   arg:u64    reftype:Val     comment:""
dmmeta.field  field:order.p_level     arg:level  reftype:Upptr   comment:""
dmmeta.field  field:level.price       arg:u64    reftype:Pkey    comment:""
dmmeta.field  field:level.zdl_orders  arg:order  reftype:Llist   comment:"per-level FIFO"
dmmeta.field  field:EngineDb.order    arg:order  reftype:Tpool   comment:""
dmmeta.field  field:EngineDb.level    arg:level  reftype:Tpool   comment:""
dmmeta.field  field:EngineDb.ind_order arg:order reftype:Thash   comment:"key order.id"
dmmeta.field  field:EngineDb.bids     arg:level  reftype:Atree   comment:"key level.price"
dmmeta.field  field:EngineDb.asks     arg:level  reftype:Atree   comment:"key level.price"
dmmeta.inlary field:EngineDb.ind_order min:0 max:NB comment:""
amcc.root     ctype:EngineDb  comment:""
```

`total_qty` is dropped. It is not in the contract, and the adapter maintains it only for itself (`engine_db_adapter.c:12-15, :97`).

What the front end does with this schema today:

| Item | Parser / `Dmmeta.check` | Generator |
|---|---|---|
| all reftypes above | accepted (`supported := Reftype.all`, `Schema.lean:74`) | — |
| two pools on the root | accepted | **ignored**: every generator uses `fields.find?`, which takes the first field per reftype |
| `Tpool` | accepted | emits ill-typed code (10 `Wf.check` errors), never allocates |
| `Inlary` pool instead | accepted | works (Pool), but see ⚑1 |
| per-parent `Llist` on `level` | accepted | **not generated**: the head is on the root global (`Llist.lean:127`) |
| `Thash` keyed by `u64` | accepted | **rejected** (`Thash.lean:348`) |
| `Upptr` | accepted | generated, but as a separate program (`genUpptr`) |
| two `Atree`s | accepted | stub bodies, first field only |
| a composed program for the whole schema | — | only `MiniDb.genC` (Pool + Llist + Thash, hard-coded `id`/`qty`) |

The existing `c/schema/matching_engine.ssim` is an out-of-date sketch: `side:u8`, no `account_id`/`stp_mode`, no level pool, `Inlary max:1000000`. D1 replaces it.

---

## 4. `view`

**Carrier.**
```
structure GenStore (cap) where
  m     : Mem          -- CSubset memory of the generated data layer
  g     : Db           -- ghost: the contract's abstract view
  rep   : Rep cap m g  -- composed representation invariant
view s := s.g
```

- **Why ghost state is needed.** The contract states its laws as equalities on the exact `Db` record, for example `orderAlloc.post : db' = {db with …, oLive := h :: db.oLive}`. List orders (`oLive`, `hash`, `tree t`) are allocation- or insertion-history orders that memory does not record.
  - Decoding memory alone would give chain order or in-order instead.
  - The ghost carries history. `Rep` fixes everything memory does determine:
    - the rows' field values;
    - queue order, which is the Llist decoder's order and does equal the contract's;
    - set membership of the hash and the trees;
    - key uniqueness;
    - counts;
    - owner pointers.
- **Why a subtype.** Laws are stated under `(view s).WF` only, not under a representation invariant. A bare `Mem` carrier would have to satisfy them for unreachable memories. The subtype makes `Rep` part of `s`.
- **`Rep`** is the composition, as in `DbRepInv3`:
  - two pool invariants;
  - a per-level `TailListInv` for every live level;
  - `Thash.RepInv` over the order rows;
  - two tree invariants;
  - an Upptr clause: `p_level = l ↔ h ∈ g.queue l`;
  - field decoding: `readMem (fld row_h "price") = .u64 (g.orders h).price` and so on;
  - the handle map (§2);
  - pairwise disjointness of the global fields;
  - key matching: hash membership ↔ `g.hash`, tree membership ↔ `g.tree t`.
- **Operations** are CSubset runs of the generated functions, guarded: `op s args := if pre g args then (run C; package with the new ghost and the proof of Rep) else s`.
  - The guard is `noncomputable` and classical.
  - Every law is stated under its `pre`, and `runExt` (`Matcher/Lang.lean:358-435`) checks `pre` before every store call, trapping otherwise. Both matcher proofs show no trap, so the fallback branch is never taken on any run the theorem covers. Each law needs a proof that, under `pre`, the C run returns `.ok` and re-establishes `Rep` with the updated ghost. That proof is exactly a forward-simulation step.
  - Reads (`readOrder`, `readLevel`, `levelCount`, `owner`, `hashFind`, `qFirst`, `qNext`, `tFind`, `tBest`) run the generated reader and return its decoded result. The law is then "reader result = ghost answer", from `Rep`.

**Which laws follow how:**

| Laws | Source | Kind |
|---|---|---|
| `init_*` | init run + reservation (§5) | new (pool init theorems) |
| 24 `count_*` / `levelsUsed_*` frames | ghost update | direct (no template theorem) |
| `readOrder`, `readLevel` | `Rep` field clause | direct |
| `writeOrder`, `writeLevel` | CSubset write frame + `Rep` preservation | composition lemma: a payload write preserves the Llist/Thash/tree invariants; a key write is outside the index by `pre` |
| `levelCount`, `qFirst`, `qNext`, `qInsertTail`, `qRemove` | Llist theorems | direct **after** the per-parent generalisation (new template work) |
| `owner` | Upptr `get_set` + Llist | composition lemma (the Upptr clause) |
| `hashFind`, `hashInsert` | Thash theorems | direct after u64 keys (new template work); `hfits` discharged by `cap = nb` ≥ live count |
| `hashRemove` | — | new template theorem (Thash `Remove`) |
| `orderAlloc`, `levelAlloc` (incl. failure iff) | pool theorems + capacity guard | new (failure branch, completeness clause, heap pool) |
| `orderFree`, `levelFree` | — | new (pool `Free`) |
| `tFind`, `tInsert`, `tRemove`, `tBest` | — | new (tree template, §6) |

**Every mutating law needs a composition lemma**, as `mini_insert_forward_sim3` needed six disjointness facts. The cost is linear in the number of structures: each template's theorem comes with a frame ("memory outside my paths is unchanged"), and `Rep`'s other clauses are read only on disjoint paths.

---

## 5. Initialisation

- **What the C does now.** `ME_adapter_init(capacity)` reserves `capacity` rows per pool, or aborts, and callocs the trade buffer (`engine_db_adapter.c:38`).
- **What the contract needs.** `init : S` is a value, with `view init = Db.empty`, `count init = 0` and `levelsUsed init = 0`, plus `none ↔ capacity ≤ count` from then on.
  - So after init, allocation must fail exactly at the capacity bound and never because memory ran out.
  - That requires `capacity` rows per pool to be reserved at init, followed by a guard `count ≥ capacity → NULL` in the alloc wrapper.
- **Where "initial allocation succeeds" enters.** The instance is built from a successful init run: `GenStore.init := ⟨m₀, Db.empty, rep₀⟩`, where `m₀` comes from `callFun p mEmpty init = .ok (m₀, _)` under an allocator oracle. The instance, and hence `engine_run_refines`, takes that success as a hypothesis. It is the single trusted step, and the slogan's "if the initial allocation succeeds" is literally this hypothesis.
- **The allocation route depends on ⚑1:**
  - **Heap route:**
    - `Stmt.alloc`/`Stmt.free` in CSubset, with an allocator oracle (malloc postulated at the leaf, as `GOALS.md` says);
    - a heap pool (amc `Tpool`/`Lpool`) with `Reserve`;
    - init = one `malloc` per pool for `capacity` rows (one block each, or one arena).
    - "Initial allocation succeeds" = those oracle calls return non-null.
    - After init, `Alloc` below capacity takes from the free list and never calls the oracle. That is a client lemma, from reserve + free-list length.
  - **Inline route (Inlary):** there is no allocation at all, and the rows are a static global of size `capacity`. The hypothesis becomes "the static image loads". It is smaller, but `GOALS.md` names exactly this ("emit a pool over a static arena rather than do the heap work") as a broken rule.
- **`Llist.init_correct` and Thash `Init`.** The first does not reset the tail and establishes no invariant; the second has no theorem. With a per-parent Llist, the list header is initialised when a level row is allocated (amc's row init), so an `Llist.InitParent` theorem is needed as part of `levelAlloc`.

---

## 6. The tree

The contract's tree is a `List LevelH` per side with unique prices, prepend order on insert, and `better`-extremal `tBest`. Whatever the template, the abstract side is that list, carried as ghost (§4). The template's invariant only has to give set equality with the ghost, plus sortedness for `Find`/`First`/`Last`.

| Option | Template work (AMCC) | Touches | Risk |
|---|---|---|---|
| **(a) `Atree`, AVL** (amc's Atree is AVL) | Real bodies for Find / First / Last / Insert / Remove / rebalance. Invariant: BST ordering over an intrusive parent/left/right/height layout, and in-order = sorted set. Theorems: Find, First/Last, Insert (descent + link + rotations preserve in-order), Remove (unlink with successor swap + rotations). Balance fields are maintained but not proved. The rotation-preserves-in-order fact exists only functionally (`Spec/Rbtree.lean:92-102`) and must be redone over `Path` memory. | AMCC only; no contract change | high: Remove is the bulk, as the prompt says |
| **(b) red-black** | Same proof shape; recolouring instead of heights. Batteries' functional `RBMap` could be the abstract side, but AMCC has no dependencies and adding Batteries is a route change. The abstract side here is a list anyway, so it buys little. The imperative version is the proof burden either way. `Rbtree` is not wired into `Main.lean`. | AMCC; new dependency | high; no advantage over (a) |
| **(c) price ladder + bitmaps** | Small (arrays, no rotations). Not an amc reftype, so it would be client code, not AMCC. | the contract (`tInsert` gains failure), `processB` (range check), both matcher proofs at their entry lemmas | low proof cost, high blast radius; changes the spec (Ara's decision) |

**Recommendation: (a).**
- It is amc's reftype, so the work counts toward AMCC's completeness goal rather than being client-only.
- It changes no spec.
- Balance is excluded, per the Not-goals.
- Estimate: 4–7k lines of Lean in AMCC (Llist's refinement of one list was about 4.1k lines with `LlistWf`), of which Remove is about half.
- It also replaces the unbalanced BST (STATUS-v2 finding) with a balanced one at no extra proof cost, since balance is maintained by the code and not proved.

---

## 7. Cost and order

These are rough line estimates, calibrated against the existing files: Llist + LlistWf ≈ 4.1k; Thash refinement ≈ 1.5k beyond `Find`; `MiniDb` composition ≈ 3.2k for two to three structures and one operation.

| Structure | AMCC template work | Unified instance work | Risk |
|---|---|---|---|
| Generator | multiple fields per reftype on the root; a composed `genDb` for any accepted schema, with `Wf` and `laws_apply`; per-parent Llist emission; u64 Thash emission; real Atree emission (1–2k) | schema file | medium |
| Pools / fields | **heap route:** `Stmt.alloc`/`free` + allocator oracle in CSubset (syntax, eval, small-step, `Wf`, printer; every exhaustive `Stmt` proof reopens) 1.5–3k; heap pool (Tpool) with Reserve/Alloc/Free, failure and completeness 2–3k. **Inline route:** Pool Free, Init, failure, completeness 0.8–1.2k | carrier, `Rep`, handle map, field lemmas, alloc/free/read/write laws, 24 frames (1.5–2.5k) | high (heap) / low (inline) |
| Queue | per-parent Llist: head/tail/n in the parent row, the parent as an argument, a generalisation of existing proofs, plus `InitParent` (1.5–2.5k) | queue laws, owner via Upptr (0.8–1.2k) | medium |
| Hash | u64 key (hash of u64 to bucket; `mask_eq_mod` for u64); `Remove` unlink theorem; `Init` (1.5–2k) | hash laws (0.4–0.8k) | medium |
| Tree | Atree AVL, §6 (4–7k) | tree laws ×2 sides (0.6–1k) | high |
| Init / closing | pool reserve / init theorems (in the pool rows above) | `init_*`, allocation hypothesis, instance, `engine_run_refines` (0.5–1k) | low |

Total: about 15–25k lines, most of it in AMCC, and most of that is work `GOALS.md` requires anyway (per-parent Llist, Tpool, Atree, heap allocation, multiple fields).

**Proposed phase order.** This deviates from PLAN-D §4: D1 as written ("generate and measure") is impossible before generator work, so generation moves first.

1. **D1 — Generator, no theorems (AMCC + unified).**
   - Build: multiple fields, composed `genDb`, per-parent Llist, u64 Thash, Atree with real bodies, and the pool route chosen at ⚑1. The heap route needs `Stmt.alloc` syntax and printer here, and its semantics in D2.
   - Generate `c/gen/` and the adapter.
   - Evidence: `tests/contract/run.sh`, `tests/differential/run.sh`, `make test-gen`, `tests/run_all.sh`. Benchmark handwritten vs generated on random and monotone streams into `BENCH-D.md`.
   - `PLAN.md` and `GOALS.md` are updated in this commit (route change: Atree/Tpool/alloc move from deferred to now).
2. **D2 — Pools and fields.**
   - AMCC: the pool theorems (plus CSubset heap semantics on the heap route).
   - Unified: `EngineDbGen.lean` with the carrier, `Rep`, pool/field laws and frames; undischarged laws kept in a `Pending` structure.
   - Evidence: the contract suite.
3. **D3 — Queue.** Per-parent Llist theorems, then the queue and owner laws. Evidence: the contract suite.
4. **D4 — Hash.** u64 and Remove theorems, then the hash laws. Evidence: the contract suite.
5. **D5 — Tree.** Atree theorems, then the tree laws. Evidence: the contract and differential suites.
6. **D6 — Init.** Reserve, `init_*`, the allocation hypothesis. Evidence: all suites.
7. **D7 — Closing.** As PLAN-D §4. Evidence: all Phase 5 suites, `#print axioms`, `EVIDENCE-D.md`.

---

## 8. Linking

**Lean level (a theorem).**
- The instance `EngineDb (GenStore cap)` defines each operation as CSubset's `callFun` of a generated function on `s.m`.
- `matcher_run_refines (S := GenStore cap)` then composes the matcher language's semantics (`Matcher/Lang.lean`, via `runExt`) with CSubset's semantics of the generated data layer.
- Nothing C-level is assumed at this level beyond CSubset's definitions.

**C level (trust, covered by tests).**
- Two printed fragments meet through `engine_db.h`: the matcher printed from the matcher language, and the data layer printed from CSubset.
- Trusted:
  - both printers;
  - the C calling convention and struct layout at that header;
  - gcc/clang;
  - single-threaded use;
  - the initial allocation (§5).
- Covered empirically by the linked differential test (`tests/differential/run.sh`) and the contract suite.

Items that do not fit the picture as stated:
- **⚑ `writeOrder` is whole-row; the C setters are per-field.**
  - `runExt`'s `.setO f` reads the row, updates one field and calls `writeOrder` (`Lang.lean:373-381`).
  - The printed matcher calls `ME_order_set_<f>`, a single setter.
  - If the instance's `writeOrder` runs all seven generated setters, the Lean program and the linked C differ in six redundant writes. Semantically they are equal, but the difference would live in the matcher printer's trust.
  - Proposal: an instance lemma `writeOrder s h ((readOrder s h).get with f := v) = run (set_f h v) s`. This proves at the Lean level that the one-setter C path is the path the theorem covers, keeping the printer's mapping `setO f ↦ ME_order_set_f` a pure name translation.
- **Adapter `total_qty`.** `ME_order_set_remaining` adjusts a level total that is not in the contract. The generated store drops it, so the adapter shrinks to pure forwarding. Finding, not ⚑.
- **Trade sink.** `ME_trade_reset`/`ME_trade_emit` are matcher output, not store operations. They stay in the matcher printer's trust exactly as today.
- **Adapter provenance.** If AMCC cannot emit the adapter (the thin `ME_*` forwarding layer), it stays handwritten in `c/gen/` and becomes a trust item. It is about 40 lines of forwarding once `total_qty` is gone. The preference is to emit it from the client schema as CSubset, so that its functions are the ones the instance runs.

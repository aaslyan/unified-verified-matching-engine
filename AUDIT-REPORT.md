## Summary

FAIL count: 19   PASS count: 12   CANNOT VERIFY: 5

Blocking issues (would sink peer review):

- The C-refinement bridge claimed in `paper_c_engine/paper.tex` is not present as stated: the capstone theorem does not execute `execStmt (genC S)`, does not mention a program, fuel, `.ok`, output memory, or `WfMem` on both sides.
- The paper claims FIFO, STP, and unique-ID invariant coverage for the C bridge, but the C-side decoded `Order` has no timestamp, the STP predicate is policy-blind, and unique IDs are assumed through a contract rather than established from memory traversal.
- The paper claims allocation-free generated C, but `c/src/matching_engine_gen.c` performs `calloc`, `realloc`, and `free`.
- The paper claims balanced-tree or logarithmic behavior in places that cannot be supported by the emitted unbalanced BST.
- Benchmark headline numbers cannot be derived from the per-class table as printed, and rerunning the benchmark produced materially different latency/throughput from the paper.
- Several paper statements describe theorem strength, generated-code safety, and operational C semantics that I could not support from source, build output, or measurements.

## Part A — Build and axioms

### A1 Clean build

Status: CANNOT VERIFY

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rm -rf lean/.lake/build && cd lean && lake build 2>&1 | tail -40
```

Output:

```text
exec_command failed: CreateProcess { message: "Rejected(\"`/bin/bash -lc 'rm -rf lean/.lake/build && cd lean && lake build 2>&1 | tail -40'` rejected: rm -f style commands are not permitted. Use a safer approach\")" }
```

Finding: The requested destructive clean command was rejected by the execution environment, so I cannot certify a non-incremental build from that exact command.

Fallback command:

```bash
cd /home/aaslyan/unified-verified-matching-engine/lean && lake build 2>&1 | tail -40
```

Output:

```text
⚠ [58/76] Replayed MatchingEngine.Theorems
warning: lean/MatchingEngine/Theorems.lean:2713:8: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [59/76] Replayed Bridge.MatchingEngineBridge
warning: lean/Bridge/MatchingEngineBridge.lean:81:36: This simp argument is unused:
  match_upd

Hint: Omit it from the simp argument list.
  simp [Uncrossed, insertBidPreservesAskFloor, h_old, match_upd]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: lean/Bridge/MatchingEngineBridge.lean:81:25: This simp argument is unused:
  h_old

Hint: Omit it from the simp argument list.
  simp [Uncrossed, insertBidPreservesAskFloor, h_old, match_upd]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [66/76] Replayed MatchingEngine.TheoremsFull
warning: lean/MatchingEngine/TheoremsFull.lean:1358:8: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: lean/MatchingEngine/TheoremsFull.lean:1422:8: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [72/76] Built Bridge.RelationalMemory
✔ [73/76] Built Bridge.EndToEndTheorem
✔ [74/76] Built UnifiedVerifiedMatchingEngine
Build completed successfully (76 jobs).
```

Finding: Incremental build succeeds, but this does not satisfy the requested clean-build check.

### A2 Default targets include proof libraries

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine/lean && cat lakefile.toml
```

Output:

```toml
name = "unified_verified_matching_engine"
version = "0.1.0"
defaultTargets = ["UnifiedVerifiedMatchingEngine"]

[[lean_lib]]
name = "Amcc"
srcDir = "lean"

[[lean_lib]]
name = "MatchingEngine"
srcDir = "lean"

[[lean_lib]]
name = "Bridge"
srcDir = "lean"

[[lean_lib]]
name = "UnifiedVerifiedMatchingEngine"
srcDir = "lean"
```

Finding: The default target is a Lean library, not merely an executable target.

### A3 Every Lean file reached by build

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine/lean
find .lake/build/lib/lean -name '*.olean' | sed 's#^.lake/build/lib/lean/#lean/#;s#.olean$#.lean#' | sort > /tmp/audit-built2.txt
find lean -name '*.lean' | sort > /tmp/audit-src2.txt
comm -23 /tmp/audit-src2.txt /tmp/audit-built2.txt
```

Output:

```text
```

Finding: No unbuilt `.lean` source file was found by this `.olean` comparison.

### A4 Forbidden constructs

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
grep -rn '\bsorry\b\|\badmit\b\|native_decide\|^\s*axiom\b\|@\[implemented_by\]' --include=*.lean lean/
```

Output:

```text
```

Finding: No `sorry`, `admit`, `native_decide`, top-level `axiom`, or `@[implemented_by]` occurrence was found in Lean source.

### A5 Axiom footprints regenerated

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine/lean
lake env lean lean/AuditScratch.lean
```

Output:

```text
'VerifiedCMatchingEngine.c_first_spec' depends on axioms: [propext, Quot.sound]
'VerifiedCMatchingEngine.c_first_spec_decodes' depends on axioms: [propext, Quot.sound]
'VerifiedCMatchingEngine.c_next_spec' depends on axioms: [propext, Quot.sound]
'VerifiedCMatchingEngine.c_next_spec_decodes' depends on axioms: [propext, Quot.sound]
'VerifiedCMatchingEngine.EngineDb_bids_First_spec' does not depend on any axioms
'VerifiedCMatchingEngine.EngineDb_asks_First_spec' does not depend on any axioms
'VerifiedCMatchingEngine.amcc_memory_contract_implies_matcher_invariants' does not depend on any axioms
'VerifiedCMatchingEngine.wf_mem_implies_AllInv' does not depend on any axioms
'VerifiedCMatchingEngine.top_of_book_match_sound' depends on axioms: [propext, Quot.sound]
'VerifiedCMatchingEngine.matching_engine_execution_sound' depends on axioms: [propext, Quot.sound]
'VerifiedCMatchingEngine.c_matching_engine_end_to_end_sound' depends on axioms: [propext, Quot.sound]
'process_preserves_BookInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'process_PostOnlyGuarantee' depends on axioms: [propext, Quot.sound]
'process_STPGuarantee' depends on axioms: [propext, Quot.sound]
Except.ok ({ glb := [], loc := [], hp := [], next := 0 }, CSubset.Outcome.normal)
```

Finding: `paper_c_engine/paper.tex:99` claims "zero custom axioms". That is only defensible if it means no project-defined axioms. It is false if read literally as "zero axioms", because the cited theorems depend on `[propext, Quot.sound]`, and full-domain `process_preserves_BookInvariant` also depends on `Classical.choice`. The paper should state the regenerated footprints precisely.

## Part B — Paper-to-source correspondence

### B1 Top-level C bridge theorem statement

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba lean/Bridge/EndToEndTheorem.lean | sed -n '35,58p'
```

Output:

```text
    35	theorem c_matching_engine_end_to_end_sound
    36	    (m : Mem) (bidsRoot asksRoot : Option Ptr) (req : COrder)
    37	    (h_wf_req : req.qty > 0)
    38	    (h_wf_mem : WfMem m bidsRoot asksRoot)
    39	    (h_noncross_buy :
    40	      ∀ passive,
    41	        Uncrossed (abstract_match_step (alpha_concrete m bidsRoot asksRoot) req.toOrder passive STPAction.cancel_new))
    42	    (h_noncross_sell :
    43	      Uncrossed (abstract_insert (alpha_concrete m bidsRoot asksRoot) req.toOrder)) :
    44	    let book := alpha_concrete m bidsRoot asksRoot
    45	    AllInv book ∧
    46	    Uncrossed (abstract_insert book req.toOrder) ∧
    47	    (∀ passive,
    48	      Uncrossed (abstract_match_step book req.toOrder passive req.stp_mode)) ∧
    49	    Uncrossed (abstract_cancel book req.id) := by
    50	  intro book
    51	  constructor
    52	  · exact wf_mem_implies_AllInv m bidsRoot asksRoot h_wf_mem
    53	  constructor
    54	  · exact matching_engine_execution_sound book req h_wf_req h_noncross_buy h_noncross_sell |>.1
    55	  constructor
    56	  · intro passive
    57	    exact match_execution_preserves_uncrossed book req passive
    58	  · exact ioc_cancel_preserves_uncrossed book req.id
```

Finding: `paper_c_engine/paper.tex:143-163` displays a refinement diagram with `execStmt(P, fuel, order_stmt, m) = ok m'` and alpha correspondence. The theorem above has no `Program`, no `fuel`, no `execStmt`, no `.ok`, no output memory `m'`, and no post-state `WfMem`.

### B2 Manual unfolding chain for C execution claim

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "c_matching_engine_end_to_end_sound|matching_engine_execution_sound|abstract_insert|abstract_match_step|execStmt|genC" lean/Bridge lean/Amcc.lean
```

Output:

```text
lean/Bridge/EndToEndTheorem.lean:35:theorem c_matching_engine_end_to_end_sound
lean/Bridge/EndToEndTheorem.lean:54:  · exact matching_engine_execution_sound book req h_wf_req h_noncross_buy h_noncross_sell |>.1
lean/Bridge/EndToEndTheorem.lean:57:    exact match_execution_preserves_uncrossed book req passive
lean/Bridge/MatchingEngineBridge.lean:135:def abstract_insert (book : CBookState) (order : Order) : CBookState :=
lean/Bridge/MatchingEngineBridge.lean:178:def abstract_match_step (book : CBookState) (aggressive passive : Order) (stp : STPAction) : CBookState :=
lean/Bridge/MatchingEngineBridge.lean:268:theorem matching_engine_execution_sound
lean/Amcc.lean:456:def execStmt (fuel : Nat) (s : Stmt) (σ : Mem) : ExecM (Mem × Outcome) :=
```

Finding: The actual unfolding chain is:

`c_matching_engine_end_to_end_sound` -> `matching_engine_execution_sound` -> `limit_insert_preserves_uncrossed` / `match_execution_preserves_uncrossed` -> `abstract_insert` / `abstract_match_step`.

It bottoms out in hand-written Lean abstract functions over `CBookState`, not in execution of generated C by `execStmt` applied to `genC S`. I found no top-level `exec_c_order` bridge.

### B3 Forward-simulation theorem required elements

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba lean/Bridge/EndToEndTheorem.lean | sed -n '35,49p'
```

Output:

```text
    35	theorem c_matching_engine_end_to_end_sound
    36	    (m : Mem) (bidsRoot asksRoot : Option Ptr) (req : COrder)
    37	    (h_wf_req : req.qty > 0)
    38	    (h_wf_mem : WfMem m bidsRoot asksRoot)
    39	    (h_noncross_buy :
    40	      ∀ passive,
    41	        Uncrossed (abstract_match_step (alpha_concrete m bidsRoot asksRoot) req.toOrder passive STPAction.cancel_new))
    42	    (h_noncross_sell :
    43	      Uncrossed (abstract_insert (alpha_concrete m bidsRoot asksRoot) req.toOrder)) :
    44	    let book := alpha_concrete m bidsRoot asksRoot
    45	    AllInv book ∧
    46	    Uncrossed (abstract_insert book req.toOrder) ∧
    47	    (∀ passive,
    48	      Uncrossed (abstract_match_step book req.toOrder passive req.stp_mode)) ∧
    49	    Uncrossed (abstract_cancel book req.id) := by
```

Finding: Missing required forward-simulation elements: program, fuel, fuel sufficiency, `.ok` result, output memory, and `WfMem` on the post-state. Only pre-state `WfMem` appears.

### B4 `MatchingEngine.TheoremsFull`

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba lean/MatchingEngine/TheoremsFull.lean | sed -n '1360,1423p'
```

Output:

```text
  1360	theorem process_limit_preserves_BookInvariant (b : BookState) (o : Order)
  1361	    (hBI : BookInvariant b)
  1362	    (hLimit : o.kind = OrderKind.limit) :
  1363	    BookInvariant (process b o).1 := by
  1364	  exact process_preserves_BookInvariant_full b o hBI
  1365	
  1366	/-- Market orders preserve book invariants -/
  1367	theorem process_market_preserves_BookInvariant (b : BookState) (o : Order)
  1368	    (hBI : BookInvariant b)
  1369	    (hMarket : o.kind = OrderKind.market) :
  1370	    BookInvariant (process b o).1 := by
  1371	  exact process_preserves_BookInvariant_full b o hBI
  1372	
  1373	/-- Process function preserves all invariants -/
  1374	theorem process_preserves_AllInv (b : BookState) (o : Order)
  1375	    (hAll : AllInv b) :
  1376	    AllInv (process b o).1 := by
  1377	  exact process_preserves_AllInv_full b o hAll
  1378	
  1379	/-- Process respects Post-Only orders -/
  1380	theorem process_PostOnlyGuarantee (b : BookState) (o : Order) :
  1381	    PostOnlyGuarantee b o (process b o).1 := by
  1382	  exact process_postonly_guarantee b o
  1383	
  1384	/-- Process respects STP policies -/
  1385	theorem process_STPGuarantee (b : BookState) (o : Order) :
  1386	    STPGuarantee b o (process b o).1 (process b o).2 := by
  1387	  exact process_stp_guarantee b o
  1388	
  1389	end MatchingEngine
  1390	
  1391	-- Export key theorems at top level for paper references
  1392	export MatchingEngine (
  1393	  -- Core theorems
  1394	  process_preserves_BookInvariant_full
  1395	  process_preserves_AllInv_full
  1396	  process_limit_preserves_BookInvariant
  1397	  process_market_preserves_BookInvariant
  1398	  process_preserves_AllInv
  1399	  process_PostOnlyGuarantee
  1400	  process_STPGuarantee
  1401	  -- Soundness theorems
  1402	  process_preserves_total_volume
  1403	  process_timestamp_monotonic
  1404	  process_cancel_reduces_or_preserves
  1405	  process_no_duplicate_ids
  1406	)
  1407	
  1408	/-- Main theorem: processing preserves book invariant -/
  1409	theorem process_preserves_BookInvariant (b : BookState) (o : Order)
  1410	    (hBI : BookInvariant b) :
  1411	    BookInvariant (process b o).1 := by
  1412	  exact MatchingEngine.process_preserves_BookInvariant_full b o hBI
  1413	
  1414	/-- Main theorem: processing preserves all invariants -/
  1415	theorem process_preserves_AllInv_exported (b : BookState) (o : Order)
  1416	    (hAll : MatchingEngine.AllInv b) :
  1417	    MatchingEngine.AllInv (process b o).1 := by
  1418	  exact MatchingEngine.process_preserves_AllInv_full b o hAll
  1419	
  1420	/-- Convenience theorem for paper: all invariants preserved -/
  1421	theorem process_preserves_AllInv_paper (b : BookState) (o : Order)
  1422	    (hAll : MatchingEngine.AllInv b) :
  1423	    MatchingEngine.AllInv (process b o).1 := by
```

Finding: `MatchingEngine.TheoremsFull` exists and contains full-domain theorems about `process` over `BookState`, not the C bridge's `abstract_step` and not generated C execution.

## Part C — Vacuity hunting

### C1 Free variables in operational conclusions

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "callFun .*ok|= \.ok \(m, some|some v|some [a-zA-Z_][a-zA-Z0-9_']*\)" lean/Bridge lean/Amcc.lean
```

Output:

```text
```

Finding: I did not find the exact vacuous `callFun ... = .ok (m, some v)` shape in the current Lean bridge files.

### C2 FIFO in C bridge

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba lean/Bridge/MatchingEngineBridge.lean | sed -n '23,59p'
nl -ba lean/Bridge/RelationalMemory.lean | sed -n '27,37p'
```

Output:

```text
    23	structure Order where
    24	  id : Nat
    25	  account : Nat
    26	  price : Price
    27	  qty : Qty
    28	  side : Side
    29	  deriving DecidableEq, Repr
    30	
    31	structure PriceLevel where
    32	  price : Price
    33	  orders : List Order
    34	  deriving DecidableEq, Repr
    35	
    36	structure CBookState where
    37	  bids : List PriceLevel
    38	  asks : List PriceLevel
    39	  deriving DecidableEq, Repr
    40	
    41	def bestBid? (book : CBookState) : Option Price :=
    42	  book.bids.head?.map (·.price)
    43	
    44	def bestAsk? (book : CBookState) : Option Price :=
    45	  book.asks.head?.map (·.price)
    46	
    47	def Uncrossed (book : CBookState) : Prop :=
    48	  ∀ bid ask, bid ∈ book.bids → ask ∈ book.asks → bid.price < ask.price
    49	
    50	def SortedBids (book : CBookState) : Prop :=
    51	  book.bids.Pairwise (fun a b => a.price > b.price)
    52	
    53	def SortedAsks (book : CBookState) : Prop :=
    54	  book.asks.Pairwise (fun a b => a.price < b.price)
    55	
    56	def NoEmptyLevels (book : CBookState) : Prop :=
    57	  ∀ lvl, lvl ∈ book.bids ++ book.asks → lvl.orders ≠ []
    58	
    59	def NoGhostOrders (book : CBookState) : Prop :=
    27	def decodeOrder (m : Mem) (p : Ptr) : Option COrder := do
    28	  let row ← getRow? m p
    29	  some {
    30	    id := asNatD (row.f "id")
    31	    account_id := asNatD (row.f "account_id")
    32	    price := asNatD (row.f "price")
    33	    remaining_qty := asNatD (row.f "remaining_qty")
    34	    side := asSideD (row.f "side")
    35	  }
    36	
    37	partial def decodeOrdersFromPtrs (m : Mem) : List Ptr → Nat → List COrder
```

Finding: The C-bridge decoded order has no timestamp field. `paper_c_engine/paper.tex:99` says the C-side invariant suite includes FIFO. FIFO cannot be established as a state property from this decoded state.

### C3 STP safety clause distinguishes policies

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba lean/Bridge/MatchingEngineBridge.lean | sed -n '84,105p'
```

Output:

```text
    84	def SameAccountNoCross (o1 o2 : Order) : Prop :=
    85	  o1.account = o2.account → (o1.side = o2.side ∨ o1.price ≠ o2.price)
    86	
    87	def NoSelfTradesLevel (opposite : Side) (lvl : PriceLevel) (orders : List Order) : Prop :=
    88	  ∀ o1 o2, o1 ∈ lvl.orders → o2 ∈ orders →
    89	    o1.account = o2.account → o1.side = opposite → o2.side ≠ opposite → o1.price ≠ o2.price
    90	
    91	def NoSelfTrades (book : CBookState) : Prop :=
    92	  ∀ bid ask, bid ∈ book.bids → ask ∈ book.asks →
    93	    ∀ ob oa, ob ∈ bid.orders → oa ∈ ask.orders →
    94	      ob.account ≠ oa.account ∨ bid.price < ask.price
    95	
    96	structure AllInv (book : CBookState) : Prop where
    97	  uncrossed : Uncrossed book
    98	  sorted : SortedBids book ∧ SortedAsks book
    99	  no_empty : NoEmptyLevels book
   100	  no_ghosts : NoGhostOrders book
   101	  unique_ids : UniqueOrderIDs book
   102	  level_consistent : LevelOrderConsistency book
   103	  stp_sound : NoSelfTrades book
   104	
   105	-- Theorem: inserting a bid below best ask preserves uncrossed
```

Finding: `stp_sound` is `NoSelfTrades book` and has no STP policy parameter. I constructed a scratch theorem showing the same uncrossed same-account book satisfies the same predicate regardless of policy; there is no way for this clause to distinguish cancel-new, cancel-old, decrement, and cancel-both.

### C4 Unique order IDs theorem

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "UniqueOrderIDs|unique_order|no_duplicate" lean/Bridge lean/MatchingEngine
```

Output:

```text
lean/Bridge/MatchingEngineBridge.lean:71:def UniqueOrderIDs (book : CBookState) : Prop :=
lean/Bridge/MatchingEngineBridge.lean:101:  unique_ids : UniqueOrderIDs book
lean/Bridge/RelationalMemory.lean:184:  unique_order_ids : UniqueOrderIDs (alpha_concrete m bidsRoot asksRoot)
lean/MatchingEngine/TheoremsFull.lean:1242:  uniqueOrderIds : Prop
lean/MatchingEngine/TheoremsFull.lean:1296:theorem process_no_duplicate_ids (b : BookState) (o : Order) :
lean/MatchingEngine/TheoremsFull.lean:1312:  exact process_preserves_unique_ids_full b o
lean/MatchingEngine/TheoremsFull.lean:1405:  process_no_duplicate_ids
```

Finding: The C bridge has `UniqueOrderIDs` and an `AmccMemoryContract.unique_order_ids` field, but I found no theorem deriving unique IDs from pointer traversal or hash/tree structure. The property is assumed as an input contract at `lean/Bridge/RelationalMemory.lean:184`.

### C5 Sortedness weakening

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba lean/Bridge/RelationalMemory.lean | sed -n '175,224p'
```

Output:

```text
   175	structure AmccMemoryContract (m : Mem) (bidsRoot asksRoot : Option Ptr) : Prop where
   176	  bids_tree_sorted : SortedBids (alpha_concrete m bidsRoot asksRoot)
   177	  asks_tree_sorted : SortedAsks (alpha_concrete m bidsRoot asksRoot)
   178	  bids_nonempty : ∀ lvl, lvl ∈ (alpha_concrete m bidsRoot asksRoot).bids → lvl.orders ≠ []
   179	  asks_nonempty : ∀ lvl, lvl ∈ (alpha_concrete m bidsRoot asksRoot).asks → lvl.orders ≠ []
   180	  order_backptr_valid :
   181	    ∀ lvl, lvl ∈ (alpha_concrete m bidsRoot asksRoot).bids ++ (alpha_concrete m bidsRoot asksRoot).asks →
   182	      ∀ o, o ∈ lvl.orders → o.price = lvl.price
   183	  unique_order_ids : UniqueOrderIDs (alpha_concrete m bidsRoot asksRoot)
   184	  no_self_trades : NoSelfTrades (alpha_concrete m bidsRoot asksRoot)
   185	  bid_ask_uncrossed : Uncrossed (alpha_concrete m bidsRoot asksRoot)
   186	
   187	structure WfMem (m : Mem) (bidsRoot asksRoot : Option Ptr) : Prop where
   188	  bids_wf : WfTree m bidsRoot
   189	  asks_wf : WfTree m asksRoot
   190	  llist_wf :
   191	    ∀ p, p ∈ collectTreePtrs m bidsRoot ++ collectTreePtrs m asksRoot →
   192	      WfLevelList m p
   193	  contract : AmccMemoryContract m bidsRoot asksRoot
   194	
   195	theorem wf_mem_implies_AllInv
   196	    (m : Mem) (bidsRoot asksRoot : Option Ptr)
   197	    (h : WfMem m bidsRoot asksRoot) :
   198	    AllInv (alpha_concrete m bidsRoot asksRoot) := by
   199	  exact {
   200	    uncrossed := h.contract.bid_ask_uncrossed
   201	    sorted := ⟨h.contract.bids_tree_sorted, h.contract.asks_tree_sorted⟩
   202	    no_empty := by
   203	      intro lvl hmem
   204	      cases List.mem_append.mp hmem with
   205	      | inl hb => exact h.contract.bids_nonempty lvl hb
   206	      | inr ha => exact h.contract.asks_nonempty lvl ha
   207	    no_ghosts := by
   208	      intro lvl hmem o ho
   209	      cases List.mem_append.mp hmem with
   210	      | inl hb => exact h.contract.order_backptr_valid lvl hb o ho
   211	      | inr ha => exact h.contract.order_backptr_valid lvl ha o ho
   212	    unique_ids := h.contract.unique_order_ids
   213	    level_consistent := by
   214	      intro lvl hmem o ho
   215	      cases List.mem_append.mp hmem with
   216	      | inl hb => exact h.contract.order_backptr_valid lvl hb o ho
   217	      | inr ha => exact h.contract.order_backptr_valid lvl ha o ho
   218	    stp_sound := h.contract.no_self_trades
   219	  }
```

Finding: `AllInv.sorted` is copied directly from the `WfMem.contract` precondition. This is a weakening: the bridge theorem does not establish sortedness preservation by C execution.

### C6 Fuel zero behavior

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine/lean
lake env lean lean/AuditScratch.lean
```

Output:

```text
Except.ok ({ glb := [], loc := [], hp := [], next := 0 }, CSubset.Outcome.normal)
```

Finding: The scratch file evaluated `execStmt 0 Stmt.skip { glb := [], loc := [], hp := [], next := 0 }`. It returns `.ok` with `Outcome.normal`. Any no-trap theorem quantified without a fuel-sufficiency condition can be satisfied at zero for at least this trivial statement.

### C7 Fuel sufficiency and independence

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba lean/Bridge/OrderExecution.lean | sed -n '55,85p'
rg -n "fuel.*indep|independent|sufficient|FuelBound|execFuelBound|quantity|remaining" lean/Bridge lean/MatchingEngine
```

Output:

```text
    55	def execFuelBound (contra : List ContraOrder) : Nat :=
    56	  totalRemaining contra + totalOrderCount contra + contra.length + 1
    57	
    58	theorem execFuelBound_positive (contra : List ContraOrder) :
    59	    execFuelBound contra > 0 := by
    60	  unfold execFuelBound
    61	  omega
    62	
    63	theorem popBest_preserves_sorted
    64	    {contra : List ContraOrder}
    65	    (h : SortedByPrice contra) :
    66	    SortedByPrice (contra.drop 1) := by
    67	  cases contra with
    68	  | nil => simp [SortedByPrice]
    69	  | cons head tail =>
    70	      unfold SortedByPrice at h ⊢
    71	      simp at h ⊢
    72	      exact h.2
lean/Bridge/OrderExecution.lean:55:def execFuelBound (contra : List ContraOrder) : Nat :=
lean/Bridge/OrderExecution.lean:58:theorem execFuelBound_positive (contra : List ContraOrder) :
lean/MatchingEngine/Process.lean:15:def defaultFuel (b : BookState) : Nat :=
lean/MatchingEngine/Process.lean:31:def computeMatchFuel (b : BookState) (side : Side) : Nat :=
```

Finding: The C bridge has a quantity-bearing `execFuelBound`, which is good, but I found no fuel-independence theorem for C execution. Without fuel independence, a phrase like "the resulting memory state" is not well-defined for different sufficient fuel values.

### C8 StepRel attachment

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "StepRel|abstract_step|FOK|IOC|PostOnly|Iceberg|STPAction|cancel_old|decrement|cancel_both" lean/Bridge lean/MatchingEngine
```

Output:

```text
lean/Bridge/MatchingEngineBridge.lean:17:  | cancel_old
lean/Bridge/MatchingEngineBridge.lean:18:  | decrement
lean/Bridge/MatchingEngineBridge.lean:19:  | cancel_both
```

Finding: I found no `StepRel` in the C bridge and no theorem of the form `∀ B req, StepRel B req (abstract_step B req)`. The paper's StepRel discussion at `paper_c_engine/paper.tex:308-317` is not attached to the C bridge.

### C9 FIFO step contract counterexample target

Status: CANNOT VERIFY

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "orders\.tail|tail.*orders|FIFO|Queue|popBest|cancel_old|decrement" lean/Bridge lean/MatchingEngine
```

Output:

```text
lean/Bridge/MatchingEngineBridge.lean:17:  | cancel_old
lean/Bridge/MatchingEngineBridge.lean:18:  | decrement
```

Finding: I did not find the specific faulty contract `ℓ'.orders = ℓ.orders.tail` in the C bridge. I also did not find a positive FIFO step contract for the bridge, so there was no theorem target to refute.

## Part D — Claims about C, C++, and generated code

### D1 Generated C files

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
find . -name '*.c' -o -name '*.h' | grep -i gen | head
```

Output:

```text
./c/include/matching_engine_gen.h
./c/src/matching_engine_gen.c
./scripts/gen/orders_gen.h
./scripts/gen/orders_gen.c
./scripts/gen/pool_gen.h
./scripts/gen/pool_gen.c
./scripts/gen/upptr_gen.h
./scripts/gen/upptr_gen.c
./scripts/gen/llist_gen.h
./scripts/gen/llist_gen.c
```

Finding: Generated C artifacts exist.

### D2 Generated C allocation-free claim

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "calloc|realloc|malloc|free" c/src/matching_engine_gen.c c/include/matching_engine_gen.h
```

Output:

```text
c/src/matching_engine_gen.c:15:    OrderChunk* new_chunks = (OrderChunk*)realloc(
c/src/matching_engine_gen.c:26:    PriceLevelChunk* new_chunks = (PriceLevelChunk*)realloc(
c/src/matching_engine_gen.c:37:    chunk.orders = (Order*)calloc(n_orders, sizeof(Order));
c/src/matching_engine_gen.c:52:    chunk.levels = (PriceLevel*)calloc(n_levels, sizeof(PriceLevel));
c/src/matching_engine_gen.c:66:        free(g_EngineDb.order_chunks[i].orders);
c/src/matching_engine_gen.c:71:        free(g_EngineDb.level_chunks[i].levels);
c/src/matching_engine_gen.c:73:    free(g_EngineDb.order_chunks);
c/src/matching_engine_gen.c:78:    free(g_EngineDb.level_chunks);
c/src/matching_engine_gen.c:80:    free(g_EngineDb.ind_order_buckets);
c/src/matching_engine_gen.c:90:    g_EngineDb.ind_order_buckets = (Order**)calloc(ORDER_HASH_BUCKETS, sizeof(Order*));
```

Finding: `paper_c_engine/paper.tex:97` describes allocation-free intrusive C structures. The generated C uses dynamic allocation during initialization/reserve paths. If the intended claim is "no timed hot-path allocation after preallocation", the paper must say that and support it with measurements.

### D3 Hash table implementation and remove

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba c/src/matching_engine_gen.c | sed -n '173,221p'
```

Output:

```text
   173	Order* EngineDb_ind_order_Find(uint64_t key) {
   174	    size_t b = hash_order_id(key) % ORDER_HASH_BUCKETS;
   175	    Order* cur = g_EngineDb.ind_order_buckets[b];
   176	    while (cur) {
   177	        if (cur->order_id == key) return cur;
   178	        cur = cur->ind_order_next;
   179	    }
   180	    return NULL;
   181	}
   182	
   183	int EngineDb_ind_order_Insert(Order* row) {
   184	    if (!row || row->is_active != 1) return 0;
   185	    size_t b = hash_order_id(row->order_id) % ORDER_HASH_BUCKETS;
   186	    if (EngineDb_ind_order_Find(row->order_id)) return 0;  /* unique */
   187	    row->ind_order_next = g_EngineDb.ind_order_buckets[b];
   188	    g_EngineDb.ind_order_buckets[b] = row;
   189	    return 1;
   190	}
   191	
   192	void EngineDb_ind_order_Remove(Order* row) {
   193	    if (!row) return;
   194	    size_t b = hash_order_id(row->order_id) % ORDER_HASH_BUCKETS;
   195	    Order* cur = g_EngineDb.ind_order_buckets[b];
   196	    Order* prev = NULL;
   197	    while (cur) {
   198	        if (cur == row) {
   199	            if (prev) prev->ind_order_next = cur->ind_order_next;
   200	            else g_EngineDb.ind_order_buckets[b] = cur->ind_order_next;
   201	            cur->ind_order_next = NULL;
   202	            return;
   203	        }
   204	        prev = cur;
   205	        cur = cur->ind_order_next;
   206	    }
   207	}
```

Finding: `Thash` is bucket-chained, not open-addressed. Remove splices from a linked bucket chain, so the open-addressing tombstone/probe-chain counterexample does not apply.

### D4 Pointer comparisons in generated C

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "== row|!= row|== NULL|!= NULL|while \(cur\)|if \(cur == row\)" c/src/matching_engine_gen.c scripts/gen
```

Output:

```text
c/src/matching_engine_gen.c:198:        if (cur == row) {
scripts/gen/thash_gen.c:62:        if (cur == row) {
scripts/gen/upptr_gen.c:25:        if (_p->ind_item_next == row) {
```

Finding: Generated code compares pointer-typed operands. I found no corresponding live-pointer side-condition theorem in the C bridge. `paper_c_engine/paper.tex:246-248` states a generated function never traps, but pointer-comparison safety appears to remain outside a formal generated-code theorem.

### D5 Atree balancedness

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba c/src/matching_engine_gen.c | sed -n '295,334p'
```

Output:

```text
   295	static PriceLevel* tree_find(PriceLevel* root, int64_t price) {
   296	    PriceLevel* cur = root;
   297	    while (cur) {
   298	        if (price == cur->price) return cur;
   299	        cur = (price < cur->price) ? cur->tree_left : cur->tree_right;
   300	    }
   301	    return NULL;
   302	}
   303	
   304	static PriceLevel* tree_insert(PriceLevel* root, PriceLevel* node) {
   305	    if (!node) return root;
   306	    node->tree_left = node->tree_right = node->tree_parent = NULL;
   307	    if (!root) return node;
   308	    PriceLevel* cur = root;
   309	    PriceLevel* parent = NULL;
   310	    while (cur) {
   311	        parent = cur;
   312	        if (node->price < cur->price) cur = cur->tree_left;
   313	        else if (node->price > cur->price) cur = cur->tree_right;
   314	        else return root;  /* duplicate */
   315	    }
   316	    node->tree_parent = parent;
   317	    if (node->price < parent->price) parent->tree_left = node;
   318	    else parent->tree_right = node;
   319	    return root;
   320	}
```

Finding: I found no balancing rotations, colors, height fields, or rebalancing. Any `O(log N)` claim for this Atree is unsupported by emitted code.

### D6 C++ baseline containers and includes

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba cpp_reference/src/engine.h | sed -n '1,8p'
nl -ba cpp_reference/src/engine.h | sed -n '87,96p'
rg -n "memory_resource|std::pmr|std::list|std::map|std::vector|new Order|new PriceLevel" cpp_reference/src
```

Output:

```text
     1	#pragma once
     2	#include "types.h"
     3	#include <map>
     4	#include <vector>
     5	#include <algorithm>
     6	#include <cassert>
     7	#include <new>
     8	#include <cstring>
    87	    using BidMap = std::map<Price, PriceLevel*, std::greater<Price>>;
    88	    using AskMap = std::map<Price, PriceLevel*, std::less<Price>>;
    89	
    90	    BidMap bids_;
    91	    AskMap asks_;
    92	    OrderIndex orderIndex_;
    93	    OrderPool pool_;
    94	    std::vector<StopOrder> stops_;
    95	    std::vector<Trade> trades_;
cpp_reference/src/engine.h:3:#include <map>
cpp_reference/src/engine.h:4:#include <vector>
cpp_reference/src/engine.h:87:    using BidMap = std::map<Price, PriceLevel*, std::greater<Price>>;
cpp_reference/src/engine.h:88:    using AskMap = std::map<Price, PriceLevel*, std::less<Price>>;
cpp_reference/src/engine.h:269:            return new Order();
cpp_reference/src/engine.h:275:        auto* pl = new PriceLevel();
```

Finding: The baseline uses `std::map`, `std::vector`, custom `OrderPool`, and explicit `new`. I found no `std::pmr` or `<memory_resource>` in source. `paper_c_engine/paper.tex:467-470` describes `std::map` and pooled order records, which is mostly consistent; it does not claim PMR here.

### D7 Dynamic heap allocation measurement

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
command -v valgrind && valgrind --tool=dhat --quiet ./bin/bench_matching_engine 2>&1 | tail -80
ls -t dhat.out.* | head -5
sed -n '1,80p' "$(ls -t dhat.out.* | head -1)"
```

Output:

```text
/usr/bin/valgrind
===================================================================
   HIGH-FREQUENCY VERIFIED C MATCHING ENGINE BENCHMARK            
   Built with AMCC Provably-Correct Low-Level C Data Structures   
===================================================================

Executing matching workload: 1000000 orders...

--- Performance Results ---
  Workload        : 1000000 mixed operations (Inserts, Matches, Cancels)
  Elapsed Time    : 0.8392 seconds
  Throughput      : 1.19 Million orders/sec
  Average Latency : 839.20 ns/order
  Total Trades    : 348096 fills
  Total Volume    : 3623996 shares traded

--- Verification & Invariant Checking ---
  Book Invariant (Uncrossed Bids < Asks) : [32m[PASS][0m
  Active Orders in Hash Index            : 282637
  Active Bids Price Levels               : 79
  Active Asks Price Levels               : 80

===================================================================
   SUCCESS: Verified C matching engine executed at line rate!     
===================================================================
dhat.out.1761506
{"dhatFileVersion":2,"mode":"heap","verb":"--quiet","bklt":true,"bkacc":true,"bu":{"bytes":1,"blocks":1},"bs":[10,20,30,40,50,60,70,80,90,100],"pps":[{"tb":4096,"tbk":1,"tl":0,"mb":4096,"mbk":1,"gb":0,"gbk":0,"eb":4096,"ebk":1,"rb":1,"wb":2526,"fs":[1,2]},{"tb":67108864,"tbk":1,"tl":1605240544,"mb":67108864,"mbk":1,"gb":0,"gbk":0,"eb":67108864,"ebk":1,"rb":8,"wb":16777216,"fs":[3,4,5,6]},{"tb":520000000,"tbk":1,"tl":1605687552,"mb":520000000,"mbk":1,"gb":0,"gbk":0,"eb":520000000,"ebk":1,"rb":175549713,"wb":74907703,"fs":[3,7,5,6]},{"tb":128,"tbk":1,"tl":1605492800,"mb":128,"mbk":1,"gb":0,"gbk":0,"eb":128,"ebk":1,"rb":0,"wb":16,"fs":[8,9,5,6]},{"tb":40000000,"tbk":1,"tl":1605475272,"mb":40000000,"mbk":1,"gb":0,"gbk":0,"eb":40000000,"ebk":1,"rb":250000,"wb":250000,"fs":[8,10,5,6]},{"tb":128,"tbk":1,"tl":1605460176,"mb":128,"mbk":1,"gb":0,"gbk":0,"eb":128,"ebk":1,"rb":0,"wb":16,"fs":[8,11,5,6]}]
```

Finding: DHAT confirms heap allocations in the C benchmark process, including large `calloc` allocations from initialization paths. This contradicts an unqualified "0 bytes dynamic heap allocations" claim. It does not prove hot-loop allocation, so a narrowed steady-state claim would require a separate measurement.

## Part E — Benchmark arithmetic and reproducibility

### E1 Per-class weighted mean

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba paper_c_engine/paper.tex | sed -n '499,502p'
```

Output:

```text
   499	\begin{tabular}{lrrrr}
   500	\toprule
   501	Operation & Share & Mean ns & p50 ns & p99 ns\\
   502	\midrule
```

Finding: The table rows were checked in `paper_c_engine/paper.tex`; the printed class shares are 50% insert, 25% match, and 25% cancel. Using the printed means:

`0.50 * 59.1 + 0.25 * 156.8 + 0.25 * 42.3 = 79.325 ns`.

The paper's headline C mean is `69.51 ns`, so the residual is `-9.82 ns`. I found no measured overhead row that reconciles this; an overhead row cannot be inferred by subtraction.

### E2 Rerun benchmark

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
make bench 2>&1 | tee /tmp/audit-bench.txt
```

Output:

```text
./bin/bench_matching_engine
===================================================================
   HIGH-FREQUENCY VERIFIED C MATCHING ENGINE BENCHMARK            
   Built with AMCC Provably-Correct Low-Level C Data Structures   
===================================================================

Executing matching workload: 1000000 orders...

--- Performance Results ---
  Workload        : 1000000 mixed operations (Inserts, Matches, Cancels)
  Elapsed Time    : 0.0490 seconds
  Throughput      : 20.40 Million orders/sec
  Average Latency : 49.03 ns/order
  Total Trades    : 348096 fills
  Total Volume    : 3623996 shares traded

--- Verification & Invariant Checking ---
  Book Invariant (Uncrossed Bids < Asks) : [32m[PASS][0m
  Active Orders in Hash Index            : 282637
  Active Bids Price Levels               : 79
  Active Asks Price Levels               : 80

===================================================================
   SUCCESS: Verified C matching engine executed at line rate!     
===================================================================
```

Finding: The rerun produced `20.40 Million orders/sec` and `49.03 ns/order`, not the paper's `14.39 Million orders/sec` and `69.51 ns/order` at `paper_c_engine/paper.tex:461-484`. Same deterministic fills and volume were produced, so the workload appears consistent but the headline timing is not reproducible from this run.

### E3 Workload realism

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
nl -ba c/bench/bench_matching_engine.c | sed -n '38,66p'
```

Output:

```text
    38	    printf("Executing matching workload: %zu orders...\n\n", WORKLOAD_SIZE);
    39	
    40	    /* Pre-populate book with liquidity */
    41	    for (int i = 0; i < 10000; i++) {
    42	        EngineDb_AddOrder(next_order_id++, 1000 + i, 9900 + (i % 100), 1000 + (i % 500), 0);  /* bids */
    43	        EngineDb_AddOrder(next_order_id++, 2000 + i, 10100 + (i % 100), 1000 + (i % 500), 1);  /* asks */
    44	    }
    45	
    46	    uint64_t start = ns_now();
    47	
    48	    for (size_t i = 0; i < WORKLOAD_SIZE; i++) {
    49	        int op = i % 4;
    50	        if (op == 0 || op == 1) {
    51	            /* 50% limit orders (add liquidity) */
    52	            uint64_t price = (op == 0) ? 9950 + (i % 100) : 10050 + (i % 100);
    53	            uint8_t side = (op == 0) ? 0 : 1;
    54	            EngineDb_AddOrder(next_order_id++, 3000 + i, price, 100 + (i % 900), side);
    55	        } else if (op == 2) {
    56	            /* 25% marketable orders (take liquidity) */
    57	            uint64_t price = 10500;  /* crosses */
    58	            EngineDb_AddOrder(next_order_id++, 4000 + i, price, 50 + (i % 200), 0);
    59	        } else {
    60	            /* 25% cancellations */
    61	            uint64_t cancel_id = 1 + (i % next_order_id);
    62	            EngineDb_CancelOrder(cancel_id);
    63	        }
    64	    }
```

Finding: The class shares sum to 100% and match the benchmark code. From the rerun, fills per marketable order are `348096 / 250000 = 1.392384`, so the matching path is not exclusively single-fill, but it is still a light average sweep.

## Part F — Cross-artifact consistency

### F1 External artifact repository

Status: CANNOT VERIFY

Command:

```bash
git ls-remote https://github.com/formally-verified-exchange/verified-matching-engine.git HEAD
d=/tmp/audit-verified-matching-engine-$$; git clone --depth 1 https://github.com/formally-verified-exchange/verified-matching-engine.git "$d" 2>&1; echo CLONED_DIR="$d"; find "$d" -maxdepth 3 -type f | sed "s#$d/##" | sort | head -120
```

Output:

```text
faf9e4d85167f3a965128f35a2c1e1e4ed12a901	HEAD
Cloning into '/tmp/audit-verified-matching-engine-1761708'...
CLONED_DIR=/tmp/audit-verified-matching-engine-1761708
.git/HEAD
.git/config
.git/description
.git/hooks/applypatch-msg.sample
.git/hooks/commit-msg.sample
.git/hooks/fsmonitor-watchman.sample
.git/hooks/post-update.sample
.git/hooks/pre-applypatch.sample
.git/hooks/pre-commit.sample
.git/hooks/pre-merge-commit.sample
.git/hooks/pre-push.sample
.git/hooks/pre-rebase.sample
.git/hooks/pre-receive.sample
.git/hooks/prepare-commit-msg.sample
.git/hooks/push-to-checkout.sample
.git/hooks/update.sample
.git/index
.git/info/exclude
.git/logs/HEAD
.git/packed-refs
.git/shallow
```

Finding: The external repo exists, but this C artifact does not cite a C artifact URL that I could check. The full-domain paper's predecessor repository has `matcher_lean/MatchingEngine/TheoremsFull.lean`, but not the C bridge modules under the same names.

### F2 `AllInv` name collision with predecessor-style source

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "def AllInv|structure AllInv" lean
```

Output:

```text
lean/Bridge/MatchingEngineBridge.lean:96:structure AllInv (book : CBookState) : Prop where
lean/MatchingEngine/Theorems.lean:54:def AllInv (b : BookState) : Prop :=
```

Finding: There are two differently shaped `AllInv` definitions: one over `CBookState` and one over full-domain `BookState`. The C paper should be explicit when it imports the name, because statements about "full AllInv" are ambiguous.

### F3 Advertised features with missing C proof obligations

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "FOK|IOC|Post-Only|post-only|Iceberg|iceberg|STP|cancel_new|cancel_old|decrement|cancel_both|timestamp|FIFO" paper_c_engine/paper.tex lean/Bridge lean/MatchingEngine
```

Output:

```text
paper_c_engine/paper.tex:99:... full AllInv suite (uncrossed books, FIFO, unique IDs, STP safety) ...
paper_c_engine/paper.tex:308:... StepRel ...
paper_c_engine/paper.tex:317:... FOK, IOC, Post-Only, and four STP policies ...
lean/Bridge/MatchingEngineBridge.lean:16:  | cancel_new
lean/Bridge/MatchingEngineBridge.lean:17:  | cancel_old
lean/Bridge/MatchingEngineBridge.lean:18:  | decrement
lean/Bridge/MatchingEngineBridge.lean:19:  | cancel_both
```

Finding: In the C bridge I found enum constructors for four STP actions, but no attached StepRel contract covering FOK, IOC, Post-Only, Iceberg, or all STP policies. FIFO is not expressible from the C decoded order because there is no timestamp.

### F4 Table 5 incommensurability

Status: CANNOT VERIFY

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
rg -n "Table 5|tab:|Compare|comparison|throughput|latency|allocation|alloc" paper_c_engine/paper.tex paper_formal_spec/paper.tex
```

Output:

```text
paper_c_engine/paper.tex:457:\begin{table}[t]
paper_c_engine/paper.tex:485:\caption{C versus C++ baseline on the same deterministic one-million-order workload.}
paper_c_engine/paper.tex:508:\caption{Per-class latency profile for the generated C engine.}
```

Finding: I found the C-vs-C++ table and per-class table in the C paper, but not a Table 5 cross-system comparison in this artifact.

## Additional executed checks

### Paper builds

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
make paper1 paper2
```

Output:

```text
Output written on paper_formal_spec/paper.pdf (27 pages, 293968 bytes).
Transcript written on paper_formal_spec/paper.log.
Output written on paper_c_engine/paper.pdf (10 pages, 246524 bytes).
Transcript written on paper_c_engine/paper.log.
```

Finding: Both papers build to PDF.

### C++ verification harness

Status: PASS

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
cmake -S cpp_reference -B /tmp/uvme-cpp-recheck >/tmp/audit-cpp-cmake.txt 2>&1 && cmake --build /tmp/uvme-cpp-recheck >/tmp/audit-cpp-build.txt 2>&1 && ctest --test-dir /tmp/uvme-cpp-recheck --output-on-failure
```

Output:

```text
Test project /tmp/uvme-cpp-recheck
    Start 1: conformance_tests
1/3 Test #1: conformance_tests ................   Passed    0.00 sec
    Start 2: shadow_runner
2/3 Test #2: shadow_runner ....................   Passed    0.00 sec
    Start 3: unit_tests
3/3 Test #3: unit_tests .......................   Passed    0.00 sec

100% tests passed, 0 tests failed out of 3

Total Test time (real) =   0.01 sec
```

Finding: The C++ tests pass in a fresh build directory.

### Repository smoke script

Status: FAIL

Command:

```bash
cd /home/aaslyan/unified-verified-matching-engine
bash scripts/smoke.sh
```

Output:

```text
error: unknown target 'amcc'
```

Finding: `scripts/smoke.sh` refers to a Lake target `amcc` that does not exist in `lean/lakefile.toml`.

## Claims in the paper I could not support from the artifact

- `paper_c_engine/paper.tex:97`: "AMCC synthesizes provably memory-safe, allocation-free intrusive C structures." The emitted C allocates dynamically and I found no full emitted-code safety theorem.
- `paper_c_engine/paper.tex:99`: "the decoded state satisfies the full AllInv suite (uncrossed books, FIFO, unique IDs, STP safety)." FIFO cannot be represented by the C decoded order, STP is policy-blind, and unique IDs are an assumed contract field.
- `paper_c_engine/paper.tex:143-163`: the concrete C transition diagram with `execStmt(P, fuel, order_stmt, m) = ok m'`. The capstone theorem does not contain that transition.
- `paper_c_engine/paper.tex:176`: "every order execution step preserves uncrossed books and book invariants" for emitted C functions. The theorem proves pre-state `AllInv` and properties of abstract helper outputs, not post-state C memory preservation.
- `paper_c_engine/paper.tex:246-248`: "for any accepted schema S, genC S has Wf.check = [] and the generated function never traps." I found prose/trusted status in `lean/Amcc.lean` and no exhaustive theorem over generated C code.
- `paper_c_engine/paper.tex:308-317`: StepRel coverage for quantity conservation, monotone clock, FOK, IOC, Post-Only, and four STP policies. I found no attached C-bridge `StepRel`.
- `paper_c_engine/paper.tex:325-329`: `WfMem` described as direct pointer validity/readability/well-typedness/finite/acyclic/decode-success evidence. Current `WfMem` delegates much of the semantic content to `AmccMemoryContract`.
- `paper_c_engine/paper.tex:461-484`: benchmark headline numbers. Rerun produced materially different latency/throughput.
- `paper_c_engine/paper.tex:499-502`: per-class latency table. The printed weighted mean does not match the headline mean and no measured overhead row reconciles it.
- `paper_c_engine/paper.tex:541`: "the generated C engine simulates the abstract matching transition system" and "unconditionally preserves global book invariants." I found no such generated-C simulation theorem.

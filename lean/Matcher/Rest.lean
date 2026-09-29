import Matcher.Outer

/-!
# Phase 4: resting the remainder

After the matching loop, a LIMIT or POST_ONLY order with quantity left rests:
the matcher allocates an order row, fills in its seven fields, finds or
creates the level at its price in the own tree, appends the order to the
level's queue and hashes it. The spec's `dispose` does `insertOrder`, which is
`insertDesc` (bids) or `insertAsc` (asks) at the order's price.

The pure part relates the two (`insSpec_fresh`, `insSpec_exists`,
`sortLevels_map`); `rest_step` runs the program part.
-/

namespace MatcherRest

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore MatcherLoop MatcherSpec MatcherInner MatcherOuter

-- ============================================================================
-- insertDesc / insertAsc against the decoded side
-- ============================================================================

/-- The spec's insertion into the side of tree `t`. -/
def insSpec : Tree → List PriceLevel → Order → Nat → List PriceLevel
  | .bids, L, o, p => insertDesc L o p
  | .asks, L, o, p => insertAsc L o p

/-- A fresh price: a new level, in sorted position. -/
theorem insSpec_fresh (t : Tree) (o : Order) (p : Nat) :
    ∀ (L : List PriceLevel), (∀ y ∈ L, y.price ≠ p) →
      insSpec t L o p = insLevel t { price := p, orders := [o] } L
  | [], _ => by cases t <;> rfl
  | y :: ys, h => by
    have ih := insSpec_fresh t o p ys (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hy : y.price ≠ p := h y List.mem_cons_self
    have hne : (p == y.price) = false := beq_eq_false_iff_ne.mpr (Ne.symm hy)
    cases t
    · simp only [insSpec] at ih ⊢
      unfold insertDesc insLevel
      simp only [prioB, gt_iff_lt, decide_eq_true_eq, hne, Bool.false_eq_true, if_false]
      split
      · rfl
      · rw [ih]
    · simp only [insSpec] at ih ⊢
      unfold insertAsc insLevel
      simp only [prioB, decide_eq_true_eq, hne, Bool.false_eq_true, if_false]
      split
      · rfl
      · rw [ih]

/-- Append order `o` to the level at price `p`. -/
def appAt (p : Nat) (o : Order) (y : PriceLevel) : PriceLevel :=
  if y.price = p then { y with orders := y.orders ++ [o] } else y

/-- An existing price: the order joins that level. -/
theorem insSpec_exists (t : Tree) (o : Order) (p : Nat) :
    ∀ (L : List PriceLevel), L.Pairwise (fun a b => prioB t a.price b.price = true) →
      (∃ y ∈ L, y.price = p) → insSpec t L o p = L.map (appAt p o)
  | [], _, ⟨_, hy, _⟩ => by cases hy
  | y :: ys, hs, hex => by
    rw [List.pairwise_cons] at hs
    by_cases hyp : y.price = p
    · have hrest : ∀ z ∈ ys, z.price ≠ p := by
        intro z hz e
        have := hs.1 z hz
        rw [hyp, e] at this
        cases t <;> simp [prioB] at this
      have hmap : ys.map (appAt p o) = ys :=
        (List.map_congr_left (g := id) fun z hz => by simp [appAt, hrest z hz]).trans (List.map_id ys)
      cases t
      · simp only [insSpec, insertDesc, List.map_cons, hmap, appAt, hyp, if_true]
        simp
      · simp only [insSpec, insertAsc, List.map_cons, hmap, appAt, hyp, if_true]
        simp
    · have hex' : ∃ z ∈ ys, z.price = p := by
        obtain ⟨z, hz, e⟩ := hex
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd e hyp
        · exact ⟨z, hz, e⟩
      have ih := insSpec_exists t o p ys hs.2 hex'
      obtain ⟨z, hz, ez⟩ := hex'
      have hyz := hs.1 z hz
      rw [ez] at hyz
      cases t
      · simp only [prioB, decide_eq_true_eq] at hyz
        simp only [insSpec] at ih ⊢
        unfold insertDesc
        have h1 : ¬ p > y.price := by omega
        have h2 : ¬ (p == y.price) = true := by simp; omega
        rw [if_neg h1, if_neg h2, ih]
        simp [appAt, hyp]
      · simp only [prioB, decide_eq_true_eq] at hyz
        simp only [insSpec] at ih ⊢
        unfold insertAsc
        have h1 : ¬ p < y.price := by omega
        have h2 : ¬ (p == y.price) = true := by simp; omega
        rw [if_neg h1, if_neg h2, ih]
        simp [appAt, hyp]

theorem insLevel_map (t : Tree) (f : PriceLevel → PriceLevel) (hf : ∀ y, (f y).price = y.price)
    (x : PriceLevel) : ∀ (ys : List PriceLevel),
      insLevel t (f x) (ys.map f) = (insLevel t x ys).map f
  | [] => rfl
  | y :: ys => by
    simp only [List.map_cons, insLevel, hf]
    split
    · rfl
    · rw [insLevel_map t f hf x ys]; rfl

/-- Sorting commutes with a map that keeps prices. -/
theorem sortLevels_map (t : Tree) (f : PriceLevel → PriceLevel) (hf : ∀ y, (f y).price = y.price) :
    ∀ (L : List PriceLevel), sortLevels t (L.map f) = (sortLevels t L).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, sortLevels]
    rw [sortLevels_map t f hf xs, insLevel_map t f hf]

theorem insLevel_views (t : Tree) {x x' : PriceLevel} (hp : x.price = x'.price)
    (hv : levelView x = levelView x') : ∀ (L : List PriceLevel),
      (insLevel t x L).map levelView = (insLevel t x' L).map levelView
  | [] => by simp [insLevel, hv]
  | y :: ys => by
    simp only [insLevel, hp]
    split
    · simp [hv]
    · simp only [List.map_cons, insLevel_views t hp hv ys]

theorem appAt_views {p : Nat} {o o' : Order} (h : orderView o = orderView o') (L : List PriceLevel) :
    (L.map (appAt p o)).map levelView = (L.map (appAt p o')).map levelView := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro y _
  simp only [Function.comp, appAt]
  split
  · simp [levelView, h]
  · rfl

-- ============================================================================
-- The store after resting, as views
-- ============================================================================

/-- A new order row `h`. -/
def allocDb (db : Db) (h : OrderH) (row : OrderRow) : Db :=
  { db with orders := upd db.orders h (some row), oLive := h :: db.oLive }

/-- A new level `l` at price `p` in tree `t`. -/
def levelDb (db : Db) (t : Tree) (l : LevelH) (p : UInt64) : Db :=
  { db with levels := upd db.levels l (some { price := p }), lLive := l :: db.lLive,
            tree := upd db.tree t (l :: db.tree t) }

/-- Order `h` joins the tail of level `l` and the hash. -/
def joinDb (db : Db) (l : LevelH) (h : OrderH) : Db :=
  { db with queue := upd db.queue l (db.queue l ++ [h]), hash := h :: db.hash }

variable {S : Type} [EngineDb S]

open EngineDb

section Prog

variable {s : S} {r : CRequest} {L : Loc} {ts : List TradeObs}

theorem ev_setOrd {f : OField} {e : Expr} {val : Val} {h : OrderH} {row row' : OrderRow}
    (ho : L.ord = some h) (hlo : liveO (view s) h = true) (hr : readOrder s h = some row)
    (hnh : h ∉ (view s).hash) (he : evalExpr (mkSt s r L ts) e = .ok val)
    (hset : setOField row f val = .ok row') :
    Eval program (call0 (.setO f) [v "ord", e]) (mkSt s r L ts)
      (mkSt (writeOrder s h row') r L ts, .normal) := by
  have hkey : (decide (f = .id) && inHashB (view s) h) = false := by
    have : inHashB (view s) h = false := by simpa [inHashB] using hnh
    simp [this]
  refine ev_ext (vals := [.order (some h), val]) ?_ (runExt_setO hlo hr hkey hset) rfl
  simp only [List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure]
  rw [show evalExpr (mkSt s r L ts) (v "ord") = .ok (.order (some h)) by lsimp [ho], he]
  rfl

/-- A write to the fresh row `h`, as a view. -/
theorem write_fresh {s : S} {h : OrderH} {row row' : OrderRow} (hw : (view s).WF)
    (hrow : (view s).orders h = some row) (hnh : h ∉ (view s).hash) :
    view (writeOrder s h row') = { view s with orders := upd (view s).orders h (some row') } ∧
      (view (writeOrder s h row')).WF := by
  have hpre : writeOrder.pre (view s) h row' := ⟨row, hrow, fun hh => absurd hh hnh⟩
  have hv := writeOrder_law s h row' hw hpre
  exact ⟨hv, writeOrder_preserves_WF hw hpre hv⟩

theorem step_write {si : S} {db : Db} {h : OrderH} {rowi row' : OrderRow} {f : OField} {e : Expr}
    {val : Val} (hv : view si = allocDb db h rowi) (hw : (view si).WF) (hnh : h ∉ db.hash)
    (ho : L.ord = some h) (he : evalExpr (mkSt si r L ts) e = .ok val)
    (hset : setOField rowi f val = .ok row') :
    Eval program (call0 (.setO f) [v "ord", e]) (mkSt si r L ts)
      (mkSt (writeOrder si h row') r L ts, .normal) ∧
    view (writeOrder si h row') = allocDb db h row' ∧ (view (writeOrder si h row')).WF ∧
    count (writeOrder si h row') = count si ∧ levelsUsed (writeOrder si h row') = levelsUsed si := by
  have hrow : (view si).orders h = some rowi := by rw [hv]; simp [allocDb]
  have hnh' : h ∉ (view si).hash := by rw [hv]; exact hnh
  obtain ⟨hv', hw'⟩ := write_fresh (row' := row') hw hrow hnh'
  refine ⟨ev_setOrd ho (by simp [liveO, hrow]) (by rw [readOrder_law]; exact hrow) hnh' he hset, ?_, hw',
    count_writeOrder _ _ _, levelsUsed_writeOrder _ _ _⟩
  rw [hv', hv]
  simp only [allocDb]
  congr 1
  funext x
  by_cases hx : x = h
  · subst hx; simp
  · simp [upd_other _ _ hx]

theorem restRow_eq (r : CRequest) (rem : UInt64) (row0 : OrderRow) :
    { row0 with id := r.id, account := r.account, side := r.side, stpMode := r.stpMode,
                price := r.price, qty := r.qty, remaining := rem } = r.restRow rem := by
  cases row0; rfl

/-- **Allocation and the seven field writes.** -/
theorem rest_prefix (isBuy : Bool) (hI : Inv s) (hcnt : count s < capacity (S := S)) :
    ∃ h s9, (view s).orders h = none ∧ view s9 = allocDb (view s) h (r.restRow L.rem) ∧
      (view s9).WF ∧ count s9 = count s + 1 ∧ levelsUsed s9 = levelsUsed s ∧
      ∀ res, Eval program (Stmt.block ((restStmts isBuy).drop 9)) (mkSt s9 r { L with ord := some h } ts) res →
        Eval program (Stmt.block (restStmts isBuy)) (mkSt s r L ts) res := by
  have hw := hI.wf
  obtain ⟨hpost, hnone⟩ := orderAlloc_law s hw
  cases hr : (orderAlloc s).1 with
  | none => exact absurd ((hnone.mp hr)) (by omega)
  | some h =>
  rw [hr] at hpost
  obtain ⟨hfree, row0, hv2⟩ := hpost
  have hw2 : (view (orderAlloc s).2).WF := orderAlloc_preserves_WF hw (r := some h) (by rw [← hr]; exact (orderAlloc_law s hw).1)
  have hc2 := count_orderAlloc s h hr
  have hl2 := levelsUsed_orderAlloc s
  have hnh : h ∉ (view s).hash := fun hh => by
    have := hw.hash_live h hh; simp [Db.orderLive, hfree] at this
  let L1 : Loc := { L with ord := some h }
  have e1 : Eval program (call1 "ord" .orderAlloc []) (mkSt s r L ts) (mkSt (orderAlloc s).2 r L1 ts, .normal) :=
    ev_ext (vals := []) (by lsimp) runExt_orderAlloc (by simp only [mkSt]; rw [hr]; exact set_ord r L _)
  have e2 : Eval program (whenS (.isNullO (v "ord")) (retc .rejectedCapacity)) (mkSt (orderAlloc s).2 r L1 ts)
      (mkSt (orderAlloc s).2 r L1 ts, .normal) :=
    Eval.when_false (by simp only [L1]; lsimp)
  have hv2' : view (orderAlloc s).2 = allocDb (view s) h row0 := hv2
  have ho : L1.ord = some h := rfl
  obtain ⟨e3, hv3, hw3, hc3, hl3⟩ := step_write (r := r) (ts := ts) (f := .id) (e := v "id")
    (val := .u64 r.id) (row' := { row0 with id := r.id })
    hv2' hw2 hnh ho (by simp only [L1]; lsimp) (by simp [setOField])
  obtain ⟨e4, hv4, hw4, hc4, hl4⟩ := step_write (r := r) (ts := ts) (f := .account) (e := v "account")
    (val := .u64 r.account) (row' := { row0 with id := r.id, account := r.account })
    hv3 hw3 hnh ho (by simp only [L1]; lsimp) (by simp [setOField])
  obtain ⟨e5, hv5, hw5, hc5, hl5⟩ := step_write (r := r) (ts := ts) (f := .side) (e := v "side")
    (val := .code r.side) (row' := { row0 with id := r.id, account := r.account, side := r.side })
    hv4 hw4 hnh ho (by simp only [L1]; lsimp) (by simp [setOField])
  obtain ⟨e6, hv6, hw6, hc6, hl6⟩ := step_write (r := r) (ts := ts) (f := .stpMode) (e := v "stp")
    (val := .code r.stpMode)
    (row' := { row0 with id := r.id, account := r.account, side := r.side, stpMode := r.stpMode })
    hv5 hw5 hnh ho (by simp only [L1]; lsimp) (by simp [setOField])
  obtain ⟨e7, hv7, hw7, hc7, hl7⟩ := step_write (r := r) (ts := ts) (f := .price) (e := v "price")
    (val := .u64 r.price)
    (row' := { row0 with id := r.id, account := r.account, side := r.side, stpMode := r.stpMode, price := r.price })
    hv6 hw6 hnh ho (by simp only [L1]; lsimp) (by simp [setOField])
  obtain ⟨e8, hv8, hw8, hc8, hl8⟩ := step_write (r := r) (ts := ts) (f := .qty) (e := v "qty")
    (val := .u64 r.qty)
    (row' := { row0 with id := r.id, account := r.account, side := r.side, stpMode := r.stpMode, price := r.price, qty := r.qty })
    hv7 hw7 hnh ho (by simp only [L1]; lsimp) (by simp [setOField])
  obtain ⟨e9, hv9, hw9, hc9, hl9⟩ := step_write (r := r) (ts := ts) (f := .remaining) (e := v "rem")
    (val := .u64 L.rem) (row' := r.restRow L.rem)
    hv8 hw8 hnh ho (by simp only [L1]; lsimp) (by simp [setOField, CRequest.restRow])
  refine ⟨h, _, hfree, ?_, hw9, by omega, by omega, fun res hres => ?_⟩
  · exact hv9
  · simp only [restStmts, List.drop] at hres ⊢
    exact Eval.block_cons_normal e1 (Eval.block_cons_normal e2 (Eval.block_cons_normal e3
      (Eval.block_cons_normal e4 (Eval.block_cons_normal e5 (Eval.block_cons_normal e6
      (Eval.block_cons_normal e7 (Eval.block_cons_normal e8 (Eval.block_cons_normal e9 hres
      (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)

-- The remaining statements, one lemma each

theorem ev_tFind (t : Tree) :
    Eval program (call1 "lvl" (.tFind t) [v "price"]) (mkSt s r L ts)
      (mkSt s r { L with lvl := tFind s t r.price } ts, .normal) :=
  ev_ext (vals := [.u64 r.price]) (by lsimp) (runExt_tFind t r.price) (set_lvl r L _)

theorem ev_qInsert {l : LevelH} {h : OrderH} (hl : L.lvl = some l) (ho : L.ord = some h)
    (hll : liveL (view s) l = true) (hlo : liveO (view s) h = true) (hq : queuedB (view s) h = false) :
    Eval program (call0 .qInsertTail [v "lvl", v "ord"]) (mkSt s r L ts)
      (mkSt (qInsertTail s l h) r L ts, .normal) :=
  ev_ext (vals := [.level (some l), .order (some h)]) (by lsimp [hl, ho]) (runExt_qInsertTail hll hlo hq) rfl

theorem ev_hashInsert {h : OrderH} (ho : L.ord = some h) (hlo : liveO (view s) h = true)
    (hin : inHashB (view s) h = false) :
    Eval program (call1 "ok" .hashInsert [v "ord"]) (mkSt s r L ts)
      (mkSt (hashInsert s h).2 r { L with ok := (hashInsert s h).1 } ts, .normal) :=
  ev_ext (vals := [.order (some h)]) (by lsimp [ho]) (runExt_hashInsert hlo hin) (set_ok r L _)

theorem ev_hashFail_ok (isBuy : Bool) (hok : L.ok = true) :
    Eval program (hashFailStmt isBuy) (mkSt s r L ts) (mkSt s r L ts, .normal) :=
  Eval.when_false (by lsimp [hok])

theorem ev_newLevel_skip (isBuy : Bool) {l : LevelH} (hl : L.lvl = some l) :
    Eval program (newLevelStmt isBuy) (mkSt s r L ts) (mkSt s r L ts, .normal) :=
  Eval.when_false (by lsimp [hl])

/-- A new level at the request's price in tree `t`. -/
theorem ev_newLevel (isBuy : Bool) (hl0 : L.lvl = none) (hw : (view s).WF)
    (hlu : levelsUsed s < capacity (S := S))
    (hfresh : ∀ l' ∈ (view s).tree (ownT isBuy), (view s).levelPrice l' ≠ r.price) :
    ∃ lnew s', (view s).levels lnew = none ∧ view s' = levelDb (view s) (ownT isBuy) lnew r.price ∧
      (view s').WF ∧ count s' = count s ∧ levelsUsed s' = levelsUsed s + 1 ∧
      Eval program (newLevelStmt isBuy) (mkSt s r L ts)
        (mkSt s' r { L with lvl := some lnew, isnew := true } ts, .normal) := by
  obtain ⟨hpost, hnone⟩ := levelAlloc_law s hw
  cases hr : (levelAlloc s).1 with
  | none => exact absurd (hnone.mp hr) (by omega)
  | some lnew =>
  rw [hr] at hpost
  obtain ⟨hfree, row0, hv1⟩ := hpost
  have hw1 : (view (levelAlloc s).2).WF :=
    levelAlloc_preserves_WF hw (r := some lnew) (by rw [← hr]; exact (levelAlloc_law s hw).1)
  have hnotT : ∀ t, lnew ∉ (view s).tree t := fun t hm => by
    have := hw.tree_live t lnew hm; simp [Db.levelLive, hfree] at this
  let s1 := (levelAlloc s).2
  let L1 : Loc := { L with lvl := some lnew }
  have hll1 : liveL (view s1) lnew = true := by simp [s1, liveL, hv1]
  have hany1 : inAnyTreeB (view s1) lnew = false := by
    simp only [inAnyTreeB, inTreeB, Bool.or_eq_false_iff, s1, hv1]
    exact ⟨by simpa using hnotT .bids, by simpa using hnotT .asks⟩
  have hrd1 : readLevel s1 lnew = some row0 := by rw [readLevel_law]; simp [s1, hv1]
  have e1 : Eval program (call1 "lvl" .levelAlloc []) (mkSt s r L ts) (mkSt s1 r L1 ts, .normal) :=
    ev_ext (vals := []) (by lsimp) runExt_levelAlloc (by simp only [mkSt]; rw [hr]; exact set_lvl r L _)
  have e2 : Eval program (whenS (.isNullL (v "lvl")) (Stmt.block [call0 .orderFree [v "ord"],
      retc .rejectedCapacity])) (mkSt s1 r L1 ts) (mkSt s1 r L1 ts, .normal) :=
    Eval.when_false (by simp only [L1]; lsimp)
  -- the price
  let s2 := writeLevel s1 lnew { row0 with price := r.price }
  have hpre2 : writeLevel.pre (view s1) lnew { row0 with price := r.price } :=
    ⟨row0, by simp [s1, hv1], fun h => by
      rcases h with h | h
      · exact absurd h (by simpa [s1, hv1] using hnotT .bids)
      · exact absurd h (by simpa [s1, hv1] using hnotT .asks)⟩
  have hv2 : view s2 = { view s1 with levels := upd (view s1).levels lnew (some { row0 with price := r.price }) } :=
    writeLevel_law s1 lnew _ hw1 hpre2
  have hw2 := writeLevel_preserves_WF hw1 hpre2 hv2
  have hv12 : view s2 = { view s with levels := upd (upd (view s).levels lnew (some row0)) lnew (some { row0 with price := r.price }), lLive := lnew :: (view s).lLive } := by
    rw [hv2]; simp only [s1, hv1]
  have e3 : Eval program (call0 (.setL .price) [v "lvl", v "price"]) (mkSt s1 r L1 ts)
      (mkSt s2 r L1 ts, .normal) :=
    ev_ext (vals := [.level (some lnew), .u64 r.price]) (by simp only [L1]; lsimp)
      (runExt_setL_price r.price hll1 hrd1 hany1) rfl
  -- the tree
  have htree2 : (view s2).tree = (view s).tree := by rw [hv12]
  have hlp2 : (view s2).levelPrice lnew = r.price := by
    rw [hv12]; simp [Db.levelPrice]
  have hlp2' : ∀ l' ∈ (view s2).tree (ownT isBuy), (view s2).levelPrice l' = (view s).levelPrice l' := by
    intro l' hl'
    rw [htree2] at hl'
    have hne : l' ≠ lnew := fun e => by subst e; exact hnotT _ hl'
    rw [hv12]; simp [Db.levelPrice, upd_other _ _ hne]
  have hll2 : liveL (view s2) lnew = true := by rw [hv12]; simp [liveL]
  have hany2 : inAnyTreeB (view s2) lnew = false := by
    simp only [inAnyTreeB, inTreeB, Bool.or_eq_false_iff, htree2]
    exact ⟨by simpa using hnotT .bids, by simpa using hnotT .asks⟩
  have hfresh2 : ∀ l' ∈ (view s2).tree (ownT isBuy), (view s2).levelPrice l' ≠ (view s2).levelPrice lnew := by
    intro l' hl'
    rw [hlp2' l' hl', hlp2]
    exact hfresh l' (by rw [htree2] at hl'; exact hl')
  have hpf : priceFreshB (view s2) (ownT isBuy) lnew = true := by
    simp only [priceFreshB, List.all_eq_true, bne_iff_ne, ne_eq]
    exact hfresh2
  have hpre3 : tInsert.pre (view s2) (ownT isBuy) lnew :=
    ⟨hll2, by rw [htree2]; exact hnotT _, by rw [htree2]; exact hnotT _, hfresh2⟩
  have hv3 : view (tInsert s2 (ownT isBuy) lnew) = { view s2 with tree := upd (view s2).tree (ownT isBuy) (lnew :: (view s2).tree (ownT isBuy)) } :=
    tInsert_law s2 (ownT isBuy) lnew hw2 hpre3
  have hw3 := tInsert_preserves_WF hw2 hpre3 hv3
  have e4 : Eval program (call0 (.tInsert (ownT isBuy)) [v "lvl"]) (mkSt s2 r L1 ts)
      (mkSt (tInsert s2 (ownT isBuy) lnew) r L1 ts, .normal) :=
    ev_ext (vals := [.level (some lnew)]) (by simp only [L1]; lsimp) (runExt_tInsert hll2 hany2 hpf) rfl
  have e5 : Eval program (.assign "isnew" (.blit true)) (mkSt (tInsert s2 (ownT isBuy) lnew) r L1 ts)
      (mkSt (tInsert s2 (ownT isBuy) lnew) r { L1 with isnew := true } ts, .normal) :=
    ev_assign (by lsimp) (set_isnew r L1 true)
  refine ⟨lnew, tInsert s2 (ownT isBuy) lnew, hfree, ?_, hw3, ?_, ?_, ?_⟩
  · rw [hv3, htree2, hv12]
    simp only [levelDb]
    congr 1
    funext x
    by_cases hx : x = lnew
    · subst hx; cases row0; simp
    · simp [upd_other _ _ hx]
  · rw [count_tInsert, count_writeLevel]; exact count_levelAlloc s
  · rw [levelsUsed_tInsert, levelsUsed_writeLevel]; exact levelsUsed_levelAlloc s lnew hr
  · exact Eval.when_true (by lsimp [hl0]) (Eval.block_cons_normal e1 (Eval.block_cons_normal e2
      (Eval.block_cons_normal e3 (Eval.block_cons_normal e4 e5 (by simp)) (by simp)) (by simp)) (by simp))

theorem ev_restCond_true (hr : L.rem ≠ 0) (hi : r.orderType ≠ 2) (hm : r.orderType ≠ 1) :
    evalExpr (mkSt s r L ts) restCond = .ok (.bool true) := by
  have : 0 < L.rem := pos_of_ne hr
  simp only [restCond]; lsimp [this, hi, hm]

theorem ev_restCond_false (h : L.rem = 0 ∨ r.orderType = 2 ∨ r.orderType = 1) :
    evalExpr (mkSt s r L ts) restCond = .ok (.bool false) := by
  rcases h with h | h | h
  · simp only [restCond]; lsimp [h]
  · by_cases h0 : 0 < L.rem <;> (simp only [restCond]; lsimp [h, h0])
  · by_cases h0 : 0 < L.rem <;> by_cases h2 : r.orderType = 2 <;> (simp only [restCond]; lsimp [h, h0, h2])

/-- The store after resting, in the two cases: the order joins an existing level
    of its price, or a new level. -/
def RestView (isBuy : Bool) (db db' : Db) (h : OrderH) (row : OrderRow) (p : UInt64)
    (lu lu' : Nat) : Prop :=
  (∃ x, x ∈ db.tree (ownT isBuy) ∧ db.levelPrice x = p ∧ (allocDb db h row).WF ∧
    db' = joinDb (allocDb db h row) x h ∧ lu' = lu) ∨
  (∃ lnew, db.levels lnew = none ∧ (∀ l' ∈ db.tree (ownT isBuy), db.levelPrice l' ≠ p) ∧
    (allocDb db h row).WF ∧ (levelDb (allocDb db h row) (ownT isBuy) lnew p).WF ∧
    db' = joinDb (levelDb (allocDb db h row) (ownT isBuy) lnew p) lnew h ∧ lu' = lu + 1)

theorem not_queued_fresh {db : Db} (hw : db.WF) {h : OrderH} (hf : db.orders h = none) : ¬ db.queued h := by
  rintro ⟨l, hl⟩
  have := (hw.queue_live l h hl).1
  simp [Db.orderLive, hf] at this

/-- **The resting block.** -/
theorem rest_run (isBuy : Bool) (hI : Inv s) (hcnt : count s < capacity (S := S))
    (hid : ∀ h ∈ (view s).hash, (view s).orderId h ≠ r.id)
    (hr : L.rem ≠ 0) (hi : r.orderType ≠ 2) (hm : r.orderType ≠ 1) :
    ∃ s' L' h, (view s).orders h = none ∧
      RestView isBuy (view s) (view s') h (r.restRow L.rem) r.price (levelsUsed s) (levelsUsed s') ∧
      (view s').WF ∧ count s' = count s + 1 ∧
      Eval program (restStmt isBuy) (mkSt s r L ts) (mkSt s' r L' ts, .normal) := by
  have hw := hI.wf
  obtain ⟨h, s9, hfree, hv9, hw9, hc9, hl9, hpre⟩ := rest_prefix (r := r) (L := L) (ts := ts) isBuy hI hcnt
  let row := r.restRow L.rem
  let L1 : Loc := { L with ord := some h }
  have hnq : ¬ (view s).queued h := not_queued_fresh hw hfree
  have hnh : h ∉ (view s).hash := fun hh => by
    have := hw.hash_live h hh; simp [Db.orderLive, hfree] at this
  -- the lookup of the own level
  have e10 := ev_tFind (s := s9) (r := r) (L := L1) (ts := ts) (ownT isBuy)
  have hfind := tFind_law s9 (ownT isBuy) r.price hw9
  have htree9 : (view s9).tree = (view s).tree := by rw [hv9]; rfl
  have hlp9 : ∀ x, (view s9).levelPrice x = (view s).levelPrice x := by intro x; rw [hv9]; rfl
  -- the end of the block, from the level `l` the order joins
  have tail : ∀ (sa : S) (La : Loc) (l : LevelH), La.lvl = some l → La.ord = some h →
      (view sa).WF → liveL (view sa) l = true → (view sa).orders h = some row → ¬ (view sa).queued h →
      (view sa).hash = (view s).hash → (∀ y, y ≠ h → (view sa).orders y = (view s).orders y) →
      ∃ sb, view sb = joinDb (view sa) l h ∧ (view sb).WF ∧ count sb = count sa ∧
        levelsUsed sb = levelsUsed sa ∧
        Eval program (Stmt.block [call0 .qInsertTail [v "lvl", v "ord"], call1 "ok" .hashInsert [v "ord"],
          hashFailStmt isBuy]) (mkSt sa r La ts) (mkSt sb r { La with ok := true } ts, .normal) := by
    intro sa La l hl ho hwa hla hoa hqa hha hya
    have hloa : liveO (view sa) h = true := by simp [liveO, hoa]
    have hpq : qInsertTail.pre (view sa) l h := ⟨hla, hloa, hqa⟩
    have hvq : view (qInsertTail sa l h) = { view sa with queue := upd (view sa).queue l ((view sa).queue l ++ [h]) } :=
      qInsertTail_law sa l h hwa hpq
    have hwq := qInsertTail_preserves_WF hwa hpq hvq
    have hloq : liveO (view (qInsertTail sa l h)) h = true := by rw [hvq]; exact hloa
    have hnhq : h ∉ (view (qInsertTail sa l h)).hash := by rw [hvq, hha]; exact hnh
    have hphi : hashInsert.pre (view (qInsertTail sa l h)) h := ⟨hloq, hnhq⟩
    have hvh := hashInsert_law _ h hwq hphi
    have hnoc : ¬ ∃ h' ∈ (view (qInsertTail sa l h)).hash,
        (view (qInsertTail sa l h)).orderId h' = (view (qInsertTail sa l h)).orderId h := by
      rintro ⟨h', hh', e⟩
      rw [hvq, hha] at hh'
      have hne : h' ≠ h := fun e' => by subst e'; exact hnh hh'
      apply hid h' hh'
      have e1 : (view (qInsertTail sa l h)).orderId h' = (view s).orderId h' := by
        rw [hvq]; simp [Db.orderId, hya h' hne]
      have e2 : (view (qInsertTail sa l h)).orderId h = r.id := by
        rw [hvq]; simp [Db.orderId, hoa, row, CRequest.restRow]
      rw [← e1, e, e2]
    unfold hashInsert.post at hvh
    rw [if_neg hnoc] at hvh
    obtain ⟨hok, hvh⟩ := hvh
    have hwh := hashInsert_preserves_WF hwq hphi (by unfold hashInsert.post; rw [if_neg hnoc]; exact ⟨hok, hvh⟩)
    refine ⟨(hashInsert (qInsertTail sa l h) h).2, ?_, hwh, ?_, ?_, ?_⟩
    · rw [hvh, hvq]; rfl
    · rw [count_hashInsert, count_qInsertTail]
    · rw [levelsUsed_hashInsert, levelsUsed_qInsertTail]
    · have a1 := ev_qInsert (s := sa) (r := r) (L := La) (ts := ts) hl ho hla hloa (queuedB_false_of hqa)
      have a2 := ev_hashInsert (s := qInsertTail sa l h) (r := r) (L := La) (ts := ts) ho hloq
        (by simpa [inHashB] using hnhq)
      rw [hok] at a2
      have a3 := ev_hashFail_ok (s := (hashInsert (qInsertTail sa l h) h).2) (r := r)
        (L := { La with ok := true }) (ts := ts) isBuy rfl
      exact Eval.block_cons_normal a1 (Eval.block_cons_normal a2 a3 (by simp)) (by simp)
  have hrow9 : (view s9).orders h = some row := by rw [hv9]; simp [allocDb, row]
  have hq9 : ¬ (view s9).queued h := by
    rintro ⟨l, hl⟩; rw [hv9] at hl; exact hnq ⟨l, hl⟩
  have hh9 : (view s9).hash = (view s).hash := by rw [hv9]; rfl
  have hy9 : ∀ y, y ≠ h → (view s9).orders y = (view s).orders y := by
    intro y hy; rw [hv9]; simp [allocDb, upd_other _ _ hy]
  have wrap : ∀ {sf : S} {Lf : Loc}, Eval program (Stmt.block ((restStmts isBuy).drop 9))
      (mkSt s9 r L1 ts) (mkSt sf r Lf ts, .normal) →
      Eval program (restStmt isBuy) (mkSt s r L ts) (mkSt sf r Lf ts, .normal) :=
    fun hb => Eval.when_true (ev_restCond_true hr hi hm) (hpre _ hb)
  cases hf : tFind s9 (ownT isBuy) r.price with
  | some x =>
    rw [hf] at hfind e10
    obtain ⟨hx, hxp⟩ := hfind
    have hll : liveL (view s9) x = true := hw9.tree_live _ _ hx
    have e11 := ev_newLevel_skip (s := s9) (r := r) (L := { L1 with lvl := some x }) (ts := ts) isBuy rfl
    obtain ⟨sb, hvb, hwb, hcb, hlb, etail⟩ := tail s9 { L1 with lvl := some x } x rfl rfl hw9 hll hrow9 hq9 hh9 hy9
    refine ⟨sb, { L1 with lvl := some x, ok := true }, h, hfree, Or.inl ⟨x, by rw [← htree9]; exact hx,
      by rw [← hlp9]; exact hxp, by rw [← hv9]; exact hw9, by rw [hvb, hv9], by omega⟩,
      hwb, by omega, wrap ?_⟩
    simp only [restStmts, List.drop]
    exact Eval.block_cons_normal e10 (Eval.block_cons_normal e11 etail (by simp)) (by simp)
  | none =>
    rw [hf] at hfind e10
    have hfresh : ∀ l' ∈ (view s9).tree (ownT isBuy), (view s9).levelPrice l' ≠ r.price := hfind
    have hlu : levelsUsed s9 < capacity (S := S) := by
      have := levels_le_count hI.client
      have := hI.levels_eq; have := hI.count_eq
      omega
    obtain ⟨lnew, s10, hlfree, hv10, hw10, hc10, hl10, e11⟩ :=
      ev_newLevel (s := s9) (r := r) (L := { L1 with lvl := none }) (ts := ts) isBuy rfl hw9 hlu hfresh
    have hll : liveL (view s10) lnew = true := by rw [hv10]; simp [liveL, levelDb]
    obtain ⟨sb, hvb, hwb, hcb, hlb, etail⟩ := tail s10 { L1 with lvl := some lnew, isnew := true } lnew rfl rfl
      hw10 hll (by rw [hv10]; exact hrow9) (by rw [hv10]; exact hq9) (by rw [hv10]; exact hh9)
      (fun y hy => by rw [hv10]; exact hy9 y hy)
    have hfree' : (view s).levels lnew = none := by rw [hv9] at hlfree; exact hlfree
    have hfresh' : ∀ l' ∈ (view s).tree (ownT isBuy), (view s).levelPrice l' ≠ r.price := by
      intro l' hl'; rw [← hlp9]; exact hfresh l' (by rw [htree9]; exact hl')
    have hvf : view sb = joinDb (levelDb (allocDb (view s) h row) (ownT isBuy) lnew r.price) lnew h := by
      rw [hvb, hv10, hv9]
    refine ⟨sb, { L1 with lvl := some lnew, isnew := true, ok := true }, h, hfree,
      Or.inr ⟨lnew, hfree', hfresh', by rw [← hv9]; exact hw9, by rw [← hv9, ← hv10]; exact hw10, hvf, by omega⟩,
      hwb, by omega, wrap ?_⟩
    simp only [restStmts, List.drop]
    exact Eval.block_cons_normal e10 (Eval.block_cons_normal e11 etail (by simp)) (by simp)

end Prog

-- ============================================================================
-- The store after resting: the invariant
-- ============================================================================

section RestInv

variable {D : Db} {t : Tree} {l : LevelH} {h : OrderH} {row : OrderRow}

theorem mem_join_queue (x : LevelH) (y : OrderH) :
    y ∈ (joinDb D l h).queue x ↔ y ∈ D.queue x ∨ (x = l ∧ y = h) := by
  simp only [joinDb]
  by_cases hx : x = l
  · subst hx; simp
  · simp [hx]

theorem join_queued (y : OrderH) : (joinDb D l h).queued y ↔ D.queued y ∨ y = h := by
  constructor
  · rintro ⟨x, hx⟩
    rcases (mem_join_queue x y).mp hx with hx | ⟨_, rfl⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr rfl
  · rintro (⟨x, hx⟩ | rfl)
    · exact ⟨x, (mem_join_queue x y).mpr (Or.inl hx)⟩
    · exact ⟨l, (mem_join_queue l y).mpr (Or.inr ⟨rfl, rfl⟩)⟩

/-- The order joins its level: the client invariant is whole again. -/
theorem join_clientInv (hw : D.WF) (hc : ClientInvM D l) (hl : l ∈ D.tree t)
    (hnq : ¬ D.queued h) (hnh : h ∉ D.hash) (hrow : D.orders h = some row)
    (hside : row.side = sideCode t) (hprice : row.price = D.levelPrice l) (hpos : 0 < row.remaining)
    (hle : row.remaining ≤ row.qty) (hstp : row.stpMode ≤ 4) : ClientInv (joinDb D l h) where
  level_nonempty := by
    intro t' x hx
    show upd D.queue l (D.queue l ++ [h]) x ≠ []
    by_cases hxl : x = l
    · subst hxl; simp
    · rw [upd_other _ _ hxl]; exact hc.level_nonempty t' x hx hxl
  queue_in_tree := by
    intro x y hy
    rcases (mem_join_queue x y).mp hy with hy | ⟨rfl, _⟩
    · exact hc.queue_in_tree x y hy
    · cases t
      · exact Or.inl hl
      · exact Or.inr hl
  hash_iff_queued := by
    intro y
    rw [join_queued]
    show y ∈ h :: D.hash ↔ _
    rw [List.mem_cons, hc.hash_iff_queued y]
    constructor
    · rintro (rfl | hq); exact Or.inr rfl; exact Or.inl hq
    · rintro (hq | rfl); exact Or.inr hq; exact Or.inl rfl
  order_ok := by
    intro t' x hx y hy
    rcases (mem_join_queue x y).mp hy with hy | ⟨rfl, rfl⟩
    · exact hc.order_ok t' x hx y hy
    · have ht : t' = t := by
        by_cases hne : t' = t
        · exact hne
        · exact absurd rfl (tree_ne_of_mem hw (show _ ∈ D.tree t' from hx) hl hne)
      subst ht
      exact ⟨row, hrow, hside, hprice, hpos, hle, hstp⟩
  price_pos := hc.price_pos
  uncrossed := hc.uncrossed

theorem join_restingCount (hw : D.WF) (hl : l ∈ D.tree t) :
    restingCount (joinDb D l h) = restingCount D + 1 := by
  have hG : ∀ y, y ≠ l → ((joinDb D l h).queue y).length = (D.queue y).length := by
    intro y hy; simp [joinDb, upd_other _ _ hy]
  have hGl : ((joinDb D l h).queue l).length = (D.queue l).length + 1 := by simp [joinDb]
  have other : ∀ t', t' ≠ t →
      ((D.tree t').map fun x => ((joinDb D l h).queue x).length).sum =
        ((D.tree t').map fun x => (D.queue x).length).sum := by
    intro t' ht
    exact sum_map_same _ _ fun y hy => hG y (tree_ne_of_mem hw hy hl ht)
  have own := sum_map_update (fun x => (D.queue x).length) (fun x => ((joinDb D l h).queue x).length)
    hG (hw.tree_nodup t) hl
  simp only at own
  rw [hGl] at own
  unfold restingCount
  simp only [List.map_append, List.sum_append_nat]
  show ((D.tree .bids).map fun x => ((joinDb D l h).queue x).length).sum +
      ((D.tree .asks).map fun x => ((joinDb D l h).queue x).length).sum = _
  cases t with
  | bids => rw [other .asks (by decide)]; omega
  | asks => rw [other .bids (by decide)]; omega

theorem alloc_clientInv {db : Db} (_hw : db.WF) (hc : ClientInv db) (hf : db.orders h = none) :
    ClientInv (allocDb db h row) where
  level_nonempty := hc.level_nonempty
  queue_in_tree := hc.queue_in_tree
  hash_iff_queued := hc.hash_iff_queued
  order_ok := by
    intro t' x hx y hy
    obtain ⟨r, hr, h1⟩ := hc.order_ok t' x hx y hy
    have hne : y ≠ h := fun e => by subst e; rw [hf] at hr; cases hr
    exact ⟨r, by simp [allocDb, upd_other _ _ hne, hr], h1⟩
  price_pos := hc.price_pos
  uncrossed := hc.uncrossed

theorem newLevel_clientInvM {db : Db} {lnew : LevelH} {p : UInt64} (hw : db.WF) (hc : ClientInv db)
    (hfree : db.levels lnew = none) (hp : 0 < p)
    (hcross : ∀ y ∈ db.tree (if t = .bids then Tree.asks else Tree.bids),
      if t = .bids then p < db.levelPrice y else db.levelPrice y < p) :
    ClientInvM (levelDb db t lnew p) lnew := by
  have hnotT : ∀ t', lnew ∉ db.tree t' := fun t' hm => by
    have := hw.tree_live t' lnew hm; simp [Db.levelLive, hfree] at this
  have hq0 : db.queue lnew = [] := by
    cases hq : db.queue lnew with
    | nil => rfl
    | cons y ys =>
      have := (hw.queue_live lnew y (by rw [hq]; exact List.mem_cons_self)).2
      simp [Db.levelLive, hfree] at this
  have memT : ∀ t' x, x ∈ (levelDb db t lnew p).tree t' ↔ (t' = t ∧ x = lnew) ∨ x ∈ db.tree t' := by
    intro t' x
    simp only [levelDb]
    by_cases ht : t' = t
    · subst ht; simp [upd_same]
    · simp [ht]
  have lp : ∀ x, x ≠ lnew → (levelDb db t lnew p).levelPrice x = db.levelPrice x := by
    intro x hx; simp [Db.levelPrice, levelDb, upd_other _ _ hx]
  have lpn : (levelDb db t lnew p).levelPrice lnew = p := by simp [Db.levelPrice, levelDb]
  exact
  { level_nonempty := by
      intro t' x hx hxn
      rcases (memT t' x).mp hx with ⟨_, e⟩ | hx
      · exact absurd e hxn
      · exact hc.level_nonempty t' x hx
    queue_in_tree := by
      intro x y hy
      rcases hc.queue_in_tree x y hy with hb | ha
      · exact Or.inl ((memT _ _).mpr (Or.inr hb))
      · exact Or.inr ((memT _ _).mpr (Or.inr ha))
    hash_iff_queued := hc.hash_iff_queued
    order_ok := by
      intro t' x hx y hy
      have hxn : x ≠ lnew := fun e => by subst e; rw [show (levelDb db t x p).queue x = db.queue x from rfl, hq0] at hy; cases hy
      rcases (memT t' x).mp hx with ⟨_, e⟩ | hx
      · exact absurd e hxn
      · obtain ⟨r, hr, h1, h2, h3⟩ := hc.order_ok t' x hx y hy
        exact ⟨r, hr, h1, by rw [lp x hxn]; exact h2, h3⟩
    price_pos := by
      intro t' x hx
      rcases (memT t' x).mp hx with ⟨_, rfl⟩ | hx'
      · rw [lpn]; exact hp
      · have hxn : x ≠ lnew := fun e => hnotT t' (e ▸ hx')
        rw [lp x hxn]; exact hc.price_pos t' x hx'
    uncrossed := by
      intro lb hb la ha
      rcases (memT _ _).mp hb with ⟨ht, rfl⟩ | hb' <;> rcases (memT _ _).mp ha with ⟨ht', rfl⟩ | ha'
      · subst ht; cases ht'
      · subst ht
        have hna : la ≠ lb := fun e => hnotT _ (e ▸ ha')
        rw [lpn, lp la hna]
        have := hcross la (by simpa using ha'); simpa using this
      · subst ht'
        have hnb : lb ≠ la := fun e => hnotT _ (e ▸ hb')
        rw [lpn, lp lb hnb]
        have := hcross lb (by simpa using hb'); simpa using this
      · have hnb : lb ≠ lnew := fun e => hnotT _ (e ▸ hb')
        have hna : la ≠ lnew := fun e => hnotT _ (e ▸ ha')
        rw [lp lb hnb, lp la hna]; exact hc.uncrossed lb hb' la ha' }

end RestInv

-- ============================================================================
-- The store after resting: the decoded sides
-- ============================================================================

section RestViews

theorem absQueue_append (db : Db) (t : Tree) (h : OrderH) :
    ∀ (i : Nat) (hs : List OrderH),
      absQueue db t i (hs ++ [h]) = absQueue db t i hs ++ [restingOrder t (rowOf db h) (i + hs.length)]
  | i, [] => by simp [absQueue, rowOf]
  | i, y :: ys => by
    simp only [List.cons_append, absQueue, absQueue_append db t h (i + 1) ys, List.length_cons]
    rw [show i + 1 + ys.length = i + (ys.length + 1) by omega]

variable {db : Db} {h : OrderH} {row : OrderRow}

/-- A level that neither the new order nor a new level touches decodes the same. -/
theorem absLevel_fresh {db' : Db} {t : Tree} {x : LevelH} (hw : db.WF) (hf : db.orders h = none)
    (hq : db'.queue x = db.queue x) (ho : ∀ y, y ≠ h → db'.orders y = db.orders y)
    (hp : db'.levelPrice x = db.levelPrice x) : absLevel db' t x = absLevel db t x := by
  apply absLevel_congr hq _ hp
  intro y hy
  have : y ≠ h := fun e => by
    subst e; have := (hw.queue_live x y hy).1; simp [Db.orderLive, hf] at this
  exact ho y this

theorem rest_exist_side {isBuy : Bool} {x : LevelH} (hw : db.WF) (hf : db.orders h = none)
    (hx : x ∈ db.tree (ownT isBuy)) :
    absSide (joinDb (allocDb db h row) x h) (ownT isBuy) =
      (absSide db (ownT isBuy)).map (appAt (db.levelPrice x).toNat
        (restingOrder (ownT isBuy) row (db.queue x).length)) := by
  unfold absSide
  rw [← sortLevels_map _ _ (fun y => by unfold appAt; split <;> rfl), List.map_map]
  simp only [joinDb, allocDb]
  congr 1
  apply List.map_congr_left
  intro y hy
  simp only [Function.comp]
  by_cases hyx : y = x
  · subst hyx
    simp only [appAt, absLevel, if_true, upd_same]
    congr 1
    rw [absQueue_append]
    simp only [rowOf, upd_same, Option.getD_some, Nat.zero_add]
    congr 1
    exact absQueue_congr 0 _ (fun z hz => by
      have : z ≠ h := fun e => by
        subst e; have := (hw.queue_live y z hz).1; simp [Db.orderLive, hf] at this
      simp [upd_other _ _ this])
  · have hp : (absLevel db (ownT isBuy) y).price ≠ (db.levelPrice x).toNat := by
      simp only [absLevel]
      intro e
      exact hyx (hw.tree_prices _ y hy x hx (UInt64.toNat_inj.mp e))
    simp only [appAt, hp, if_false]
    exact absLevel_fresh hw hf (by simp [upd_other _ _ hyx]) (fun z hz => by simp [upd_other _ _ hz]) rfl

theorem rest_new_side {isBuy : Bool} {lnew : LevelH} {p : UInt64} (hw : db.WF) (hf : db.orders h = none)
    (hfree : db.levels lnew = none) :
    absSide (joinDb (levelDb (allocDb db h row) (ownT isBuy) lnew p) lnew h) (ownT isBuy) =
      insLevel (ownT isBuy) { price := p.toNat, orders := [restingOrder (ownT isBuy) row 0] }
        (absSide db (ownT isBuy)) := by
  have hnotT : ∀ t', lnew ∉ db.tree t' := fun t' hm => by
    have := hw.tree_live t' lnew hm; simp [Db.levelLive, hfree] at this
  have hq0 : db.queue lnew = [] := by
    cases hq : db.queue lnew with
    | nil => rfl
    | cons y ys =>
      have := (hw.queue_live lnew y (by rw [hq]; exact List.mem_cons_self)).2
      simp [Db.levelLive, hfree] at this
  unfold absSide
  simp only [joinDb, levelDb, allocDb, upd_same, List.map_cons, sortLevels]
  congr 1
  · simp [absLevel, absQueue, hq0, Db.levelPrice]
  · congr 1
    apply List.map_congr_left
    intro y hy
    have hyn : y ≠ lnew := fun e => by subst e; exact hnotT _ hy
    exact absLevel_fresh hw hf (by simp [upd_other _ _ hyn]) (fun z hz => by simp [upd_other _ _ hz])
      (by simp [Db.levelPrice, upd_other _ _ hyn])

theorem rest_other_side {isBuy : Bool} {D : Db} {x : LevelH} (hw : db.WF) (hf : db.orders h = none)
    (hD : D = joinDb (allocDb db h row) x h ∨
      ∃ lnew p, db.levels lnew = none ∧ x = lnew ∧ D = joinDb (levelDb (allocDb db h row) (ownT isBuy) lnew p) lnew h)
    (hx : x ∈ db.tree (ownT isBuy) ∨ db.levels x = none) :
    absSide D (contraT isBuy) = absSide db (contraT isBuy) := by
  have hne := (MatcherOuter.ownT_ne isBuy).symm
  have hxc : x ∉ db.tree (contraT isBuy) := by
    rcases hx with hx | hx
    · exact fun h' => tree_ne_of_mem hw h' hx hne rfl
    · intro h'; have := hw.tree_live _ x h'; simp [Db.levelLive, hx] at this
  unfold absSide
  rcases hD with rfl | ⟨lnew, p, hfree, rfl, rfl⟩
  · simp only [joinDb, allocDb]
    congr 1
    apply List.map_congr_left
    intro y hy
    have hyx : y ≠ x := fun e => by subst e; exact hxc hy
    exact absLevel_fresh hw hf (by simp [upd_other _ _ hyx]) (fun z hz => by simp [upd_other _ _ hz]) rfl
  · simp only [joinDb, levelDb, allocDb, upd_other _ _ hne]
    congr 1
    apply List.map_congr_left
    intro y hy
    have hyx : y ≠ x := fun e => by subst e; exact hxc hy
    exact absLevel_fresh hw hf (by simp [upd_other _ _ hyx]) (fun z hz => by simp [upd_other _ _ hz])
      (by simp [Db.levelPrice, upd_other _ _ hyx])

end RestViews

-- ============================================================================
-- The invariant after resting
-- ============================================================================

section RestInvS

variable {S : Type} [EngineDb S]

open EngineDb

theorem rest_inv {isBuy : Bool} {s s' : S} {h : OrderH} {row : OrderRow} {p : UInt64}
    (hI : Inv s) (hcnt : count s < capacity (S := S)) (hf : (view s).orders h = none)
    (hRV : RestView isBuy (view s) (view s') h row p (levelsUsed s) (levelsUsed s'))
    (hw' : (view s').WF) (hc' : count s' = count s + 1)
    (hside : row.side = sideCode (ownT isBuy)) (hprice : row.price = p) (hpos : 0 < row.remaining)
    (hle : row.remaining ≤ row.qty) (hstp : row.stpMode ≤ 4) (hp : 0 < p)
    (hcross : ∀ y ∈ (view s).tree (contraT isBuy),
      if isBuy then p < (view s).levelPrice y else (view s).levelPrice y < p) :
    Inv s' := by
  have hw := hI.wf
  have hnq : ¬ (view s).queued h := not_queued_fresh hw hf
  have hnh : h ∉ (view s).hash := fun hh => by
    have := hw.hash_live h hh; simp [Db.orderLive, hf] at this
  have hca := alloc_clientInv (row := row) hw hI.client hf
  -- orders
  have ores : ∀ (X : Db) (l : LevelH), X.orders = (allocDb (view s) h row).orders →
      X.queue = (view s).queue → X.hash = (view s).hash → ∀ y,
      (joinDb X l h).orderLive y ↔ (joinDb X l h).queued y := by
    intro X l ho hq hh y
    rw [join_queued]
    show (X.orders y).isSome = true ↔ X.queued y ∨ y = h
    rw [ho]
    have hq' : X.queued y ↔ (view s).queued y := by simp only [Db.queued, hq]
    rw [hq']
    by_cases hy : y = h
    · subst hy; simp [allocDb]
    · simp only [allocDb, upd_other _ _ hy, hy, or_false]
      exact hI.orders_resting y
  rcases hRV with ⟨x, hx, hxp, hwa, hv, hlu⟩ | ⟨lnew, hfree, hfresh, hwa, hwl, hv, hlu⟩
  · refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv]
      exact join_clientInv hwa (ClientInv.toM hca x) hx hnq hnh (by simp [allocDb]) hside
        (by rw [hprice, ← hxp]; rfl) hpos hle hstp
    · rw [hv]; exact ores _ x rfl rfl rfl
    · rw [hv]; exact hI.levels_resting
    · rw [hc', hv, join_restingCount hwa hx]
      show count s + 1 = restingCount (view s) + 1
      rw [hI.count_eq]
    · rw [hlu, hv]; exact hI.levels_eq
    · have := hI.count_le; omega
  · have hcM : ClientInvM (levelDb (allocDb (view s) h row) (ownT isBuy) lnew p) lnew := by
      apply newLevel_clientInvM hwa hca hfree hp
      intro y hy
      cases isBuy
      · have := hcross y (by simpa [ownT, contraT] using hy); simpa [ownT] using this
      · have := hcross y (by simpa [ownT, contraT] using hy); simpa [ownT] using this
    have hlin : lnew ∈ (levelDb (allocDb (view s) h row) (ownT isBuy) lnew p).tree (ownT isBuy) := by
      simp [levelDb]
    have hnotT : ∀ t', lnew ∉ (view s).tree t' := fun t' hm => by
      have := hw.tree_live t' lnew hm; simp [Db.levelLive, hfree] at this
    refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv]
      exact join_clientInv hwl hcM hlin hnq hnh (by simp [levelDb, allocDb]) hside
        (by simp [Db.levelPrice, levelDb, hprice]) hpos hle hstp
    · rw [hv]; exact ores _ lnew rfl rfl rfl
    · rw [hv]
      intro y
      show ((levelDb (allocDb (view s) h row) (ownT isBuy) lnew p).levels y).isSome = true ↔ _
      simp only [joinDb, levelDb, allocDb]
      by_cases hy : y = lnew
      · subst hy
        cases isBuy <;> simp [ownT]
      · rw [upd_other _ _ hy]
        have := hI.levels_resting y
        simp only [Db.levelLive] at this
        rw [this]
        cases isBuy <;> simp [ownT, upd, hy]
    · rw [hc', hv, join_restingCount hwl hlin]
      have : restingCount (levelDb (allocDb (view s) h row) (ownT isBuy) lnew p) = restingCount (view s) := by
        have hq0 : (view s).queue lnew = [] := by
          cases hq : (view s).queue lnew with
          | nil => rfl
          | cons y ys =>
            have := (hw.queue_live lnew y (by rw [hq]; exact List.mem_cons_self)).2
            simp [Db.levelLive, hfree] at this
        unfold restingCount
        simp only [levelDb, allocDb, List.map_append, List.sum_append_nat]
        cases isBuy <;> simp [ownT, upd, hq0]
      rw [this, hI.count_eq]
    · rw [hlu, hv, hI.levels_eq]
      simp only [joinDb, levelDb, allocDb, List.length_append]
      cases isBuy <;> simp [ownT, upd] <;> omega
    · have := hI.count_le; omega

/-- **The decoded book after resting**: the own side is the spec's insertion,
    the contra side is unchanged. -/
theorem rest_book {isBuy : Bool} {db db' : Db} {h : OrderH} {row : OrderRow} {p : UInt64} {lu lu' : Nat}
    {o' : Order} (hw : db.WF) (hf : db.orders h = none)
    (hRV : RestView isBuy db db' h row p lu lu')
    (hov : ∀ n, orderView o' = orderView (restingOrder (ownT isBuy) row n)) :
    (absSide db' (ownT isBuy)).map levelView =
      (insSpec (ownT isBuy) (absSide db (ownT isBuy)) o' p.toNat).map levelView ∧
    absSide db' (contraT isBuy) = absSide db (contraT isBuy) := by
  rcases hRV with ⟨x, hx, hxp, _, hv, _⟩ | ⟨lnew, hfree, hfresh, _, _, hv, _⟩
  · refine ⟨?_, rest_other_side hw hf (Or.inl hv) (Or.inl hx)⟩
    rw [hv, rest_exist_side hw hf hx, hxp,
      insSpec_exists _ o' _ _ (absSide_pairwise hw _) ⟨absLevel db (ownT isBuy) x,
        mem_sortLevels.mpr (List.mem_map_of_mem hx), by simp [absLevel, hxp]⟩]
    exact appAt_views (hov _).symm _
  · refine ⟨?_, rest_other_side hw hf (Or.inr ⟨lnew, p, hfree, rfl, hv⟩) (Or.inr hfree)⟩
    rw [hv, rest_new_side hw hf hfree, insSpec_fresh]
    · exact insLevel_views (ownT isBuy) (x := { price := p.toNat, orders := [restingOrder (ownT isBuy) row 0] })
        (x' := { price := p.toNat, orders := [o'] }) rfl (by simp [levelView, hov 0]) _
    · intro y hy e
      obtain ⟨z, hz, rfl⟩ := mem_absSide hy
      exact hfresh z hz (UInt64.toNat_inj.mp (by simpa [absLevel] using e))

end RestInvS

end MatcherRest

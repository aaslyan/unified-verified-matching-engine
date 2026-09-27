import Matcher.Inner

/-!
# Phase 4: the outer matching loop

Each outer iteration takes the best level of the contra tree, stops when there
is none or it does not cross, and otherwise runs the inner loop on it and frees
it if it emptied. `OInv` is the invariant at outer boundaries: `Inv` holds (no
empty level), the decoded contra side is the spec's contra side through
`levelView`, the own side is untouched, and the spec's remaining computation is
the whole run.

`outer_body` (c): one iteration re-establishes `OInv` with a smaller measure.
`outer_loop` (d): the loop runs to its exit within `capacity + 1`, and then the
spec's remaining computation has terminated (`mr = term …`).
-/

namespace MatcherOuter

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore MatcherLoop MatcherSpec MatcherInner

variable {S : Type} [EngineDb S]

open EngineDb

-- ============================================================================
-- Freeing an emptied level
-- ============================================================================

def freeS (s : S) (t : Tree) (l : LevelH) : S := levelFree (tRemove s t l) l

theorem ev_free (isBuy : Bool) {s : S} {r : CRequest} {L : Loc} {ts : List TradeObs} {l : LevelH}
    (hb : L.best = some l) (hw : (view s).WF) (hin : l ∈ (view s).tree (contraT isBuy))
    (he : (view s).queue l = []) :
    Eval program (freeStmt isBuy) (mkSt s r L ts) (mkSt (freeS s (contraT isBuy) l) r L ts, .normal) ∧
    view (freeS s (contraT isBuy) l) = freeDb (view s) (contraT isBuy) l ∧
    (view (freeS s (contraT isBuy) l)).WF ∧ count (freeS s (contraT isBuy) l) = count s ∧
    levelsUsed (freeS s (contraT isBuy) l) + 1 = levelsUsed s := by
  have hl : liveL (view s) l = true := hw.tree_live _ _ hin
  have hv1 : view (tRemove s (contraT isBuy) l) = { view s with tree := upd (view s).tree (contraT isBuy) (((view s).tree (contraT isBuy)).erase l) } := tRemove_law s _ l hw hin
  have hw1 := tRemove_preserves_WF hw hv1
  have hnotin : ∀ t, l ∉ (view (tRemove s (contraT isBuy) l)).tree t := by
    intro t hm
    rw [hv1] at hm
    by_cases ht : t = contraT isBuy
    · subst ht; simp only [upd_same] at hm; exact (hw.tree_nodup _).not_mem_erase hm
    · simp only [upd_other _ _ ht] at hm; exact tree_ne_of_mem hw hm hin ht rfl
  have hl1 : liveL (view (tRemove s (contraT isBuy) l)) l = true := by rw [hv1]; exact hl
  have hpre : levelFree.pre (view (tRemove s (contraT isBuy) l)) l :=
    ⟨hl1, hnotin .bids, hnotin .asks, by rw [hv1]; exact he⟩
  have hv2 := levelFree_law _ l hw1 hpre
  have hw2 := levelFree_preserves_WF hw1 hpre hv2
  have hlc : levelCount s l < 2 ^ 64 := by rw [levelCount_law]; simp [EngineDbApi.levelCount, he]
  have hc0 : levelCount s l = 0 := by rw [levelCount_law]; simp [EngineDbApi.levelCount, he]
  refine ⟨?_, ?_, hw2, ?_, ?_⟩
  · refine Eval.when_true (by rw [ev_countZero hb hl hlc, decide_eq_true hc0]) ?_
    have a1 : Eval program (call0 (.tRemove (contraT isBuy)) [v "best"]) (mkSt s r L ts)
        (mkSt (tRemove s (contraT isBuy) l) r L ts, .normal) :=
      ev_ext (vals := [.level (some l)]) (by lsimp [hb]) (runExt_tRemove hl (List.contains_iff_mem.mpr hin)) rfl
    have hany : inAnyTreeB (view (tRemove s (contraT isBuy) l)) l = false := by
      simp only [inAnyTreeB, inTreeB, Bool.or_eq_false_iff]
      exact ⟨by simpa using hnotin .bids, by simpa using hnotin .asks⟩
    have a2 : Eval program (call0 .levelFree [v "best"]) (mkSt (tRemove s (contraT isBuy) l) r L ts)
        (mkSt (freeS s (contraT isBuy) l) r L ts, .normal) :=
      ev_ext (vals := [.level (some l)]) (by lsimp [hb])
        (runExt_levelFree hl1 hany (by simp [viewOf, mkSt, hv1, he])) rfl
    exact Eval.block_cons_normal a1 a2 (by simp)
  · unfold freeS; rw [hv2, hv1]; rfl
  · unfold freeS; rw [count_levelFree, count_tRemove]
  · have := levelsUsed_levelFree _ l hw1 hpre
    unfold freeS; rw [levelsUsed_tRemove] at this; exact this

theorem ev_nofree (isBuy : Bool) {s : S} {r : CRequest} {L : Loc} {ts : List TradeObs} {l : LevelH}
    (hb : L.best = some l) (hl : liveL (view s) l = true) (he : (view s).queue l ≠ [])
    (hlc : levelCount s l < 2 ^ 64) :
    Eval program (freeStmt isBuy) (mkSt s r L ts) (mkSt s r L ts, .normal) := by
  have hlen : ((view s).queue l).length ≠ 0 := fun e => he (List.length_eq_zero_iff.mp e)
  exact Eval.when_false (by rw [ev_countZero hb hl hlc, decide_eq_false]; rw [levelCount_law]; exact hlen)

-- ============================================================================
-- The outer invariant
-- ============================================================================

/-- The data fixed during the matching phase of one request. -/
structure MCtx where
  r : CRequest
  isBuy : Bool
  o1 : Order
  own : List PriceLevel
  tm : Timestamp
  mr : MatchResult
  C0 : Nat

abbrev MCtx.t (c : MCtx) : Tree := contraT c.isBuy

structure MCtx.Ok (c : MCtx) : Prop where
  req : ReqOk c.r c.o1
  side : c.o1.side = if c.isBuy then .buy else .sell
  price : c.o1.price = if c.r.orderType = 1 then none else some c.r.price.toNat

/-- **The outer-loop invariant.** -/
structure OInv (c : MCtx) (s : S) (L : Loc) (ts : List TradeObs) (inc : Order)
    (contra : List PriceLevel) (strades : List Trade) : Prop where
  inv : Inv s
  own : absSide (view s) (ownT c.isBuy) = c.own
  spec : c.mr = rest inc c.own contra strades c.tm
  cview : (absSide (view s) c.t).map levelView = contra.map levelView
  aggr : L.rem.toNat = if inc.status = .cancelled then 0 else inc.remainingQty
  shape : IncShape c.o1 inc
  trades : ts = strades.map tradeObs
  tbound : ts.length + count s ≤ c.C0 + (if L.rem = 0 then 1 else 0)
  cnt : count s ≤ c.C0
  hashid : ∀ h ∈ (view s).hash, (view s).orderId h ≠ c.r.id
  remle : L.rem ≤ c.r.qty
  stopT : L.stop = true → c.mr = term inc c.own contra strades c.tm
  stopX : L.stop = true → c.r.orderType ≠ 1 →
    ∀ x ∈ (view s).tree c.t, ¬ crossB c.isBuy ((view s).levelPrice x) c.r.price

def omeasure (c : MCtx) (s : S) (L : Loc) : Nat :=
  ((view s).tree c.t).length + (if L.rem ≠ 0 ∧ L.stop = false then 1 else 0)

theorem notDone_of {inc : Order} {rem : UInt64}
    (hagg : rem.toNat = if inc.status = .cancelled then 0 else inc.remainingQty) (hr : rem ≠ 0) :
    (inc.remainingQty == 0 || inc.status == .cancelled) = false := by
  have hnc : inc.status ≠ .cancelled := by
    intro e; rw [if_pos e] at hagg; exact hr (UInt64.toNat_inj.mp (by rw [hagg]; rfl))
  rw [if_neg hnc] at hagg
  have h1 : inc.remainingQty ≠ 0 := by
    rw [← hagg]; intro e; exact hr (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h2 : (inc.status == OrderStatus.cancelled) = false := by
    cases hst : inc.status <;> first | rfl | exact absurd hst hnc
  simp [h1, h2]

theorem done_of {inc : Order} {rem : UInt64}
    (hagg : rem.toNat = if inc.status = .cancelled then 0 else inc.remainingQty) (hr : rem = 0) :
    (inc.remainingQty == 0 || inc.status == .cancelled) = true := by
  by_cases hc : inc.status = .cancelled
  · exact done_of_cancelled hc
  · rw [if_neg hc, hr] at hagg
    simp [← hagg]

theorem canMatch_iff {c : MCtx} (hc : c.Ok) (lp : UInt64) :
    canMatchPrice c.o1 lp.toNat = true ↔ (c.r.orderType = 1 ∨ crossB c.isBuy lp c.r.price) := by
  unfold canMatchPrice
  rw [hc.price]
  by_cases hm : c.r.orderType = 1
  · simp [hm]
  · simp only [hm, if_false, false_or]
    rw [hc.side]
    cases hb : c.isBuy <;> simp [crossB, UInt64.le_iff_toNat_le]

theorem stopX_of_best {isBuy : Bool} {db : Db} {l : LevelH} {rp : UInt64}
    (hb : ∀ x ∈ db.tree (contraT isBuy), better (contraT isBuy) (db.levelPrice l) (db.levelPrice x))
    (hn : ¬ crossB isBuy (db.levelPrice l) rp) :
    ∀ x ∈ db.tree (contraT isBuy), ¬ crossB isBuy (db.levelPrice x) rp := by
  intro x hx hcx
  have := hb x hx
  cases isBuy <;> simp only [contraT, crossB, better, Bool.false_eq_true, if_false, if_true] at this hn hcx <;>
    rw [UInt64.le_iff_toNat_le] at * <;> omega

theorem map_levelView_cons {L : List PriceLevel} {a : LevelView} {as : List LevelView}
    (h : L.map levelView = a :: as) : ∃ x xs, L = x :: xs ∧ levelView x = a ∧ xs.map levelView = as := by
  cases L with
  | nil => cases h
  | cons x xs => simp only [List.map_cons, List.cons.injEq] at h; exact ⟨x, xs, rfl, h.1, h.2⟩

theorem count_le_cap_lc {s : S} (hI : Inv s) {l : LevelH} {t : Tree} (hl : l ∈ (view s).tree t)
    (hcap : CapOk S) : levelCount s l < 2 ^ 64 := by
  rw [levelCount_law]
  have hq : ((view s).queue l).length ≤ restingCount (view s) := by
    unfold restingCount
    apply le_sum_of_mem_nat
    apply List.mem_map.mpr
    exact ⟨l, by cases t <;> simp [hl], rfl⟩
  have := hI.count_eq; have := hI.count_le
  unfold CapOk at hcap
  simp only [EngineDbApi.levelCount]; omega

-- ============================================================================
-- (c) One outer iteration
-- ============================================================================

/-- The fixed data of one outer iteration. -/
def oc (c : MCtx) (l : LevelH) (db : Db) (RL : List PriceLevel) : OCtx :=
  { r := c.r, isBuy := c.isBuy, o1 := c.o1, own := c.own, tm := c.tm, mr := c.mr, C0 := c.C0,
    l := l, dbR := db, RL := RL }

theorem ownT_ne (isBuy : Bool) : ownT isBuy ≠ contraT isBuy := by
  cases isBuy <;> decide

theorem not_mem_other {db : Db} (hw : db.WF) {l : LevelH} {isBuy : Bool}
    (hl : l ∈ db.tree (contraT isBuy)) : l ∉ db.tree (ownT isBuy) := fun h =>
  tree_ne_of_mem hw h hl (ownT_ne isBuy) rfl

theorem free_levels_resting {db : Db} {t : Tree} {l : LevelH} (hw : db.WF) (hl : l ∈ db.tree t)
    (hr : ∀ x, db.levelLive x ↔ (x ∈ db.tree .bids ∨ x ∈ db.tree .asks)) (x : LevelH) :
    (freeDb db t l).levelLive x ↔ (x ∈ (freeDb db t l).tree .bids ∨ x ∈ (freeDb db t l).tree .asks) := by
  have memT : ∀ t', x ∈ (freeDb db t l).tree t' ↔ x ∈ db.tree t' ∧ x ≠ l := by
    intro t'
    simp only [freeDb]
    by_cases ht : t' = t
    · subst ht
      rw [upd_same]
      constructor
      · intro hx
        exact ⟨List.mem_of_mem_erase hx, fun e => by subst e; exact (hw.tree_nodup t').not_mem_erase hx⟩
      · rintro ⟨hx, hne⟩; exact (List.mem_erase_of_ne hne).mpr hx
    · rw [upd_other _ _ ht]
      exact ⟨fun hx => ⟨hx, fun e => by subst e; exact tree_ne_of_mem hw hx hl ht rfl⟩, fun h => h.1⟩
  rw [memT, memT]
  by_cases hxl : x = l
  · subst hxl
    simp [Db.levelLive, freeDb]
  · have : (freeDb db t l).levelLive x ↔ db.levelLive x := by
      simp [Db.levelLive, freeDb, upd_other _ _ hxl]
    rw [this, hr x]
    simp [hxl]

def OStep (c : MCtx) (s : S) (L : Loc) (ts : List TradeObs) : Prop :=
  ∃ s' L' ts' inc' contra' strades',
    Eval program (outerBody c.isBuy) (mkSt s c.r L ts) (mkSt s' c.r L' ts', .normal) ∧
    OInv c s' L' ts' inc' contra' strades' ∧ omeasure c s' L' < omeasure c s L

/-- **Outer body.** One outer iteration from a state where the loop condition
    holds: take the best contra level, stop if there is none or it does not
    cross, otherwise run the inner loop on it and free it if it emptied. -/
theorem outer_body {c : MCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade}
    (hc : c.Ok) (hcap : CapOk S) (hC0 : c.C0 ≤ capacity (S := S))
    (hO : OInv c s L ts inc contra strades) (hrem : L.rem ≠ 0) (hstop : L.stop = false) :
    OStep c s L ts := by
  have hw := hO.inv.wf
  have hnd := notDone_of hO.aggr hrem
  have e1 := ev_tBest (P := program) (s := s) (r := c.r) (L := L) (ts := ts) c.t
  have hlaw := tBest_law s c.t hw
  have hmeas : omeasure c s L = ((view s).tree c.t).length + 1 := by
    unfold omeasure; rw [if_pos ⟨hrem, hstop⟩]
  cases hbest : tBest s c.t with
  | none =>
    rw [hbest] at hlaw e1
    have htree : (view s).tree c.t = [] := hlaw
    have hcn : contra = [] := by
      have := hO.cview
      simp only [absSide, htree, List.map_nil, sortLevels] at this
      exact List.map_eq_nil_iff.mp this.symm
    refine ⟨s, { L with best := none, stop := true }, ts, inc, contra, strades, ?_, ?_, ?_⟩
    · exact Eval.block_cons_normal e1 (Eval.ite_true (by rw [ev_bestNull]; rfl) ev_stop) (by simp)
    · refine ⟨hO.inv, hO.own, hO.spec, hO.cview, hO.aggr, hO.shape, hO.trades, hO.tbound, hO.cnt,
        hO.hashid, hO.remle, fun _ => ?_, fun _ _ x hx => ?_⟩
      · rw [hO.spec, hcn]; exact rest_empty hnd
      · rw [htree] at hx; cases hx
    · rw [hmeas]; unfold omeasure; simp
  | some l =>
    rw [hbest] at hlaw e1
    obtain ⟨hl, hlb⟩ := hlaw
    have hll : liveL (view s) l = true := hw.tree_live _ _ hl
    obtain ⟨lrow, hlrow⟩ : ∃ lrow, readLevel s l = some lrow := by
      rw [readLevel_law]; simp only [liveL] at hll; exact Option.isSome_iff_exists.mp hll
    have hlp : (view s).levelPrice l = lrow.price := by
      rw [readLevel_law] at hlrow; simp [Db.levelPrice, hlrow]
    have hsplit := absSide_best hw hl hlb
    have hcv := hO.cview
    rw [hsplit, List.map_cons] at hcv
    obtain ⟨level, RL, hcontra, hlv, hRL⟩ := map_levelView_cons hcv.symm
    have hlpx : level.price = lrow.price.toNat := by
      have := congrArg LevelView.price hlv
      simp only [levelView, absLevel] at this
      rw [this, hlp]
    have ecross := ev_crossCond (s := s) (r := c.r) (ts := ts) (L := { L with best := some l })
      c.isBuy rfl hll hlrow
    by_cases hx : c.r.orderType ≠ 1 ∧ ¬ crossB c.isBuy lrow.price c.r.price
    · -- no crossing: stop
      refine ⟨s, { L with best := some l, stop := true }, ts, inc, contra, strades, ?_, ?_, ?_⟩
      · exact Eval.block_cons_normal e1 (Eval.ite_false (by rw [ev_bestNull]; rfl)
          (Eval.ite_true (by rw [ecross, decide_eq_true hx]) ev_stop)) (by simp)
      · refine ⟨hO.inv, hO.own, hO.spec, hO.cview, hO.aggr, hO.shape, hO.trades, hO.tbound, hO.cnt,
          hO.hashid, hO.remle, fun _ => ?_, fun _ _ => ?_⟩
        · rw [hO.spec, hcontra]
          refine rest_noprice hnd ?_
          rw [canMatch_shape hO.shape, hlpx]
          cases h : canMatchPrice c.o1 lrow.price.toNat
          · rfl
          · rcases (canMatch_iff hc lrow.price).mp h with h1 | h1
            · exact absurd h1 hx.1
            · exact absurd h1 hx.2
        · exact stopX_of_best hlb (by rw [hlp]; exact hx.2)
      · rw [hmeas]; unfold omeasure; simp
    · -- crossing: match against level l
      have hpx : canMatchPrice c.o1 ((view s).levelPrice l).toNat = true := by
        rw [hlp, canMatch_iff hc]
        by_cases hm : c.r.orderType = 1
        · exact Or.inl hm
        · exact Or.inr (Classical.byContradiction fun hn => hx ⟨hm, hn⟩)
      have hc' : (oc c l (view s) RL).Ok := ⟨hc.req, hw, hl, hlb, hRL, hpx⟩
      have hqne : (view s).queue l ≠ [] := hO.inv.client.level_nonempty _ l hl
      have hqf : qFirst s l = ((view s).queue l).head? := qFirst_law s l hw hll
      have e2 := ev_qFirst (P := program) (s := s) (r := c.r) (ts := ts) (L := { L with best := some l })
        rfl hll
      rw [hqf] at e2
      have hII : IInv (oc c l (view s) RL) s { L with best := some l, passive := ((view s).queue l).head? }
          ts inc contra strades :=
        ⟨⟨Inv.toM hO.inv l, Frame.refl l _, fun he => absurd he hqne, fun _ => ⟨level, hcontra, hlv⟩,
          hO.cnt, hO.hashid⟩, rfl, hstop, hO.spec, hO.aggr, hO.shape, fun _ => rfl, hO.trades,
          hO.tbound, hO.remle⟩
      obtain ⟨s', L', ts', inc', contra', strades', eloop, hI', hexit⟩ := inner_loop hc' hcap hC0 hII
      have hS := hI'.sinv
      have hw' := hS.inv.wf
      have hfr : Frame l (view s) (view s') := hS.frame
      have hin' : l ∈ (view s').tree c.t := by rw [hfr.tree]; exact hl
      have hll' : liveL (view s') l = true := hw'.tree_live _ _ hin'
      have hbest' : L'.best = some l := hI'.best
      have hown' : absSide (view s') (ownT c.isBuy) = c.own := by
        rw [hfr.absSide_other (not_mem_other hw hl)]; exact hO.own
      have eall : ∀ {s'' : S}, Eval program (freeStmt c.isBuy) (mkSt s' c.r L' ts') (mkSt s'' c.r L' ts', .normal) →
          Eval program (outerBody c.isBuy) (mkSt s c.r L ts) (mkSt s'' c.r L' ts', .normal) := fun ef =>
        Eval.block_cons_normal e1 (Eval.ite_false (by rw [ev_bestNull]; rfl)
          (Eval.ite_false (by rw [ecross, decide_eq_false hx])
            (Eval.block_cons_normal e2 (Eval.block_cons_normal eloop ef (by simp)) (by simp)))) (by simp)
      have hstop' : L'.stop = false := hI'.stop
      by_cases he' : (view s').queue l = []
      · -- the level emptied: free it
        obtain ⟨efree, hv'', hw'', hcnt'', hlu''⟩ := ev_free c.isBuy (r := c.r) (L := L') (ts := ts') hbest' hw' hin' he'
        have hIM := hS.inv
        refine ⟨_, L', ts', inc', contra', strades', eall efree, ?_, ?_⟩
        · refine ⟨⟨hw'', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hI'.spec, ?_, hI'.aggr, hI'.shape, hI'.trades, ?_, ?_,
            ?_, hI'.remle, (fun h => by simp [hstop'] at h), (fun h => by simp [hstop'] at h)⟩
          · rw [hv'']; exact free_clientInv hw' hIM.client hin' he'
          · intro y; rw [hv'']; exact hIM.orders_resting y
          · rw [hv'']; exact free_levels_resting hw' hin' hIM.levels_resting
          · rw [hcnt'', hv'', free_restingCount hw' hin' he']; exact hIM.count_eq
          · have := free_tree_length (db := view s') (t := contraT c.isBuy) hin'
            have := hIM.levels_eq
            rw [hv'']; omega
          · rw [hcnt'']; exact hIM.count_le
          · rw [hv'', free_absSide_other hw' hin' (ownT_ne c.isBuy)]; exact hown'
          · rw [hv'', free_absSide hw' hin', hfr.restSide_eq hw, hS.empty he']; exact hRL.symm
          · rw [hcnt'']; exact hI'.tbound
          · rw [hcnt'']; exact hS.cnt
          · rw [hv'']; exact hS.hashid
        · rw [hmeas]
          unfold omeasure
          rw [hv'']
          simp only [freeDb, upd_same, hfr.tree]
          have := List.length_erase_of_mem (show l ∈ (view s).tree (contraT c.isBuy) from hl)
          have := List.length_pos_of_mem (show l ∈ (view s).tree (contraT c.isBuy) from hl)
          simp only [MCtx.t] at *
          split <;> omega
      · -- the level still has orders: the incoming order is used up
        have hr0 : L'.rem = 0 := by
          rcases hexit with h | h
          · exact h
          · exact absurd h he'
        have efree := ev_nofree c.isBuy (r := c.r) (L := L') (ts := ts') hbest' hll' he'
          (count_le_cap_lc (hS.inv.toInv he') hin' hcap)
        refine ⟨s', L', ts', inc', contra', strades', eall efree, ?_, ?_⟩
        · refine ⟨hS.inv.toInv he', hown', hI'.spec, ?_, hI'.aggr, hI'.shape, hI'.trades, hI'.tbound,
            hS.cnt, hS.hashid, hI'.remle, (fun h => by simp [hstop'] at h),
            (fun h => by simp [hstop'] at h)⟩
          have hb' : ∀ x ∈ (view s').tree c.t, better c.t ((view s').levelPrice l) ((view s').levelPrice x) := by
            intro x hx
            rw [hfr.levelPrice_eq, hfr.levelPrice_eq]
            exact hlb x (by rw [← hfr.tree]; exact hx)
          obtain ⟨level', hc'', hlv'⟩ := hS.head he'
          rw [absSide_best hw' hin' hb', hc'', List.map_cons, List.map_cons, hlv']
          simp only [oc]
          rw [hfr.restSide_eq hw, ← hRL]
        · rw [hmeas]; unfold omeasure; rw [hfr.tree]; simp [hr0]

-- ============================================================================
-- (d) The outer loop
-- ============================================================================

theorem pos_of_ne {x : UInt64} (h : x ≠ 0) : 0 < x := by
  rw [UInt64.lt_iff_toNat_lt]
  have : x.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by rw [e]; rfl))
  simp; omega

theorem outer_run {c : MCtx} (hc : c.Ok) (hcap : CapOk S) (hC0 : c.C0 ≤ capacity (S := S)) :
    ∀ (μ : Nat) (s : S) (L : Loc) (ts : List TradeObs) (inc : Order) (contra : List PriceLevel)
      (strades : List Trade), OInv c s L ts inc contra strades → omeasure c s L ≤ μ →
      ∃ s' L' ts' inc' contra' strades',
        LoopRun program outerCond (outerBody c.isBuy) μ (mkSt s c.r L ts) (mkSt s' c.r L' ts', .normal) ∧
        OInv c s' L' ts' inc' contra' strades' ∧ (L'.rem = 0 ∨ L'.stop = true) := by
  intro μ
  induction μ with
  | zero =>
    intro s L ts inc contra strades hO hμ
    have hx : L.rem = 0 ∨ L.stop = true := by
      unfold omeasure at hμ
      by_cases h : L.rem ≠ 0 ∧ L.stop = false
      · rw [if_pos h] at hμ; omega
      · by_cases hr : L.rem = 0
        · exact Or.inl hr
        · exact Or.inr (by cases hs : L.stop; exact absurd ⟨hr, hs⟩ h; rfl)
    refine ⟨s, L, ts, inc, contra, strades, .stop ?_, hO, hx⟩
    rw [ev_outerCond]
    rcases hx with h | h <;> simp [h]
  | succ μ ih =>
    intro s L ts inc contra strades hO hμ
    by_cases hx : L.rem = 0 ∨ L.stop = true
    · refine ⟨s, L, ts, inc, contra, strades, .stop ?_, hO, hx⟩
      rw [ev_outerCond]
      rcases hx with h | h <;> simp [h]
    · have hr : L.rem ≠ 0 := fun h => hx (Or.inl h)
      have hs : L.stop = false := by cases h : L.stop; rfl; exact absurd (Or.inr h) hx
      obtain ⟨s1, L1, ts1, inc1, contra1, strades1, hev, hO1, hlt⟩ := outer_body hc hcap hC0 hO hr hs
      obtain ⟨s', L', ts', inc', contra', strades', hrun, hO', hexit⟩ :=
        ih s1 L1 ts1 inc1 contra1 strades1 hO1 (by omega)
      refine ⟨s', L', ts', inc', contra', strades', .step ?_ hev hrun, hO', hexit⟩
      rw [ev_outerCond]; simp [pos_of_ne hr, hs]

/-- **Outer loop.** From `OInv`, the outer loop runs to completion within its
    bound `capacity + 1`, and at its exit the spec's matching run has ended:
    `mr` is the terminal result of the current state. -/
theorem outer_loop {c : MCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade}
    (hc : c.Ok) (hcap : CapOk S) (hC0 : c.C0 ≤ capacity (S := S))
    (hO : OInv c s L ts inc contra strades) :
    ∃ s' L' ts' inc' contra' strades',
      Eval program (outerLoop c.isBuy) (mkSt s c.r L ts) (mkSt s' c.r L' ts', .normal) ∧
      OInv c s' L' ts' inc' contra' strades' ∧ (L'.rem = 0 ∨ L'.stop = true) ∧
      c.mr = term inc' c.own contra' strades' c.tm := by
  have hle : omeasure c s L ≤ capacity (S := S) + 1 := by
    unfold omeasure
    have h1 := levels_le_count hO.inv.client
    have h2 := hO.inv.count_eq
    have h3 := hO.inv.count_le
    have h4 : ((view s).tree c.t).length ≤ ((view s).tree .bids ++ (view s).tree .asks).length := by
      rw [List.length_append]; cases hb : c.isBuy <;> simp [MCtx.t, contraT, hb]
    split <;> omega
  obtain ⟨s', L', ts', inc', contra', strades', hrun, hO', hexit⟩ :=
    outer_run hc hcap hC0 (omeasure c s L) s L ts inc contra strades hO (Nat.le_refl _)
  refine ⟨s', L', ts', inc', contra', strades', Eval.loop (boundVal_capPlus1 hcap) (hrun.mono hle),
    hO', hexit, ?_⟩
  rcases hexit with h | h
  · rw [hO'.spec]; exact rest_done (done_of hO'.aggr h)
  · exact hO'.stopT h

end MatcherOuter

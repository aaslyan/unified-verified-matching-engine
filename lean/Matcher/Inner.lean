import Matcher.LoopEnv
import Matcher.SpecStep

/-!
# Phase 4: the inner matching loop

The inner loop of `sideFun` matches the incoming order against the orders of
one level `l`, the best level of the contra tree when the outer iteration
began. `IInv` is its invariant (LOOP-INVARIANT.md): the store satisfies
`InvM s l` (level `l` may have emptied), everything outside level `l` is as
at the start of the outer iteration (`Frame`), and the spec's remaining
computation `rest inc own contra strades` is the whole spec run `mr`, where
`contra` is the store's contra side as seen through `levelView`.

`inner_body` shows one iteration is one `doMatch` step (one lemma per branch:
the four STP modes, full and partial fill); `inner_loop` folds it with the
bound `capacity + 1`.
-/

namespace MatcherInner

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore MatcherLoop MatcherSpec

-- ============================================================================
-- The spec order and the request
-- ============================================================================

/-- `inc` is the spec order `o1` with only its remaining quantity and status
    changed: the only fields `doMatch` changes. -/
def IncShape (o1 inc : Order) : Prop :=
  inc = { o1 with remainingQty := inc.remainingQty, status := inc.status }

theorem IncShape.refl (o1 : Order) : IncShape o1 o1 := rfl

theorem IncShape.side {o1 inc : Order} (h : IncShape o1 inc) : inc.side = o1.side := by rw [h]
theorem IncShape.price {o1 inc : Order} (h : IncShape o1 inc) : inc.price = o1.price := by rw [h]
theorem IncShape.id {o1 inc : Order} (h : IncShape o1 inc) : inc.id = o1.id := by rw [h]
theorem IncShape.group {o1 inc : Order} (h : IncShape o1 inc) : inc.stpGroup = o1.stpGroup := by rw [h]
theorem IncShape.policy {o1 inc : Order} (h : IncShape o1 inc) : inc.stpPolicy = o1.stpPolicy := by rw [h]

theorem IncShape.upd {o1 inc : Order} (h : IncShape o1 inc) (a : Nat) (st : OrderStatus) :
    IncShape o1 { inc with remainingQty := a, status := st } := by
  rw [h]; rfl

theorem IncShape.updRem {o1 inc : Order} (h : IncShape o1 inc) (a : Nat) :
    IncShape o1 { inc with remainingQty := a } := by
  rw [h]; rfl

theorem IncShape.updSt {o1 inc : Order} (h : IncShape o1 inc) (st : OrderStatus) :
    IncShape o1 { inc with status := st } := by
  rw [h]; rfl

theorem canMatch_shape {o1 inc : Order} (h : IncShape o1 inc) (p : Nat) :
    canMatchPrice inc p = canMatchPrice o1 p := by
  unfold canMatchPrice; rw [h.price, h.side]

/-- What the matching loop needs to know about the spec order of a request. -/
structure ReqOk (r : CRequest) (o1 : Order) : Prop where
  id : o1.id = r.id.toNat
  group : o1.stpGroup = stpGroupOf r.account
  policy : o1.stpPolicy = stpPolicyOf r.account r.stpMode
  stp : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4

-- ============================================================================
-- The head order, store side and spec side
-- ============================================================================

theorem head_decomp {level : PriceLevel} {P : Nat} {F : OrderH → OrderView} {h : OrderH}
    {qs : List OrderH} (hv : levelView level = { price := P, orders := (h :: qs).map F }) :
    ∃ resting restOrders, level.orders = resting :: restOrders ∧ orderView resting = F h ∧
      restOrders.map orderView = qs.map F ∧ level.price = P := by
  simp only [levelView, LevelView.mk.injEq, List.map_cons] at hv
  obtain ⟨hp, ho⟩ := hv
  cases hq : level.orders with
  | nil => rw [hq] at ho; simp at ho
  | cons x xs =>
    rw [hq] at ho
    simp only [List.map_cons, List.cons.injEq] at ho
    exact ⟨x, xs, rfl, ho.1, ho.2, hp⟩

/-- The fields of a spec order whose view is a resting row's. -/
structure RowView (t : Tree) (row : OrderRow) (o : Order) : Prop where
  id : o.id = row.id.toNat
  rem : o.remainingQty = row.remaining.toNat
  vis : o.visibleQty = row.remaining.toNat
  disp : o.displayQty = none
  group : o.stpGroup = stpGroupOf row.account

theorem rowView_of {t : Tree} {row : OrderRow} {o : Order}
    (h : orderView o = orderView (restingOrder t row 0)) : RowView t row o := by
  simp only [orderView, restingOrder, OrderView.mk.injEq] at h
  exact ⟨h.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem view_update {t : Tree} {row : OrderRow} {o : Order}
    (h : orderView o = orderView (restingOrder t row 0)) (p : UInt64) (a b : Nat)
    (ha : a = p.toNat) (hb : b = p.toNat) :
    orderView { o with remainingQty := a, visibleQty := b } =
      orderView (restingOrder t { row with remaining := p } 0) := by
  simp only [orderView, restingOrder, OrderView.mk.injEq] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _, h9, h10, _, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, ha, h9, h10, hb, h12, h13⟩

theorem view_update_st {t : Tree} {row : OrderRow} {o : Order}
    (h : orderView o = orderView (restingOrder t row 0)) (p : UInt64) (a b : Nat)
    (ha : a = p.toNat) (hb : b = p.toNat) (st : OrderStatus) :
    orderView { o with remainingQty := a, visibleQty := b, status := st } =
      orderView (restingOrder t { row with remaining := p } 0) :=
  view_update h p a b ha hb

theorem stpGroupOf_eq {a b : UInt64} : stpGroupOf a = stpGroupOf b → a ≠ 0 → a = b := by
  intro h ha
  unfold stpGroupOf at h
  by_cases hb : b = 0
  · simp [ha, hb] at h
  · simp [ha, hb] at h; exact UInt64.toNat_inj.mp h

/-- The spec's self-trade test is the matcher's. -/
theorem conflict_iff {r : CRequest} {o1 inc resting : Order} {t : Tree} {row : OrderRow}
    (hr : ReqOk r o1) (hs : IncShape o1 inc) (hv : RowView t row resting) :
    selfTradeConflict inc resting =
      decide (r.account ≠ 0 ∧ r.account = row.account ∧ r.stpMode ≠ 0) := by
  unfold selfTradeConflict
  rw [hs.policy, hs.group, hr.policy, hr.group, hv.group]
  by_cases ha : r.account = 0
  · simp [stpPolicyOf, ha]
  · have hp : (stpPolicyOf r.account r.stpMode).isSome = decide (r.stpMode ≠ 0) := by
      unfold stpPolicyOf
      rw [if_neg ha]
      rcases hr.stp with h | h | h | h | h <;> rw [h] <;> rfl
    rw [hp]
    by_cases hrow : row.account = 0
    · have : r.account ≠ row.account := fun e => ha (e.trans hrow)
      simp [stpGroupOf, ha, hrow, this]
    · simp only [stpGroupOf, ha, hrow, if_false]
      by_cases e : r.account = row.account
      · simp [e, hrow]
      · have : r.account.toNat ≠ row.account.toNat := fun h => e (UInt64.toNat_inj.mp h)
        simp [e, this]

theorem policy_of {r : CRequest} {o1 inc : Order} (hr : ReqOk r o1) (hs : IncShape o1 inc)
    (ha : r.account ≠ 0) :
    (r.stpMode = 1 → inc.stpPolicy.getD .cancelNewest = .cancelNewest) ∧
    (r.stpMode = 2 → inc.stpPolicy.getD .cancelNewest = .cancelOldest) ∧
    (r.stpMode = 3 → inc.stpPolicy.getD .cancelNewest = .cancelBoth) ∧
    (r.stpMode = 4 → inc.stpPolicy.getD .cancelNewest = .decrement) := by
  rw [hs.policy, hr.policy]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp [stpPolicyOf, ha, h, decodeStpMode, CStpMode.policy]

-- ============================================================================
-- The invariant
-- ============================================================================

variable {S : Type} [EngineDb S]

open EngineDb

/-- The data fixed during one outer iteration. -/
structure OCtx where
  r : CRequest
  isBuy : Bool
  o1 : Order
  own : List PriceLevel
  tm : Timestamp
  mr : MatchResult
  C0 : Nat
  l : LevelH
  dbR : Db
  RL : List PriceLevel

abbrev OCtx.t (c : OCtx) : Tree := contraT c.isBuy

/-- What holds of the fixed data: `l` was the best level of the contra tree at
    the start of the iteration, `RL` is the spec's view of the other levels,
    and the level's price crosses the order's. -/
structure OCtx.Ok (c : OCtx) : Prop where
  req : ReqOk c.r c.o1
  wf : c.dbR.WF
  mem : c.l ∈ c.dbR.tree c.t
  best : ∀ l' ∈ c.dbR.tree c.t, better c.t (c.dbR.levelPrice c.l) (c.dbR.levelPrice l')
  rl : c.RL.map levelView = (restSide c.dbR c.t c.l).map levelView
  px : canMatchPrice c.o1 (c.dbR.levelPrice c.l).toNat = true

/-- The store part of the inner invariant. -/
structure SInv (c : OCtx) (s : S) (contra : List PriceLevel) : Prop where
  inv : InvM s c.l
  frame : Frame c.l c.dbR (view s)
  empty : (view s).queue c.l = [] → contra = c.RL
  head : (view s).queue c.l ≠ [] → ∃ level, contra = level :: c.RL ∧
    levelView level = levelView (absLevel (view s) c.t c.l)
  cnt : count s ≤ c.C0
  hashid : ∀ h ∈ (view s).hash, (view s).orderId h ≠ c.r.id

/-- **The inner-loop invariant.** -/
structure IInv (c : OCtx) (s : S) (L : Loc) (ts : List TradeObs) (inc : Order)
    (contra : List PriceLevel) (strades : List Trade) : Prop where
  sinv : SInv c s contra
  best : L.best = some c.l
  stop : L.stop = false
  spec : c.mr = rest inc c.own contra strades c.tm
  aggr : L.rem.toNat = if inc.status = .cancelled then 0 else inc.remainingQty
  shape : IncShape c.o1 inc
  passive : L.rem ≠ 0 → L.passive = ((view s).queue c.l).head?
  trades : ts = strades.map tradeObs
  tbound : ts.length + count s ≤ c.C0 + (if L.rem = 0 then 1 else 0)
  remle : L.rem ≤ c.r.qty

/-- The inner loop's measure. -/
def imeasure (c : OCtx) (s : S) (L : Loc) : Nat :=
  ((view s).queue c.l).length + (if L.rem = 0 then 0 else 1)

theorem SInv.mem {c : OCtx} {s : S} {contra : List PriceLevel} (hs : SInv c s contra)
    (hc : c.Ok) : c.l ∈ (view s).tree c.t := by
  rw [hs.frame.tree]; exact hc.mem

theorem SInv.liveL {c : OCtx} {s : S} {contra : List PriceLevel} (hs : SInv c s contra)
    (hc : c.Ok) : liveL (view s) c.l = true :=
  (hs.inv.wf.tree_live _ _ (hs.mem hc))

theorem ordV_congr {db db' : Db} {t : Tree} {y : OrderH} (h : db'.orders y = db.orders y) :
    ordV db' t y = ordV db t y := by
  simp only [ordV, rowOf, h]

-- ============================================================================
-- The store steps
-- ============================================================================

theorem sinv_drop {c : OCtx} {s s' : S} {contra : List PriceLevel} {h : OrderH}
    {qs : List OrderH} {level : PriceLevel} {resting : Order} {restOrders : List Order}
    (hc : c.Ok) (hs : SInv c s contra) (hq : (view s).queue c.l = h :: qs)
    (hcontra : contra = level :: c.RL) (hlv : level.orders = resting :: restOrders)
    (hro : restOrders.map orderView = qs.map (ordV (view s) c.t))
    (hpx : level.price = ((view s).levelPrice c.l).toNat)
    (hv' : view s' = dropDb (view s) c.l h) (hw' : (view s').WF) (hcount : count s' + 1 = count s)
    (hlu : levelsUsed s' = levelsUsed s) :
    SInv c s' (drop1 level restOrders c.RL) ∧ (view s').queue c.l = qs := by
  have hw := hs.inv.wf
  have hh : h ∈ (view s).queue c.l := by rw [hq]; exact List.mem_cons_self
  have hl := hs.mem hc
  have hnd : (h :: qs).Nodup := hq ▸ hw.queue_nodup c.l
  have hq' : (view s').queue c.l = qs := by
    rw [hv']; simp only [dropDb, upd_same, hq, List.erase_cons_head]
  have hqs : ∀ y ∈ qs, (view s').orders y = (view s).orders y := by
    intro y hy
    have : y ≠ h := fun e => by subst e; exact (List.nodup_cons.mp hnd).1 hy
    rw [hv']; simp only [dropDb, upd_other _ _ this]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hq'⟩
  · refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv']; exact drop_clientInvM hw hs.inv.client hh
    · rw [hv']; exact drop_orders_resting hw hh hs.inv.orders_resting
    · rw [hv']; exact hs.inv.levels_resting
    · rw [hv']
      have := drop_restingCount hw hl hh
      have := hs.inv.count_eq
      omega
    · rw [hlu, hv']; exact hs.inv.levels_eq
    · have := hs.inv.count_le; omega
  · rw [hv']; exact hs.frame.trans (frame_drop hw hh)
  · intro he
    rw [hq'] at he; subst he
    have : restOrders = [] := by simpa using hro
    simp [drop1, this]
  · intro hne
    rw [hq'] at hne
    have hro0 : restOrders ≠ [] := by
      intro e; rw [e] at hro; simp at hro; exact hne hro
    refine ⟨{ price := level.price, orders := restOrders }, by simp [drop1, hro0], ?_⟩
    rw [levelView_absLevel, hq']
    simp only [levelView, LevelView.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hpx, hv']; rfl
    · rw [hro]; exact List.map_congr_left (fun y hy => (ordV_congr (hqs y hy)).symm)
  · have := hs.cnt; omega
  · intro y hy
    rw [hv'] at hy ⊢
    have hy' : y ∈ (view s).hash := List.mem_of_mem_erase hy
    have hne : y ≠ h := fun e => by subst e; exact hw.hash_nodup.not_mem_erase hy
    have := hs.hashid y hy'
    simpa [Db.orderId, dropDb, upd_other _ _ hne] using this

theorem sinv_setRem {c : OCtx} {s s' : S} {contra : List PriceLevel} {h : OrderH}
    {qs : List OrderH} {level : PriceLevel} {resting' : Order} {restOrders : List Order}
    {row : OrderRow} {p : UInt64}
    (hc : c.Ok) (hs : SInv c s contra) (hq : (view s).queue c.l = h :: qs)
    (hcontra : contra = level :: c.RL) (hro : restOrders.map orderView = qs.map (ordV (view s) c.t))
    (hpx : level.price = ((view s).levelPrice c.l).toNat)
    (hrow : (view s).orders h = some row) (hp0 : 0 < p) (hp : p ≤ row.remaining)
    (hr' : orderView resting' = orderView (restingOrder c.t { row with remaining := p } 0))
    (hv' : view s' = setRemDb (view s) h { row with remaining := p }) (hw' : (view s').WF)
    (hcount : count s' = count s) (hlu : levelsUsed s' = levelsUsed s) :
    SInv c s' ({ price := level.price, orders := resting' :: restOrders } :: c.RL) ∧
      (view s').queue c.l = h :: qs := by
  have hw := hs.inv.wf
  have hh : h ∈ (view s).queue c.l := by rw [hq]; exact List.mem_cons_self
  have hl := hs.mem hc
  have hnd : (h :: qs).Nodup := hq ▸ hw.queue_nodup c.l
  have hq' : (view s').queue c.l = h :: qs := by rw [hv']; exact hq
  have hqs : ∀ y ∈ qs, (view s').orders y = (view s).orders y := by
    intro y hy
    have : y ≠ h := fun e => by subst e; exact (List.nodup_cons.mp hnd).1 hy
    rw [hv']; simp only [setRemDb, upd_other _ _ this]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hq'⟩
  · refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv']; exact setRem_clientInvM hs.inv.client hh hl hrow hp0 hp
    · intro y
      rw [hv']
      have := hs.inv.orders_resting y
      by_cases hy : y = h
      · subst hy
        have hq1 : (view s).queued y := ⟨_, hh⟩
        constructor
        · intro _; exact hq1
        · intro _; simp [Db.orderLive, setRemDb]
      · simpa [Db.orderLive, setRemDb, upd_other _ _ hy, Db.queued] using this
    · rw [hv']; exact hs.inv.levels_resting
    · rw [hcount, hv']; exact hs.inv.count_eq
    · rw [hlu, hv']; exact hs.inv.levels_eq
    · rw [hcount]; exact hs.inv.count_le
  · rw [hv']; exact hs.frame.trans (frame_setRem hw hh)
  · intro he; rw [hq'] at he; cases he
  · intro _
    refine ⟨_, rfl, ?_⟩
    rw [levelView_absLevel, hq']
    simp only [levelView, LevelView.mk.injEq, List.map_cons, List.cons.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [hpx, hv']; rfl
    · rw [hr']; simp [ordV, rowOf, hv', setRemDb]
    · rw [hro]; exact List.map_congr_left (fun y hy => (ordV_congr (hqs y hy)).symm)
  · rw [hcount]; exact hs.cnt
  · intro y hy
    rw [hv'] at hy ⊢
    have := hs.hashid y hy
    by_cases hyh : y = h
    · subst hyh; simpa [Db.orderId, setRemDb, hrow] using this
    · simpa [Db.orderId, setRemDb, upd_other _ _ hyh] using this

-- ============================================================================
-- The head order under the invariant
-- ============================================================================

theorem nextIn_head (h : Nat) (qs : List Nat) : nextIn (h :: qs) h = qs.head? := by
  cases qs <;> simp [nextIn]

theorem qNext_head {s : S} {l : LevelH} {h : OrderH} {qs : List OrderH} (hw : (view s).WF)
    (hq : (view s).queue l = h :: qs) : qNext s h = qs.head? := by
  have hh : h ∈ (view s).queue l := by rw [hq]; exact List.mem_cons_self
  obtain ⟨l', hl', e⟩ := qNext_law s h hw ⟨l, hh⟩
  have := hw.queue_unique _ _ _ hl' hh
  subst this
  rw [e, hq, nextIn_head]

/-- Everything the inner body needs about the head order `h` of level `l`. -/
structure HeadFacts (c : OCtx) (s : S) (L : Loc) (inc : Order) (contra : List PriceLevel)
    (h : OrderH) (qs : List OrderH) (row : OrderRow) (level : PriceLevel) (resting : Order)
    (restOrders : List Order) : Prop where
  hq : (view s).queue c.l = h :: qs
  hcontra : contra = level :: c.RL
  hlv : level.orders = resting :: restOrders
  hro : restOrders.map orderView = qs.map (ordV (view s) c.t)
  hpx : level.price = ((view s).levelPrice c.l).toNat
  hrow : (view s).orders h = some row
  hread : readOrder s h = some row
  hrpos : 0 < row.remaining
  hrle : row.remaining ≤ row.qty
  hrv : orderView resting = orderView (restingOrder c.t row 0)
  rv : RowView c.t row resting
  ah : AtHead inc level resting restOrders
  incRem : inc.remainingQty = L.rem.toNat
  notc : inc.status ≠ .cancelled
  hp : L.passive = some h
  hlo : liveO (view s) h = true
  hll : liveL (view s) c.l = true
  hhash : h ∈ (view s).hash
  hqd : queuedB (view s) h = true
  hh : h ∈ (view s).queue c.l

theorem head_facts {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH}
    (hc : c.Ok) (hI : IInv c s L ts inc contra strades) (hrem : L.rem ≠ 0)
    (hq : (view s).queue c.l = h :: qs) :
    ∃ row level resting restOrders, HeadFacts c s L inc contra h qs row level resting restOrders := by
  have hs := hI.sinv
  have hw := hs.inv.wf
  have hl := hs.mem hc
  have hh : h ∈ (view s).queue c.l := by rw [hq]; exact List.mem_cons_self
  obtain ⟨level, hcontra, hlvv⟩ := hs.head (by rw [hq]; simp)
  rw [levelView_absLevel, hq] at hlvv
  obtain ⟨resting, restOrders, hlv, hrv0, hro, hpx⟩ := head_decomp hlvv
  obtain ⟨row, hrow, -, hrp, hrpos, hrle, -⟩ := hs.inv.client.order_ok c.t c.l hl h hh
  have hrv : orderView resting = orderView (restingOrder c.t row 0) := by
    rw [hrv0]; simp [ordV, rowOf, hrow]
  have rv := rowView_of hrv
  have hagg := hI.aggr
  have hnc : inc.status ≠ .cancelled := by
    intro e; rw [if_pos e] at hagg
    exact hrem (UInt64.toNat_inj.mp (by rw [hagg]; rfl))
  rw [if_neg hnc] at hagg
  have hlp : level.price = (c.dbR.levelPrice c.l).toNat := by
    rw [hpx, hs.frame.levelPrice_eq]
  have hrposN : row.remaining.toNat ≠ 0 := by
    have := UInt64.lt_iff_toNat_lt.mp hrpos; simp at this; omega
  refine ⟨row, level, resting, restOrders, ⟨hq, hcontra, hlv, hro, hpx, hrow,
    by rw [readOrder_law]; exact hrow, hrpos, hrle, hrv, rv, ⟨?_, ?_, hlv, ?_, rv.disp⟩, hagg.symm,
    hnc, ?_, (hw.queue_live _ _ hh).1, hs.liveL hc, (hs.inv.client.hash_iff_queued h).mpr ⟨_, hh⟩,
    ?_, hh⟩⟩
  · have h1 : inc.remainingQty ≠ 0 := by
      rw [← hagg]; intro e; exact hrem (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have h2 : (inc.status == OrderStatus.cancelled) = false := by
      cases hst : inc.status <;> first | rfl | exact absurd hst hnc
    simp [h1, h2]
  · rw [canMatch_shape hI.shape, hlp]; exact hc.px
  · rw [rv.vis]; exact hrposN
  · rw [hI.passive hrem, hq]; rfl
  · unfold queuedB
    rw [List.any_eq_true]
    exact ⟨c.l, (hs.inv.wf.levels_live _).mp (hw.tree_live _ _ hl), by simp [hh]⟩

-- ============================================================================
-- One inner iteration per branch
-- ============================================================================

/-- The conclusion of one inner iteration: a run of the body to a state that
    satisfies the invariant again, with a smaller measure. -/
def IStep (c : OCtx) (s : S) (L : Loc) (ts : List TradeObs) : Prop :=
  ∃ s' L' ts' inc' contra' strades', Eval program innerBody (mkSt s c.r L ts) (mkSt s' c.r L' ts', .normal) ∧
    IInv c s' L' ts' inc' contra' strades' ∧ imeasure c s' L' < imeasure c s L

theorem conflict_of {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH} {row : OrderRow}
    {level : PriceLevel} {resting : Order} {restOrders : List Order}
    (hc : c.Ok) (hI : IInv c s L ts inc contra strades)
    (hf : HeadFacts c s L inc contra h qs row level resting restOrders) :
    selfTradeConflict inc resting =
      decide (c.r.account ≠ 0 ∧ c.r.account = row.account ∧ c.r.stpMode ≠ 0) :=
  conflict_iff hc.req hI.shape hf.rv

theorem inner_cancelNew {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH} {row : OrderRow}
    {level : PriceLevel} {resting : Order} {restOrders : List Order}
    (hc : c.Ok) (hI : IInv c s L ts inc contra strades) (hrem : L.rem ≠ 0)
    (hf : HeadFacts c s L inc contra h qs row level resting restOrders)
    (hconf : c.r.account ≠ 0 ∧ c.r.account = row.account ∧ c.r.stpMode ≠ 0) (h1 : c.r.stpMode = 1) :
    IStep c s L ts := by
  have hcf : selfTradeConflict inc resting = true := by rw [conflict_of hc hI hf, decide_eq_true hconf]
  have hpol := (policy_of hc.req hI.shape hconf.1).1 h1
  refine ⟨s, { L with rem := 0 }, ts, { inc with status := .cancelled }, contra, strades, ?_, ?_, ?_⟩
  · exact Eval.ite_true (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_true hconf])
      (Eval.ite_true (by rw [ev_stp_eq]; simp only [STP_CANCEL_NEW]; rw [decide_eq_true h1]) ev_rem0)
  · refine ⟨hI.sinv, hI.best, hI.stop, ?_, ?_, hI.shape.updSt _, ?_, hI.trades, ?_, ?_⟩
    · rw [hI.spec, hf.hcontra]
      exact rest_step_done (step_cancelNew hf.ah hcf hpol) (done_of_cancelled rfl)
    · simp
    · intro e; exact absurd rfl e
    · have := hI.tbound; rw [if_neg hrem] at this; simp; omega
    · exact UInt64.zero_le
  · unfold imeasure; simp [hrem]

theorem inner_cancelOld {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH} {row : OrderRow}
    {level : PriceLevel} {resting : Order} {restOrders : List Order}
    (hc : c.Ok) (hI : IInv c s L ts inc contra strades) (hrem : L.rem ≠ 0)
    (hf : HeadFacts c s L inc contra h qs row level resting restOrders)
    (hconf : c.r.account ≠ 0 ∧ c.r.account = row.account ∧ c.r.stpMode ≠ 0)
    (h23 : c.r.stpMode = 2 ∨ c.r.stpMode = 3) :
    IStep c s L ts := by
  have hw := hI.sinv.inv.wf
  have hcf : selfTradeConflict inc resting = true := by rw [conflict_of hc hI hf, decide_eq_true hconf]
  have h1 : c.r.stpMode ≠ 1 := by rcases h23 with e | e <;> rw [e] <;> decide
  obtain ⟨hv', hw', hcnt, hlu, -⟩ := dropS_facts hw hf.hh hf.hhash
  obtain ⟨hs', hq'⟩ := sinv_drop hc hI.sinv hf.hq hf.hcontra hf.hlv hf.hro hf.hpx hv' hw' hcnt hlu
  have hnext := qNext_head hw hf.hq
  -- the program
  let L1 : Loc := { L with victim := some h }
  let L2 : Loc := { L1 with passive := qs.head? }
  let Lf : Loc := if c.r.stpMode = 3 then { L2 with rem := 0 } else L2
  have eblock : Eval program cancelOldBlock (mkSt s c.r L ts) (mkSt (dropS s c.l h) c.r Lf ts, .normal) := by
    have e1 : Eval program (.assign "victim" (v "passive")) (mkSt s c.r L ts) (mkSt s c.r L1 ts, .normal) :=
      ev_victim hf.hp
    have e2 : Eval program (call1 "passive" .qNext [v "passive"]) (mkSt s c.r L1 ts)
        (mkSt s c.r L2 ts, .normal) := by
      have := ev_qNextP (P := program) (s := s) (r := c.r) (L := L1) (ts := ts) hf.hp hf.hlo hf.hqd
      rw [hnext] at this; exact this
    have e3 : Eval program (removeResting "best" "victim") (mkSt s c.r L2 ts)
        (mkSt (dropS s c.l h) c.r L2 ts, .normal) :=
      ev_remove hI.best (fun _ => by simp only [L2, L1]; lsimp) hw hf.hh hf.hhash hf.hll
    have e4 : Eval program (whenS (eqc "stp" STP_CANCEL_BOTH) (.assign "rem" (u 0)))
        (mkSt (dropS s c.l h) c.r L2 ts) (mkSt (dropS s c.l h) c.r Lf ts, .normal) := by
      by_cases h3 : c.r.stpMode = 3
      · simp only [Lf, if_pos h3]
        exact Eval.when_true (by rw [ev_stp_eq]; simp [h3, STP_CANCEL_BOTH]) ev_rem0
      · simp only [Lf, if_neg h3]
        exact Eval.when_false (by rw [ev_stp_eq]; simp [h3, STP_CANCEL_BOTH])
    exact Eval.block_cons_normal e1 (Eval.block_cons_normal e2 (Eval.block_cons_normal e3 e4
      (by simp)) (by simp)) (by simp)
  have eall : Eval program innerBody (mkSt s c.r L ts) (mkSt (dropS s c.l h) c.r Lf ts, .normal) :=
    Eval.ite_true (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_true hconf])
      (Eval.ite_false (by rw [ev_stp_eq]; simp [h1, STP_CANCEL_NEW])
        (Eval.ite_true (by rw [ev_oldBoth]; simp [h23]) eblock))
  have htb := hI.tbound
  rw [if_neg hrem] at htb
  rcases h23 with h2 | h3
  · -- CANCEL_OLD: drop the resting order, keep matching
    have h3 : c.r.stpMode ≠ 3 := by rw [h2]; decide
    have hpol := (policy_of hc.req hI.shape hconf.1).2.1 h2
    have hLf : Lf = L2 := by simp only [Lf, if_neg h3]
    refine ⟨dropS s c.l h, Lf, ts, inc, drop1 level restOrders c.RL, strades, eall, ?_, ?_⟩
    · rw [hLf]
      refine ⟨hs', hI.best, hI.stop, ?_, hI.aggr, hI.shape, ?_, hI.trades, ?_, hI.remle⟩
      · rw [hI.spec, hf.hcontra]
        exact rest_step (step_cancelOld hf.ah hcf hpol) (mm_drop1 hf.hlv _ _)
      · intro _; show qs.head? = _; rw [hq']
      · show ts.length + count (dropS s c.l h) ≤ c.C0 + (if L.rem = 0 then 1 else 0)
        rw [if_neg hrem]; omega
    · rw [hLf]; unfold imeasure; rw [hq', hf.hq]
      show qs.length + (if L.rem = 0 then 0 else 1) < (h :: qs).length + (if L.rem = 0 then 0 else 1)
      simp
  · -- CANCEL_BOTH: drop the resting order and cancel the incoming one
    have hpol := (policy_of hc.req hI.shape hconf.1).2.2.1 h3
    have hLf : Lf = { L2 with rem := 0 } := by simp only [Lf, if_pos h3]
    refine ⟨dropS s c.l h, Lf, ts, { inc with status := .cancelled }, drop1 level restOrders c.RL,
      strades, eall, ?_, ?_⟩
    · rw [hLf]
      refine ⟨hs', hI.best, hI.stop, ?_, by simp, hI.shape.updSt _, ?_, hI.trades, ?_,
        UInt64.zero_le⟩
      · rw [hI.spec, hf.hcontra]
        exact rest_step_done (step_cancelBoth hf.ah hcf hpol) (done_of_cancelled rfl)
      · intro e; exact absurd rfl e
      · show ts.length + count (dropS s c.l h) ≤ c.C0 + (if (0 : UInt64) = 0 then 1 else 0)
        simp; omega
    · rw [hLf]; unfold imeasure; rw [hq', hf.hq]
      show qs.length + (if (0 : UInt64) = 0 then 0 else 1) < (h :: qs).length + (if L.rem = 0 then 0 else 1)
      simp only [if_true, List.length_cons]; omega

-- ============================================================================
-- Decrement and fill: the shared first half
-- ============================================================================

theorem dropDb_setRem (db : Db) (l : LevelH) (h : OrderH) (row : OrderRow) :
    dropDb (setRemDb db h row) l h = dropDb db l h := by
  simp only [dropDb, setRemDb]
  congr 1
  funext x
  by_cases hx : x = h
  · subst hx; simp
  · simp [upd_other _ _ hx]

/-- The quantities and stores after `fill := min(rem, prem)`, `rem -= fill`,
    `prem := remaining - fill`, and the write of `prem`. -/
structure Core (c : OCtx) (s : S) (L : Loc) (inc : Order) (h : OrderH) (qs : List OrderH)
    (row : OrderRow) (resting : Order) : Prop where
  fle : umin L.rem row.remaining ≤ L.rem
  fler : umin L.rem row.remaining ≤ row.remaining
  fq : (umin L.rem row.remaining).toNat = min inc.remainingQty resting.visibleQty
  qpos : 0 < min inc.remainingQty resting.visibleQty
  remq : (L.rem - umin L.rem row.remaining).toNat = inc.remainingQty - min inc.remainingQty resting.visibleQty
  premq : (row.remaining - umin L.rem row.remaining).toNat =
    resting.remainingQty - min inc.remainingQty resting.visibleQty
  part : row.remaining - umin L.rem row.remaining ≠ 0 → L.rem - umin L.rem row.remaining = 0
  prle : row.remaining - umin L.rem row.remaining ≤ row.remaining
  remle : L.rem - umin L.rem row.remaining ≤ L.rem
  v1 : view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) =
    setRemDb (view s) h { row with remaining := row.remaining - umin L.rem row.remaining }
  w1 : (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).WF
  lo1 : liveO (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })) h = true
  qd1 : queuedB (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })) h = true
  rd1 : readOrder (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) h =
    some { row with remaining := row.remaining - umin L.rem row.remaining }
  q1 : (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue c.l = h :: qs
  hash1 : h ∈ (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).hash
  ll1 : liveL (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })) c.l = true
  rl1 : readLevel (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) c.l =
    readLevel s c.l
  next1 : qNext (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) h = qs.head?

theorem core_facts {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH} {row : OrderRow}
    {level : PriceLevel} {resting : Order} {restOrders : List Order}
    (hI : IInv c s L ts inc contra strades)
    (hf : HeadFacts c s L inc contra h qs row level resting restOrders) :
    Core c s L inc h qs row resting := by
  have hw := hI.sinv.inv.wf
  have hvis := hf.rv.vis
  have hrr := hf.rv.rem
  have hir := hf.incRem
  have hnz : row.remaining.toNat ≠ 0 := by rw [← hvis]; exact hf.ah.visible
  have hin : inc.remainingQty ≠ 0 := hf.ah.rem
  have hF := umin_toNat L.rem row.remaining
  have fle : umin L.rem row.remaining ≤ L.rem := UInt64.le_iff_toNat_le.mpr (umin_le_left _ _)
  have fler : umin L.rem row.remaining ≤ row.remaining := UInt64.le_iff_toNat_le.mpr (umin_le_right _ _)
  have s1 := UInt64.toNat_sub_of_le _ _ fle
  have s2 := UInt64.toNat_sub_of_le _ _ fler
  have qpos : 0 < min inc.remainingQty resting.visibleQty := by
    rw [hvis]
    have a : 0 < inc.remainingQty := Nat.pos_of_ne_zero hin
    have b : 0 < row.remaining.toNat := Nat.pos_of_ne_zero hnz
    exact Nat.lt_min.mpr ⟨a, b⟩
  have part : row.remaining - umin L.rem row.remaining ≠ 0 → L.rem - umin L.rem row.remaining = 0 := by
    intro hp
    have : (row.remaining - umin L.rem row.remaining).toNat ≠ 0 := fun e => hp (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rw [s2, hF] at this
    apply UInt64.toNat_inj.mp
    rw [s1, hF]
    show _ = 0
    omega
  have hpre : writeOrder.pre (view s) h { row with remaining := row.remaining - umin L.rem row.remaining } :=
    ⟨row, hf.hrow, fun _ => rfl⟩
  have hv1 := writeOrder_law s h { row with remaining := row.remaining - umin L.rem row.remaining } hw hpre
  have hw1 := writeOrder_preserves_WF hw hpre hv1
  have hq1 : (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue c.l = h :: qs := by
    rw [hv1]; exact hf.hq
  refine ⟨fle, fler, ?_, qpos, ?_, ?_, part, UInt64.sub_le fler, UInt64.sub_le fle, hv1, hw1, ?_, ?_, ?_,
    hq1, ?_, ?_, ?_, qNext_head hw1 hq1⟩
  · rw [hF, hvis, hir]
  · rw [s1, hF, hvis, hir]
  · rw [s2, hF, hvis, hir, hrr]
  · rw [hv1]; try simp [liveO, setRemDb]
  · have := hf.hqd
    rw [hv1]; simpa [queuedB, setRemDb] using this
  · rw [readOrder_law, hv1]; simp [setRemDb]
  · rw [hv1]; exact hf.hhash
  · have := hf.hll; rw [hv1]; simpa [liveL, setRemDb] using this
  · rw [readLevel_law, readLevel_law, hv1]

theorem decInc_aggr (inc : Order) (q : Nat) (x : UInt64) (hx : x.toNat = inc.remainingQty - q)
    (hnc : inc.status ≠ .cancelled) :
    x.toNat = if (decInc inc q).status = .cancelled then 0 else (decInc inc q).remainingQty := by
  unfold decInc
  by_cases hz : inc.remainingQty - q = 0
  · simp [hz, hx]
  · simp [hz, hnc, hx]

theorem inner_dec {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH} {row : OrderRow}
    {level : PriceLevel} {resting : Order} {restOrders : List Order}
    (hc : c.Ok) (hI : IInv c s L ts inc contra strades) (hrem : L.rem ≠ 0)
    (hf : HeadFacts c s L inc contra h qs row level resting restOrders)
    (hconf : c.r.account ≠ 0 ∧ c.r.account = row.account ∧ c.r.stpMode ≠ 0) (h4 : c.r.stpMode = 4) :
    IStep c s L ts := by
  have hw := hI.sinv.inv.wf
  have hcf : selfTradeConflict inc resting = true := by rw [conflict_of hc hI hf, decide_eq_true hconf]
  have h1 : c.r.stpMode ≠ 1 := by rw [h4]; decide
  have h23 : ¬(c.r.stpMode = 2 ∨ c.r.stpMode = 3) := by rw [h4]; decide
  have hpol := (policy_of hc.req hI.shape hconf.1).2.2.2 h4
  have K := core_facts hI hf
  have htb := hI.tbound
  rw [if_neg hrem] at htb
  have hcnt1 := count_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
  have hlu1 := levelsUsed_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
  have hh1 : h ∈ (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue c.l := by
    rw [K.q1]; exact List.mem_cons_self
  -- the first half of the block
  have e1 := ev_min (s := s) (r := c.r) (L := L) (ts := ts) hf.hp hf.hlo hf.hread
  have e2 := ev_subRem (P := program) (s := s) (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining }) K.fle
  have e3 := ev_prem (P := program) (s := s) (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining })
    hf.hp hf.hlo hf.hread K.fler
  have e4 := ev_setRem (P := program) (s := s) (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining })
    hf.hp hf.hlo hf.hread
  have e5 := ev_qNextN (P := program) (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
    (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining })
    hf.hp K.lo1 K.qd1
  rw [K.next1] at e5
  have e7 := ev_passiveNext (P := program)
    (s := dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) c.l h)
    (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
  have e7' := ev_passiveNext (P := program)
    (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
    (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
  have ite_to : ∀ {st' : St S},
      Eval program (Stmt.block decStmts) (mkSt s c.r L ts) (st', .normal) →
      Eval program innerBody (mkSt s c.r L ts) (st', .normal) := fun hb =>
    Eval.ite_true (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_true hconf])
      (Eval.ite_false (by rw [ev_stp_eq]; simp only [STP_CANCEL_NEW]; rw [decide_eq_false h1])
        (Eval.ite_false (by rw [ev_oldBoth, decide_eq_false h23]) hb))
  have hmin := K.qpos
  by_cases hz : row.remaining - umin L.rem row.remaining = 0
  · -- the resting order is used up: it leaves its level
    have hfull : resting.remainingQty - min inc.remainingQty resting.visibleQty = 0 := by
      rw [← K.premq, hz]; rfl
    obtain ⟨hv2, hw2, hc2, hl2, -⟩ := dropS_facts K.w1 hh1 K.hash1
    rw [K.v1, dropDb_setRem] at hv2
    obtain ⟨hs', hq'⟩ := sinv_drop hc hI.sinv hf.hq hf.hcontra hf.hlv hf.hro hf.hpx hv2 hw2
      (by rw [← hcnt1]; exact hc2) (by rw [hl2, hlu1])
    have e6 := ev_premWhen_zero (P := program) (r := c.r) (ts := ts)
      (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                     prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
      hz hI.best hf.hp K.w1 hh1 K.hash1 K.ll1
    refine ⟨_, _, ts, decInc inc (min inc.remainingQty resting.visibleQty),
      drop1 level restOrders c.RL, strades,
      ite_to (Eval.block_cons_normal e1 (Eval.block_cons_normal e2 (Eval.block_cons_normal e3
        (Eval.block_cons_normal e4 (Eval.block_cons_normal e5 (Eval.block_cons_normal e6 e7
        (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)), ?_, ?_⟩
    · refine ⟨hs', hI.best, hI.stop, ?_, decInc_aggr _ _ _ K.remq hf.notc, ?_, ?_, hI.trades, ?_,
        UInt64.le_trans K.remle hI.remle⟩
      · rw [hI.spec, hf.hcontra]
        exact rest_step (step_decrement_full hf.ah hcf hpol hfull) (mm_drop1 hf.hlv _ _)
      · unfold decInc; exact hI.shape.upd _ _
      · intro _; show qs.head? = _; rw [hq']
      · show ts.length + _ ≤ _
        have : count (dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) c.l h) + 1 = count s := by
          rw [← hcnt1]; exact hc2
        split <;> omega
    · unfold imeasure; rw [hq', hf.hq]; simp only [List.length_cons, if_neg hrem]; split <;> omega
  · -- the resting order stays with less: the incoming order is used up
    have hpart : resting.remainingQty - min inc.remainingQty resting.visibleQty ≠ 0 := by
      rw [← K.premq]; intro e; exact hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have hr0 := K.part hz
    have hp0 : 0 < row.remaining - umin L.rem row.remaining := by
      rw [UInt64.lt_iff_toNat_lt]; have : (row.remaining - umin L.rem row.remaining).toNat ≠ 0 :=
        fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
      simp; omega
    have hvw : orderView { resting with
        remainingQty := resting.remainingQty - min inc.remainingQty resting.visibleQty,
        visibleQty := resting.visibleQty - min inc.remainingQty resting.visibleQty } =
        orderView (restingOrder c.t { row with remaining := row.remaining - umin L.rem row.remaining } 0) :=
      view_update hf.hrv _ _ _ K.premq.symm (by
        rw [show resting.visibleQty - min inc.remainingQty resting.visibleQty = resting.remainingQty - min inc.remainingQty resting.visibleQty from by rw [hf.rv.vis, hf.rv.rem]]
        exact K.premq.symm)
    obtain ⟨hs', hq'⟩ := sinv_setRem hc hI.sinv hf.hq hf.hcontra hf.hro hf.hpx hf.hrow hp0 K.prle hvw
      K.v1 K.w1 hcnt1 hlu1
    have e6 := ev_premWhen_pos (P := program) (r := c.r) (ts := ts)
      (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
      (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                     prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? }) hz
    refine ⟨_, _, ts, decInc inc (min inc.remainingQty resting.visibleQty),
      { price := level.price, orders := { resting with remainingQty := resting.remainingQty - min inc.remainingQty resting.visibleQty, visibleQty := resting.visibleQty - min inc.remainingQty resting.visibleQty } :: restOrders } :: c.RL, strades,
      ite_to (Eval.block_cons_normal e1 (Eval.block_cons_normal e2 (Eval.block_cons_normal e3
        (Eval.block_cons_normal e4 (Eval.block_cons_normal e5 (Eval.block_cons_normal e6 e7'
        (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)), ?_, ?_⟩
    · refine ⟨hs', hI.best, hI.stop, ?_, decInc_aggr _ _ _ K.remq hf.notc, ?_, ?_, hI.trades, ?_,
        UInt64.le_trans K.remle hI.remle⟩
      · rw [hI.spec, hf.hcontra]
        refine rest_step (step_decrement_part hf.ah hcf hpol hpart) (mm_head hf.hlv _ ?_ _ _)
        show resting.remainingQty - min inc.remainingQty resting.visibleQty < resting.remainingQty
        refine Nat.sub_lt ?_ hmin
        rw [hf.rv.rem, ← hf.rv.vis]; exact Nat.pos_of_ne_zero hf.ah.visible
      · unfold decInc; exact hI.shape.upd _ _
      · intro e; exact absurd hr0 e
      · show ts.length + _ ≤ c.C0 + (if L.rem - umin L.rem row.remaining = 0 then 1 else 0)
        rw [if_pos hr0, hcnt1]; omega
    · unfold imeasure; rw [hq', hf.hq]; show _ + (if L.rem - umin L.rem row.remaining = 0 then 0 else 1) < _
      rw [if_pos hr0, if_neg hrem]; omega

theorem count_pos_of_head {c : OCtx} {s : S} {contra : List PriceLevel} {h : OrderH}
    {qs : List OrderH} (hc : c.Ok) (hs : SInv c s contra) (hq : (view s).queue c.l = h :: qs) :
    1 ≤ count s := by
  have hle : ((view s).queue c.l).length ≤ restingCount (view s) := by
    unfold restingCount
    apply le_sum_of_mem_nat
    apply List.mem_map.mpr
    exact ⟨c.l, by cases ht : c.t <;> simp [← ht, hs.mem hc], rfl⟩
  rw [hq] at hle
  have := hs.inv.count_eq
  simp at hle; omega

theorem inner_fill {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH} {row : OrderRow}
    {level : PriceLevel} {resting : Order} {restOrders : List Order}
    (hc : c.Ok) (hcap : CapOk S) (hC0 : c.C0 ≤ capacity (S := S))
    (hI : IInv c s L ts inc contra strades) (hrem : L.rem ≠ 0)
    (hf : HeadFacts c s L inc contra h qs row level resting restOrders)
    (hconf : ¬(c.r.account ≠ 0 ∧ c.r.account = row.account ∧ c.r.stpMode ≠ 0)) :
    IStep c s L ts := by
  have hw := hI.sinv.inv.wf
  have hcf : selfTradeConflict inc resting = false := by rw [conflict_of hc hI hf, decide_eq_false hconf]
  have K := core_facts hI hf
  have htb := hI.tbound
  rw [if_neg hrem] at htb
  have hpos := count_pos_of_head hc hI.sinv hf.hq
  obtain ⟨lrow, hlrow⟩ : ∃ lrow, readLevel s c.l = some lrow := by
    have := hf.hll
    rw [readLevel_law]
    simp only [liveL] at this
    exact Option.isSome_iff_exists.mp this
  have hlp : level.price = lrow.price.toNat := by
    rw [hf.hpx]; rw [readLevel_law] at hlrow; simp [Db.levelPrice, hlrow]
  have htrade : tradeObs (fillTrade inc level resting (min inc.remainingQty resting.visibleQty)) =
      toNatTrade row.id c.r.id lrow.price (umin L.rem row.remaining) := by
    simp only [tradeObs, fillTrade, toNatTrade, TradeObs.mk.injEq]
    exact ⟨hf.rv.id, by rw [hI.shape.id, hc.req.id], hlp, K.fq.symm⟩
  have hcnt1 := count_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
  have hlu1 := levelsUsed_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
  have hh1 : h ∈ (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue c.l := by
    rw [K.q1]; exact List.mem_cons_self
  let T := toNatTrade row.id c.r.id lrow.price (umin L.rem row.remaining)
  have e1 := ev_min (s := s) (r := c.r) (L := L) (ts := ts) hf.hp hf.hlo hf.hread
  have e2 := ev_subRem (P := program) (s := s) (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining }) K.fle
  have e3 := ev_prem (P := program) (s := s) (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining })
    hf.hp hf.hlo hf.hread K.fler
  have e4 := ev_setRem (P := program) (s := s) (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining })
    hf.hp hf.hlo hf.hread
  have e4b := ev_emit (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
    (r := c.r) (ts := ts)
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining })
    hcap hf.hp K.lo1 K.rd1 hI.best K.ll1 (by rw [K.rl1]; exact hlrow) (by omega)
  have e5 := ev_qNextN (P := program) (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
    (r := c.r) (ts := ts ++ [T])
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining })
    hf.hp K.lo1 K.qd1
  rw [K.next1] at e5
  have e7 := ev_passiveNext (P := program)
    (s := dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) c.l h)
    (r := c.r) (ts := ts ++ [T])
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
  have e7' := ev_passiveNext (P := program)
    (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
    (r := c.r) (ts := ts ++ [T])
    (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                   prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
  have ite_to : ∀ {st' : St S},
      Eval program (Stmt.block fillStmts) (mkSt s c.r L ts) (st', .normal) →
      Eval program innerBody (mkSt s c.r L ts) (st', .normal) := fun hb =>
    Eval.ite_false (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_false hconf]) hb
  have hmin := K.qpos
  have htr : ts ++ [T] = (strades ++ [fillTrade inc level resting (min inc.remainingQty resting.visibleQty)]).map tradeObs := by
    rw [List.map_append, ← hI.trades, List.map_singleton, htrade]
  by_cases hz : row.remaining - umin L.rem row.remaining = 0
  · have hfull : resting.remainingQty - min inc.remainingQty resting.visibleQty = 0 := by
      rw [← K.premq, hz]; rfl
    obtain ⟨hv2, hw2, hc2, hl2, -⟩ := dropS_facts K.w1 hh1 K.hash1
    rw [K.v1, dropDb_setRem] at hv2
    obtain ⟨hs', hq'⟩ := sinv_drop hc hI.sinv hf.hq hf.hcontra hf.hlv hf.hro hf.hpx hv2 hw2
      (by rw [← hcnt1]; exact hc2) (by rw [hl2, hlu1])
    have e6 := ev_premWhen_zero (P := program) (r := c.r) (ts := ts ++ [T])
      (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                     prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
      hz hI.best hf.hp K.w1 hh1 K.hash1 K.ll1
    refine ⟨_, _, ts ++ [T], { inc with remainingQty := inc.remainingQty - min inc.remainingQty resting.visibleQty },
      drop1 level restOrders c.RL, strades ++ [fillTrade inc level resting (min inc.remainingQty resting.visibleQty)],
      ite_to (Eval.block_cons_normal e1 (Eval.block_cons_normal e2 (Eval.block_cons_normal e3
        (Eval.block_cons_normal e4 (Eval.block_cons_normal e4b (Eval.block_cons_normal e5
        (Eval.block_cons_normal e6 e7 (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp))
        (by simp)), ?_, ?_⟩
    · refine ⟨hs', hI.best, hI.stop, ?_, by simp [hf.notc, K.remq], hI.shape.updRem _, ?_, htr, ?_,
        UInt64.le_trans K.remle hI.remle⟩
      · rw [hI.spec, hf.hcontra]
        exact rest_step (step_fill_full hf.ah hcf hfull) (mm_drop1 hf.hlv _ _)
      · intro _; show qs.head? = _; rw [hq']
      · show (ts ++ [T]).length + _ ≤ _
        have : count (dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) c.l h) + 1 = count s := by
          rw [← hcnt1]; exact hc2
        simp only [List.length_append, List.length_singleton]
        split <;> omega
    · unfold imeasure; rw [hq', hf.hq]; simp only [List.length_cons, if_neg hrem]; split <;> omega
  · have hpart : resting.remainingQty - min inc.remainingQty resting.visibleQty ≠ 0 := by
      rw [← K.premq]; intro e; exact hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have hr0 := K.part hz
    have hp0 : 0 < row.remaining - umin L.rem row.remaining := by
      rw [UInt64.lt_iff_toNat_lt]; have : (row.remaining - umin L.rem row.remaining).toNat ≠ 0 :=
        fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
      simp; omega
    have hvw : orderView { resting with
        remainingQty := resting.remainingQty - min inc.remainingQty resting.visibleQty,
        visibleQty := resting.visibleQty - min inc.remainingQty resting.visibleQty,
        status := .partiallyFilled } =
        orderView (restingOrder c.t { row with remaining := row.remaining - umin L.rem row.remaining } 0) :=
      view_update_st hf.hrv _ _ _ K.premq.symm (by
        rw [show resting.visibleQty - min inc.remainingQty resting.visibleQty = resting.remainingQty - min inc.remainingQty resting.visibleQty from by rw [hf.rv.vis, hf.rv.rem]]
        exact K.premq.symm) _
    obtain ⟨hs', hq'⟩ := sinv_setRem hc hI.sinv hf.hq hf.hcontra hf.hro hf.hpx hf.hrow hp0 K.prle hvw
      K.v1 K.w1 hcnt1 hlu1
    have e6 := ev_premWhen_pos (P := program) (r := c.r) (ts := ts ++ [T])
      (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
      (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                     prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? }) hz
    refine ⟨_, _, ts ++ [T], { inc with remainingQty := inc.remainingQty - min inc.remainingQty resting.visibleQty },
      { price := level.price, orders := { resting with remainingQty := resting.remainingQty - min inc.remainingQty resting.visibleQty, visibleQty := resting.visibleQty - min inc.remainingQty resting.visibleQty, status := .partiallyFilled } :: restOrders } :: c.RL,
      strades ++ [fillTrade inc level resting (min inc.remainingQty resting.visibleQty)],
      ite_to (Eval.block_cons_normal e1 (Eval.block_cons_normal e2 (Eval.block_cons_normal e3
        (Eval.block_cons_normal e4 (Eval.block_cons_normal e4b (Eval.block_cons_normal e5
        (Eval.block_cons_normal e6 e7' (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp))
        (by simp)), ?_, ?_⟩
    · refine ⟨hs', hI.best, hI.stop, ?_, by simp [hf.notc, K.remq], hI.shape.updRem _, ?_, htr, ?_,
        UInt64.le_trans K.remle hI.remle⟩
      · rw [hI.spec, hf.hcontra]
        refine rest_step (step_fill_part hf.ah hcf hpart) (mm_head hf.hlv _ ?_ _ _)
        show resting.remainingQty - min inc.remainingQty resting.visibleQty < resting.remainingQty
        refine Nat.sub_lt ?_ hmin
        rw [hf.rv.rem, ← hf.rv.vis]; exact Nat.pos_of_ne_zero hf.ah.visible
      · intro e; exact absurd hr0 e
      · show (ts ++ [T]).length + _ ≤ c.C0 + (if L.rem - umin L.rem row.remaining = 0 then 1 else 0)
        rw [if_pos hr0]; have := hcnt1; simp only [List.length_append, List.length_singleton]; omega
    · unfold imeasure; rw [hq', hf.hq]; show _ + (if L.rem - umin L.rem row.remaining = 0 then 0 else 1) < _
      rw [if_pos hr0, if_neg hrem]; omega

-- ============================================================================
-- (a) One inner iteration is one doMatch step
-- ============================================================================

/-- **Inner body.** One iteration of the inner loop, from a state where the loop
    condition holds, is one `doMatch` step and re-establishes the invariant
    with a smaller measure. -/
theorem inner_body {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade} {h : OrderH} {qs : List OrderH}
    (hc : c.Ok) (hcap : CapOk S) (hC0 : c.C0 ≤ capacity (S := S))
    (hI : IInv c s L ts inc contra strades) (hrem : L.rem ≠ 0)
    (hq : (view s).queue c.l = h :: qs) : IStep c s L ts := by
  obtain ⟨row, level, resting, restOrders, hf⟩ := head_facts hc hI hrem hq
  by_cases hconf : c.r.account ≠ 0 ∧ c.r.account = row.account ∧ c.r.stpMode ≠ 0
  · rcases hc.req.stp with h0 | h1 | h2 | h3 | h4
    · exact absurd h0 hconf.2.2
    · exact inner_cancelNew hc hI hrem hf hconf h1
    · exact inner_cancelOld hc hI hrem hf hconf (Or.inl h2)
    · exact inner_cancelOld hc hI hrem hf hconf (Or.inr h3)
    · exact inner_dec hc hI hrem hf hconf h4
  · exact inner_fill hc hcap hC0 hI hrem hf hconf

-- ============================================================================
-- (b) The inner loop
-- ============================================================================

theorem inner_run {c : OCtx} (hc : c.Ok) (hcap : CapOk S) (hC0 : c.C0 ≤ capacity (S := S)) :
    ∀ (μ : Nat) (s : S) (L : Loc) (ts : List TradeObs) (inc : Order) (contra : List PriceLevel)
      (strades : List Trade), IInv c s L ts inc contra strades → imeasure c s L ≤ μ →
      ∃ s' L' ts' inc' contra' strades',
        LoopRun program innerCond innerBody μ (mkSt s c.r L ts) (mkSt s' c.r L' ts', .normal) ∧
        IInv c s' L' ts' inc' contra' strades' ∧ (L'.rem = 0 ∨ (view s').queue c.l = []) := by
  intro μ
  induction μ with
  | zero =>
    intro s L ts inc contra strades hI hμ
    have hr : L.rem = 0 := by
      unfold imeasure at hμ; by_cases h : L.rem = 0
      · exact h
      · rw [if_neg h] at hμ; omega
    refine ⟨s, L, ts, inc, contra, strades, .stop ?_, hI, Or.inl hr⟩
    rw [ev_innerCond, hr]; simp
  | succ μ ih =>
    intro s L ts inc contra strades hI hμ
    by_cases hr : L.rem = 0
    · refine ⟨s, L, ts, inc, contra, strades, .stop ?_, hI, Or.inl hr⟩
      rw [ev_innerCond, hr]; simp
    · cases hq : (view s).queue c.l with
      | nil =>
        refine ⟨s, L, ts, inc, contra, strades, .stop ?_, hI, Or.inr hq⟩
        rw [ev_innerCond, hI.passive hr, hq]; simp
      | cons h qs =>
        obtain ⟨s1, L1, ts1, inc1, contra1, strades1, hev, hI1, hlt⟩ :=
          inner_body hc hcap hC0 hI hr hq
        obtain ⟨s', L', ts', inc', contra', strades', hrun, hI', hexit⟩ :=
          ih s1 L1 ts1 inc1 contra1 strades1 hI1 (by omega)
        refine ⟨s', L', ts', inc', contra', strades', .step ?_ hev hrun, hI', hexit⟩
        rw [ev_innerCond, hI.passive hr, hq]
        have : 0 < L.rem := by
          rw [UInt64.lt_iff_toNat_lt]; have : L.rem.toNat ≠ 0 := fun e => hr (UInt64.toNat_inj.mp (by rw [e]; rfl))
          simp; omega
        simp [this]

theorem boundVal_capPlus1 (hcap : CapOk S) :
    boundVal (S := S) (.capPlus 1) = .ok (capacity (S := S) + 1) := by
  unfold CapOk at hcap
  simp [boundVal, hcap]

/-- **Inner loop.** From the invariant, the inner loop runs to completion within
    its bound `capacity + 1`, ending with the invariant and its exit condition. -/
theorem inner_loop {c : OCtx} {s : S} {L : Loc} {ts : List TradeObs} {inc : Order}
    {contra : List PriceLevel} {strades : List Trade}
    (hc : c.Ok) (hcap : CapOk S) (hC0 : c.C0 ≤ capacity (S := S))
    (hI : IInv c s L ts inc contra strades) :
    ∃ s' L' ts' inc' contra' strades',
      Eval program (.loop (.capPlus 1) innerCond innerBody) (mkSt s c.r L ts) (mkSt s' c.r L' ts', .normal) ∧
      IInv c s' L' ts' inc' contra' strades' ∧ (L'.rem = 0 ∨ (view s').queue c.l = []) := by
  have hle : imeasure c s L ≤ capacity (S := S) + 1 := by
    unfold imeasure
    have hq : ((view s).queue c.l).length ≤ restingCount (view s) := by
      unfold restingCount
      apply le_sum_of_mem_nat
      apply List.mem_map.mpr
      exact ⟨c.l, by cases ht : c.t <;> simp [← ht, hI.sinv.mem hc], rfl⟩
    have := hI.sinv.inv.count_eq
    have := hI.sinv.inv.count_le
    split <;> omega
  obtain ⟨s', L', ts', inc', contra', strades', hrun, hI', hexit⟩ :=
    inner_run hc hcap hC0 (imeasure c s L) s L ts inc contra strades hI (Nat.le_refl _)
  exact ⟨s', L', ts', inc', contra', strades', Eval.loop (boundVal_capPlus1 hcap) (hrun.mono hle),
    hI', hexit⟩

end MatcherInner

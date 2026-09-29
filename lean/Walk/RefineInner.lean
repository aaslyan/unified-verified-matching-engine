import Walk.WFInv
import Walk.LogicInv

/-!
# A3a: the program's inner loop refines the walk's

The relation between a program state inside an outer iteration (store `s`,
locals `L`, trade buffer `ts`) and a walk state `st` is `WR`:

* **identity** — `bookView (absBook (view s)) = bookView st.book`, `rem`,
  `stop`, and `ts = st.trades.map tradeObs`;
* **the two derived locals** — `best` is the level `l` the iteration fetched,
  `passive` is the head of `l`'s queue while `rem ≠ 0`;
* **store-side** — `InvM s l` (`main`'s invariant with `l` allowed empty), `l`
  in the contra tree and best there.

There is no continuation clause: nothing in `WR` mentions the reference
(`doMatch`, `rest`) or a final result. The walk's own state is the thing
related, and A2 carries the walk to the reference separately.
-/

namespace Walk

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore MatcherLoop MatcherInner

variable {S : Type} [EngineDb S]

open EngineDb

/-- The walk's context for a request on this store. -/
def wctx (S : Type) [EngineDb S] (r : CRequest) (isBuy : Bool) : Ctx :=
  { cap := capacity (S := S), r := r, isBuy := isBuy }

theorem wctx_contra (r : CRequest) (isBuy : Bool) : (wctx S r isBuy).contra = contraT isBuy := rfl
theorem wctx_own (r : CRequest) (isBuy : Bool) : (wctx S r isBuy).own = ownT isBuy := rfl

/-- **The inner-loop relation.** -/
structure WR (r : CRequest) (isBuy : Bool) (l : LevelH) (s : S) (L : Loc) (ts : List TradeObs)
    (st : State) : Prop where
  inv     : InvM s l
  mem     : l ∈ (view s).tree (contraT isBuy)
  best    : ∀ l' ∈ (view s).tree (contraT isBuy),
    better (contraT isBuy) ((view s).levelPrice l) ((view s).levelPrice l')
  book    : bookView (absBook (view s)) = bookView st.book
  rem     : L.rem.toNat = st.rem
  stop    : L.stop = st.stop
  trades  : ts = st.trades.map tradeObs
  bestL   : L.best = some l
  passive : L.rem ≠ 0 → L.passive = ((view s).queue l).head?

-- ============================================================================
-- Views by side
-- ============================================================================

theorem bookView_sides {X Y : BookState} :
    bookView X = bookView Y ↔
      ((sideL X .bids).map levelView = (sideL Y .bids).map levelView ∧
       (sideL X .asks).map levelView = (sideL Y .asks).map levelView ∧
       X.stops.map orderView = Y.stops.map orderView) := by
  simp [bookView, sideL]

theorem sideL_absBook (db : Db) (t : Tree) : sideL (absBook db) t = absSide db t := by
  cases t <;> rfl

/-- **One store step, one walk step, same view.** If the store changed only at
    level `l` (a `Frame`) and the walk changed only its contra head level, and
    the two new head levels have the same view, the books keep the same view. -/
theorem book_step {db db' : Db} {t : Tree} {l : LevelH} {B B' : BookState}
    {L0 L1 : PriceLevel} {R : List PriceLevel}
    (hw : db.WF) (hw' : db'.WF) (hf : Frame l db db') (hl : l ∈ db.tree t)
    (hb : ∀ l' ∈ db.tree t, better t (db.levelPrice l) (db.levelPrice l'))
    (hB : bookView (absBook db) = bookView B) (hs : sideL B t = L0 :: R)
    (hs' : sideL B' t = L1 :: R) (ho : ∀ t', t' ≠ t → sideL B' t' = sideL B t')
    (hst : B'.stops = B.stops) (hv : levelView (absLevel db' t l) = levelView L1) :
    bookView (absBook db') = bookView B' := by
  have hsplit := absSide_best hw hl hb
  have hl' : l ∈ db'.tree t := by rw [hf.tree]; exact hl
  have hb' : ∀ l' ∈ db'.tree t, better t (db'.levelPrice l) (db'.levelPrice l') := by
    intro l' h'; rw [hf.levelPrice_eq, hf.levelPrice_eq]; rw [hf.tree] at h'; exact hb l' h'
  have hsplit' := absSide_best hw' hl' hb'
  have hrest := hf.restSide_eq hw t
  rw [bookView_sides] at hB ⊢
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hcontra : (sideL (absBook db') t).map levelView = (sideL B' t).map levelView := by
    have htB : (sideL (absBook db) t).map levelView = (sideL B t).map levelView := by
      cases t; exact hB1; exact hB2
    rw [sideL_absBook, hsplit, hs] at htB
    rw [sideL_absBook, hsplit', hs', hrest]
    simp only [List.map_cons, List.cons.injEq] at htB ⊢
    exact ⟨hv, htB.2⟩
  have hother : ∀ t', t' ≠ t →
      (sideL (absBook db') t').map levelView = (sideL B' t').map levelView := by
    intro t' ht'
    have hnot : l ∉ db.tree t' := fun h => by
      cases t <;> cases t'
      · exact ht' rfl
      · exact hw.tree_disjoint l hl h
      · exact hw.tree_disjoint l h hl
      · exact ht' rfl
    rw [sideL_absBook, hf.absSide_other hnot, ho t' ht', ← sideL_absBook]
    cases t' <;> assumption
  refine ⟨?_, ?_, ?_⟩
  · cases t
    · exact hcontra
    · exact hother .bids (by decide)
  · cases t
    · exact hother .asks (by decide)
    · exact hcontra
  · rw [hst]; exact hB3

-- ============================================================================
-- The head of the walk's contra side
-- ============================================================================

/-- Under `WR`, the walk's contra side is the decoded level `l` followed by the
    decoded rest of the tree, through the view. -/
theorem wr_split {r : CRequest} {isBuy : Bool} {l : LevelH} {s : S} {L : Loc}
    {ts : List TradeObs} {st : State} (hW : WR r isBuy l s L ts st) :
    ∃ L0 R, sideL st.book (contraT isBuy) = L0 :: R ∧
      levelView L0 = levelView (absLevel (view s) (contraT isBuy) l) ∧
      R.map levelView = (restSide (view s) (contraT isBuy) l).map levelView := by
  have hsplit := absSide_best hW.inv.wf hW.mem hW.best
  have hB := hW.book
  rw [bookView_sides] at hB
  have ht : (sideL (absBook (view s)) (contraT isBuy)).map levelView =
      (sideL st.book (contraT isBuy)).map levelView := by
    cases h : contraT isBuy
    · exact hB.1
    · exact hB.2.1
  rw [sideL_absBook, hsplit] at ht
  cases hc : sideL st.book (contraT isBuy) with
  | nil => rw [hc] at ht; simp at ht
  | cons L0 R =>
    rw [hc] at ht
    simp only [List.map_cons, List.cons.injEq] at ht
    exact ⟨L0, R, rfl, ht.1.symm, ht.2.symm⟩

/-- Everything one inner iteration needs about the head order `h` of `l`. -/
structure WHead (isBuy : Bool) (l : LevelH) (s : S) (L : Loc) (st : State) (h : OrderH)
    (qs : List OrderH) (row : OrderRow) (L0 : PriceLevel) (R : List PriceLevel) (p : Order)
    (os : List Order) : Prop where
  hq    : (view s).queue l = h :: qs
  hside : sideL st.book (contraT isBuy) = L0 :: R
  hL0   : L0.orders = p :: os
  hpv   : orderView p = orderView (restingOrder (contraT isBuy) row 0)
  rv    : RowView (contraT isBuy) row p
  hos   : os.map orderView = qs.map (ordV (view s) (contraT isBuy))
  hlp   : L0.price = ((view s).levelPrice l).toNat
  hR    : R.map levelView = (restSide (view s) (contraT isBuy) l).map levelView
  hrow  : (view s).orders h = some row
  hread : readOrder s h = some row
  hrpos : 0 < row.remaining
  hp    : L.passive = some h
  hlo   : liveO (view s) h = true
  hll   : liveL (view s) l = true
  hhash : h ∈ (view s).hash
  hqd   : queuedB (view s) h = true
  hh    : h ∈ (view s).queue l

theorem whead {r : CRequest} {isBuy : Bool} {l : LevelH} {s : S} {L : Loc}
    {ts : List TradeObs} {st : State} {h : OrderH} {qs : List OrderH}
    (hW : WR r isBuy l s L ts st) (hrem : L.rem ≠ 0) (hq : (view s).queue l = h :: qs) :
    ∃ row L0 R p os, WHead isBuy l s L st h qs row L0 R p os := by
  have hw := hW.inv.wf
  have hh : h ∈ (view s).queue l := by rw [hq]; exact List.mem_cons_self
  obtain ⟨L0, R, hside, hv0, hR⟩ := wr_split hW
  rw [levelView_absLevel, hq] at hv0
  obtain ⟨p, os, hL0, hpv0, hos, hlp⟩ := head_decomp hv0
  obtain ⟨row, hrow, -, -, hrpos, -, -⟩ := hW.inv.client.order_ok _ l hW.mem h hh
  have hpv : orderView p = orderView (restingOrder (contraT isBuy) row 0) := by
    rw [hpv0]; simp [ordV, rowOf, hrow]
  refine ⟨row, L0, R, p, os, ⟨hq, hside, hL0, hpv, rowView_of hpv, hos, hlp, hR, hrow,
    by rw [readOrder_law]; exact hrow, hrpos, by rw [hW.passive hrem, hq]; rfl,
    (hw.queue_live _ _ hh).1, hw.tree_live _ _ hW.mem,
    (hW.inv.client.hash_iff_queued h).mpr ⟨_, hh⟩, ?_, hh⟩⟩
  unfold queuedB
  rw [List.any_eq_true]
  exact ⟨l, (hw.levels_live _).mp (hw.tree_live _ _ hW.mem), by simp [hh]⟩

/-- The walk's STP test on the head order is the program's on its row. -/
theorem acct_iff {r : CRequest} {t : Tree} {row : OrderRow} {p : Order} (rv : RowView t row p) :
    (r.account ≠ 0 ∧ r.account.toNat = getAccount p ∧ r.stpMode ≠ 0) ↔
      (r.account ≠ 0 ∧ r.account = row.account ∧ r.stpMode ≠ 0) := by
  unfold getAccount
  rw [rv.group]
  constructor
  · rintro ⟨ha, he, hs⟩
    refine ⟨ha, ?_, hs⟩
    unfold stpGroupOf at he
    by_cases hr : row.account = 0
    · rw [if_pos hr] at he; exact absurd (UInt64.toNat_inj.mp (by simpa using he)) ha
    · rw [if_neg hr] at he; exact UInt64.toNat_inj.mp he
  · rintro ⟨ha, he, hs⟩
    refine ⟨ha, ?_, hs⟩
    rw [← he]; unfold stpGroupOf; rw [if_neg ha]; rfl

-- ============================================================================
-- Store side: InvM through the two store steps of an iteration
-- ============================================================================

theorem invM_drop {s s' : S} {l : LevelH} {t : Tree} {h : OrderH} (hI : InvM s l)
    (hl : l ∈ (view s).tree t) (hh : h ∈ (view s).queue l)
    (hv' : view s' = dropDb (view s) l h) (hw' : (view s').WF)
    (hcount : EngineDb.count s' + 1 = EngineDb.count s) (hlu : EngineDb.levelsUsed s' = EngineDb.levelsUsed s) : InvM s' l := by
  have hw := hI.wf
  refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv']; exact drop_clientInvM hw hI.client hh
  · rw [hv']; exact drop_orders_resting hw hh hI.orders_resting
  · rw [hv']; exact hI.levels_resting
  · rw [hv']
    have := drop_restingCount hw hl hh
    have := hI.count_eq
    omega
  · rw [hlu, hv']; exact hI.levels_eq
  · have := hI.count_le; omega

theorem invM_setRem {s s' : S} {l : LevelH} {t : Tree} {h : OrderH} {row : OrderRow}
    {p : UInt64} (hI : InvM s l) (hl : l ∈ (view s).tree t) (hh : h ∈ (view s).queue l)
    (hrow : (view s).orders h = some row) (hp0 : 0 < p) (hp : p ≤ row.remaining)
    (hv' : view s' = setRemDb (view s) h { row with remaining := p }) (hw' : (view s').WF)
    (hcount : EngineDb.count s' = EngineDb.count s) (hlu : EngineDb.levelsUsed s' = EngineDb.levelsUsed s) : InvM s' l := by
  refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv']; exact setRem_clientInvM hI.client hh hl hrow hp0 hp
  · intro y
    rw [hv']
    have := hI.orders_resting y
    by_cases hy : y = h
    · subst hy
      have hq1 : (view s).queued y := ⟨_, hh⟩
      constructor
      · intro _; exact hq1
      · intro _; simp [Db.orderLive, setRemDb]
    · simpa [Db.orderLive, setRemDb, upd_other _ _ hy, Db.queued] using this
  · rw [hv']; exact hI.levels_resting
  · rw [hcount, hv']; exact hI.count_eq
  · rw [hlu, hv']; exact hI.levels_eq
  · rw [hcount]; exact hI.count_le

/-- `l` stays in its tree and best there across a `Frame` step. -/
theorem best_frame {db db' : Db} {l : LevelH} {t : Tree} (hf : Frame l db db')
    (hl : l ∈ db.tree t) (hb : ∀ l' ∈ db.tree t, better t (db.levelPrice l) (db.levelPrice l')) :
    l ∈ db'.tree t ∧ ∀ l' ∈ db'.tree t, better t (db'.levelPrice l) (db'.levelPrice l') := by
  refine ⟨by rw [hf.tree]; exact hl, fun l' h' => ?_⟩
  rw [hf.levelPrice_eq, hf.levelPrice_eq]; rw [hf.tree] at h'; exact hb l' h'

/-- The head level after the head order leaves, through the view. -/
theorem view_drop {db : Db} {t : Tree} {l : LevelH} {h : OrderH} {qs : List OrderH}
    {L0 : PriceLevel} {os : List Order} (hw : db.WF) (hq : db.queue l = h :: qs)
    (hlp : L0.price = (db.levelPrice l).toNat) (hos : os.map orderView = qs.map (ordV db t)) :
    levelView (absLevel (dropDb db l h) t l) = levelView { L0 with orders := os } := by
  have hnd : (h :: qs).Nodup := hq ▸ hw.queue_nodup l
  rw [levelView_absLevel]
  simp only [levelView, LevelView.mk.injEq]
  refine ⟨by rw [hlp]; rfl, ?_⟩
  simp only [dropDb, upd_same, hq, List.erase_cons_head]
  rw [hos]
  apply List.map_congr_left
  intro y hy
  have : y ≠ h := fun e => by subst e; exact (List.nodup_cons.mp hnd).1 hy
  exact ordV_congr (upd_other _ _ this)

/-- The head level after the head order's remaining is rewritten, through the view. -/
theorem view_setRem {db : Db} {t : Tree} {l : LevelH} {h : OrderH} {qs : List OrderH}
    {row : OrderRow} {L0 : PriceLevel} {p : Order} {os : List Order} (hw : db.WF)
    (hq : db.queue l = h :: qs) (hlp : L0.price = (db.levelPrice l).toNat)
    (hos : os.map orderView = qs.map (ordV db t))
    (hpv : orderView p = orderView (restingOrder t row 0)) (x : UInt64) (q : Nat)
    (hq' : q = x.toNat) :
    levelView (absLevel (setRemDb db h { row with remaining := x }) t l) =
      levelView { L0 with orders := { p with remainingQty := q, visibleQty := q } :: os } := by
  have hnd : (h :: qs).Nodup := hq ▸ hw.queue_nodup l
  rw [levelView_absLevel]
  simp only [levelView, LevelView.mk.injEq, List.map_cons]
  refine ⟨by rw [hlp]; rfl, ?_⟩
  show ((setRemDb db h { row with remaining := x }).queue l).map _ = _
  simp only [setRemDb, hq, List.map_cons, List.cons.injEq]
  refine ⟨?_, ?_⟩
  · rw [view_update hpv x q q hq' hq']; simp [ordV, rowOf]
  · rw [hos]
    apply List.map_congr_left
    intro y hy
    have : y ≠ h := fun e => by subst e; exact (List.nodup_cons.mp hnd).1 hy
    exact ordV_congr (upd_other _ _ this)

-- ============================================================================
-- Decrement and fill: the shared first half
-- ============================================================================

/-- The store and quantities after `fill := min(rem, remaining)`, `rem -= fill`,
    `prem := remaining - fill`, and the write of `prem`. -/
structure WCore (l : LevelH) (s : S) (L : Loc) (h : OrderH) (qs : List OrderH)
    (row : OrderRow) : Prop where
  fle   : umin L.rem row.remaining ≤ L.rem
  fler  : umin L.rem row.remaining ≤ row.remaining
  fN    : (umin L.rem row.remaining).toNat = min L.rem.toNat row.remaining.toNat
  remN  : (L.rem - umin L.rem row.remaining).toNat = L.rem.toNat - min L.rem.toNat row.remaining.toNat
  premN : (row.remaining - umin L.rem row.remaining).toNat =
    row.remaining.toNat - min L.rem.toNat row.remaining.toNat
  part  : row.remaining - umin L.rem row.remaining ≠ 0 → L.rem - umin L.rem row.remaining = 0
  prle  : row.remaining - umin L.rem row.remaining ≤ row.remaining
  v1 : view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) =
    setRemDb (view s) h { row with remaining := row.remaining - umin L.rem row.remaining }
  w1 : (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).WF
  lo1 : liveO (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })) h = true
  qd1 : queuedB (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })) h = true
  rd1 : readOrder (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) h =
    some { row with remaining := row.remaining - umin L.rem row.remaining }
  q1 : (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue l = h :: qs
  hash1 : h ∈ (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).hash
  ll1 : liveL (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })) l = true
  rl1 : readLevel (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) l =
    readLevel s l
  next1 : qNext (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) h = qs.head?

theorem wcore {isBuy : Bool} {l : LevelH} {s : S} {L : Loc} {st : State} {h : OrderH}
    {qs : List OrderH} {row : OrderRow} {L0 : PriceLevel} {R : List PriceLevel} {p : Order}
    {os : List Order} (hw : (view s).WF) (hf : WHead isBuy l s L st h qs row L0 R p os) :
    WCore l s L h qs row := by
  have hF := umin_toNat L.rem row.remaining
  have fle : umin L.rem row.remaining ≤ L.rem := UInt64.le_iff_toNat_le.mpr (umin_le_left _ _)
  have fler : umin L.rem row.remaining ≤ row.remaining := UInt64.le_iff_toNat_le.mpr (umin_le_right _ _)
  have s1 := UInt64.toNat_sub_of_le _ _ fle
  have s2 := UInt64.toNat_sub_of_le _ _ fler
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
  have hq1 : (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue l = h :: qs := by
    rw [hv1]; exact hf.hq
  refine ⟨fle, fler, hF, by rw [s1, hF], by rw [s2, hF], part, UInt64.sub_le fler, hv1, hw1, ?_, ?_, ?_,
    hq1, ?_, ?_, ?_, qNext_head hw1 hq1⟩
  · rw [hv1]; try simp [liveO]
  · have := hf.hqd
    rw [hv1]; simpa [queuedB, setRemDb] using this
  · rw [readOrder_law, hv1]; simp
  · rw [hv1]; exact hf.hhash
  · have := hf.hll; rw [hv1]; simpa [liveL, setRemDb] using this
  · rw [readLevel_law, readLevel_law, hv1]

-- ============================================================================
-- The inner body
-- ============================================================================

/-- The walk's inner test is the program's. -/
theorem ev_innerCond_walk {r : CRequest} {isBuy : Bool} {l : LevelH} {s : S} {L : Loc}
    {ts : List TradeObs} {st : State} (hW : WR r isBuy l s L ts st) :
    evalExpr (mkSt s r L ts) innerCond = .ok (.bool (innerTest (wctx S r isBuy) st)) := by
  rw [ev_innerCond]
  congr 2
  unfold innerTest
  obtain ⟨L0, R, hside, hv0, -⟩ := wr_split hW
  rw [wctx_contra, tBest_eq, hside, List.head?_cons, Option.bind_some, qFirst, ← hW.rem]
  by_cases hr : L.rem = 0
  · simp [hr]
  · have hpos : 0 < L.rem := by
      rw [UInt64.lt_iff_toNat_lt]
      have : L.rem.toNat ≠ 0 := fun e => hr (UInt64.toNat_inj.mp (by rw [e]; rfl))
      simp; omega
    have hposN : 0 < L.rem.toNat := by rw [UInt64.lt_iff_toNat_lt] at hpos; simpa using hpos
    rw [hW.passive hr]
    simp only [hpos, hposN, decide_true, Bool.and_true]
    rw [levelView_absLevel] at hv0
    have hlen := congrArg (fun v : LevelView => v.orders.length) hv0
    simp only [levelView, List.length_map] at hlen
    cases hq : (view s).queue l with
    | nil => rw [hq] at hlen; cases ho : L0.orders <;> simp_all
    | cons h qs => rw [hq] at hlen; cases ho : L0.orders <;> simp_all

/-- **The inner body.** One execution of the program's inner loop body, from a
    state related to `st` where the inner test holds, is one `innerStep`: it
    ends normally in a state related to `innerStep st` by the same relation. -/
theorem w_inner_body (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {l : LevelH} {s : S}
    {L : Loc} {ts : List TradeObs} {st st' : State} (hW : WR r isBuy l s L ts st)
    (ht : innerTest (wctx S r isBuy) st = true) (hs : innerStep (wctx S r isBuy) st = some st') :
    ∃ s' L', Eval program innerBody (mkSt s r L ts)
        (mkSt s' r L' (st'.trades.map tradeObs), .normal) ∧
      WR r isBuy l s' L' (st'.trades.map tradeObs) st' := by
  have hw := hW.inv.wf
  have hrem : L.rem ≠ 0 := by
    intro e; simp [innerTest, ← hW.rem, e] at ht
  have hqne : (view s).queue l ≠ [] := by
    intro hq
    have := ev_innerCond_walk hW
    rw [ev_innerCond, hW.passive hrem, hq, ht] at this
    simp at this
  obtain ⟨h, qs, hq⟩ : ∃ h qs, (view s).queue l = h :: qs := by
    cases e : (view s).queue l with
    | nil => exact absurd e hqne
    | cons h qs => exact ⟨h, qs, rfl⟩
  obtain ⟨row, L0, R, p, os, hf⟩ := whead hW hrem hq
  have htr : st.trades.map tradeObs = ts := hW.trades.symm
  have hfr : Frame l (view s) (dropDb (view s) l h) := frame_drop hw hf.hh
  unfold innerStep at hs
  rw [wctx_contra, tBest_eq, hf.hside] at hs
  simp only [List.head?_cons, qFirst, hf.hL0] at hs
  simp only [wctx] at hs
  by_cases hconf : r.account ≠ 0 ∧ r.account = row.account ∧ r.stpMode ≠ 0
  · rw [if_pos ((acct_iff hf.rv).mpr hconf)] at hs
    by_cases h1 : r.stpMode = 1
    · -- CANCEL_NEW: rem = 0
      simp only [if_pos h1, Option.some.injEq] at hs
      subst hs
      refine ⟨s, { L with rem := 0 }, ?_, ⟨hW.inv, hW.mem, hW.best, hW.book, rfl, hW.stop, rfl,
        hW.bestL, fun e => absurd rfl e⟩⟩
      dsimp only; rw [htr]
      exact Eval.ite_true (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_true hconf])
        (Eval.ite_true (by rw [ev_stp_eq]; simp only [STP_CANCEL_NEW]; rw [decide_eq_true h1]) ev_rem0)
    · simp only [if_neg h1] at hs
      by_cases h23 : r.stpMode = 2 ∨ r.stpMode = 3
      · -- CANCEL_OLD / CANCEL_BOTH: the head order leaves
        rw [if_pos h23] at hs
        obtain ⟨hv', hw', hcnt, hlu, -⟩ := dropS_facts hw hf.hh hf.hhash
        have hnext := qNext_head hw hf.hq
        let L1 : Loc := { L with victim := some h }
        let L2 : Loc := { L1 with passive := qs.head? }
        let Lf : Loc := if r.stpMode = 3 then { L2 with rem := 0 } else L2
        have eblock : Eval program cancelOldBlock (mkSt s r L ts)
            (mkSt (dropS s l h) r Lf ts, .normal) := by
          have e1 : Eval program (.assign "victim" (v "passive")) (mkSt s r L ts)
              (mkSt s r L1 ts, .normal) := ev_victim hf.hp
          have e2 : Eval program (call1 "passive" .qNext [v "passive"]) (mkSt s r L1 ts)
              (mkSt s r L2 ts, .normal) := by
            have := ev_qNextP (P := program) (s := s) (r := r) (L := L1) (ts := ts) hf.hp hf.hlo hf.hqd
            rw [hnext] at this; exact this
          have e3 : Eval program (removeResting "best" "victim") (mkSt s r L2 ts)
              (mkSt (dropS s l h) r L2 ts, .normal) :=
            ev_remove hW.bestL (fun _ => by simp only [L2, L1]; lsimp) hw hf.hh hf.hhash hf.hll
          have e4 : Eval program (whenS (eqc "stp" STP_CANCEL_BOTH) (.assign "rem" (u 0)))
              (mkSt (dropS s l h) r L2 ts) (mkSt (dropS s l h) r Lf ts, .normal) := by
            by_cases h3 : r.stpMode = 3
            · simp only [Lf, if_pos h3]
              exact Eval.when_true (by rw [ev_stp_eq]; simp [h3, STP_CANCEL_BOTH]) ev_rem0
            · simp only [Lf, if_neg h3]
              exact Eval.when_false (by rw [ev_stp_eq]; simp [h3, STP_CANCEL_BOTH])
          exact Eval.block_cons_normal e1 (Eval.block_cons_normal e2 (Eval.block_cons_normal e3 e4
            (by simp)) (by simp)) (by simp)
        have eall : Eval program innerBody (mkSt s r L ts) (mkSt (dropS s l h) r Lf ts, .normal) :=
          Eval.ite_true (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_true hconf])
            (Eval.ite_false (by rw [ev_stp_eq]; simp [h1, STP_CANCEL_NEW])
              (Eval.ite_true (by rw [ev_oldBoth]; simp [h23]) eblock))
        have hinv := invM_drop hW.inv hW.mem hf.hh hv' hw' hcnt hlu
        obtain ⟨hmem', hbest'⟩ := best_frame hfr hW.mem hW.best
        have hpop : sideL (popHead st.book (contraT isBuy)) (contraT isBuy) =
            { L0 with orders := os } :: R := by simp [hf.hside, hf.hL0]
        have hbook : bookView (absBook (view (dropS s l h))) =
            bookView (popHead st.book (contraT isBuy)) := by
          rw [hv']
          exact book_step hw (hv' ▸ hw') hfr hW.mem hW.best hW.book hf.hside hpop
            (fun t' ht' => sideL_setSideL_ne ht') (by simp [popHead])
            (view_drop hw hf.hq hf.hlp hf.hos)
        have hq' : (view (dropS s l h)).queue l = qs := by
          rw [hv']; simp only [dropDb, upd_same, hf.hq, List.erase_cons_head]
        by_cases h3 : r.stpMode = 3
        · simp only [if_pos h3, Option.some.injEq] at hs
          subst hs
          have hLf : Lf = { L2 with rem := 0 } := by simp only [Lf, if_pos h3]
          refine ⟨dropS s l h, Lf, by dsimp only; rw [htr]; exact eall, ?_⟩
          rw [hLf]
          exact ⟨hinv, hv' ▸ hmem', hv' ▸ hbest', hbook, rfl, hW.stop, rfl, hW.bestL,
            fun e => absurd rfl e⟩
        · simp only [if_neg h3, Option.some.injEq] at hs
          subst hs
          have hLf : Lf = L2 := by simp only [Lf, if_neg h3]
          refine ⟨dropS s l h, Lf, by dsimp only; rw [htr]; exact eall, ?_⟩
          rw [hLf]
          exact ⟨hinv, hv' ▸ hmem', hv' ▸ hbest', hbook, hW.rem, hW.stop, rfl, hW.bestL,
            fun _ => by show qs.head? = _; rw [hq']⟩
      · -- DECREMENT
        rw [if_neg h23] at hs
        have K := wcore hw hf
        have hh1 : h ∈ (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue l := by
          rw [K.q1]; exact List.mem_cons_self
        have hcnt1 := count_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
        have hlu1 := levelsUsed_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
        rw [← hW.rem, hf.rv.rem, ← K.premN, ← K.remN] at hs
        have e1 := ev_min (s := s) (r := r) (L := L) (ts := ts) hf.hp hf.hlo hf.hread
        have e2 := ev_subRem (P := program) (s := s) (r := r) (ts := ts)
          (L := { L with fill := umin L.rem row.remaining }) K.fle
        have e3 := ev_prem (P := program) (s := s) (r := r) (ts := ts)
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining })
          hf.hp hf.hlo hf.hread K.fler
        have e4 := ev_setRem (P := program) (s := s) (r := r) (ts := ts)
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                         prem := row.remaining - umin L.rem row.remaining })
          hf.hp hf.hlo hf.hread

        have e5 := ev_qNextN (P := program)
          (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
          (r := r) (ts := ts)
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                         prem := row.remaining - umin L.rem row.remaining })
          hf.hp K.lo1 K.qd1
        rw [K.next1] at e5
        have ite_to : ∀ {st1 : St S},
            Eval program (Stmt.block decStmts) (mkSt s r L ts) (st1, .normal) →
            Eval program innerBody (mkSt s r L ts) (st1, .normal) := fun hb =>
          Eval.ite_true (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_true hconf])
            (Eval.ite_false (by rw [ev_stp_eq]; simp only [STP_CANCEL_NEW]; rw [decide_eq_false h1])
              (Eval.ite_false (by rw [ev_oldBoth, decide_eq_false h23]) hb))
        by_cases hz : row.remaining - umin L.rem row.remaining = 0
        · rw [if_pos (by rw [hz]; rfl)] at hs
          simp only [Option.some.injEq] at hs; subst hs
          obtain ⟨hv2, hw2, hc2, hl2, -⟩ := dropS_facts K.w1 hh1 K.hash1
          rw [K.v1, dropDb_setRem] at hv2
          have e6 := ev_premWhen_zero (P := program) (r := r) (ts := ts)
            (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                           prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
            hz hW.bestL hf.hp K.w1 hh1 K.hash1 K.ll1
          have e7 := ev_passiveNext (P := program)
            (s := dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) l h)
            (r := r) (ts := ts)
            (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                           prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
          refine ⟨_, _, by dsimp only; rw [htr]; exact ite_to (Eval.block_cons_normal e1
            (Eval.block_cons_normal e2 (Eval.block_cons_normal e3 (Eval.block_cons_normal e4
            (Eval.block_cons_normal e5 (Eval.block_cons_normal e6 e7 (by simp)) (by simp)) (by simp))
            (by simp)) (by simp)) (by simp)), ?_⟩
          obtain ⟨hmem', hbest'⟩ := best_frame hfr hW.mem hW.best
          have hq' : (view (dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) l h)).queue l = qs := by
            rw [hv2]; simp only [dropDb, upd_same, hf.hq, List.erase_cons_head]
          refine ⟨invM_drop hW.inv hW.mem hf.hh hv2 hw2 (by rw [← hcnt1]; exact hc2)
              (by rw [hl2, hlu1]), hv2 ▸ hmem', hv2 ▸ hbest', ?_, rfl, hW.stop, rfl, hW.bestL,
            fun _ => by show qs.head? = _; rw [hq']⟩
          rw [hv2]
          exact book_step hw (hv2 ▸ hw2) hfr hW.mem hW.best hW.book hf.hside
            (by simp [hf.hside, hf.hL0]) (fun t' ht' => by simp [popHead, setHeadRem, sideL_setSideL_ne ht'])
            (by simp [popHead, setHeadRem]) (view_drop hw hf.hq hf.hlp hf.hos)
        · rw [if_neg (fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl)))] at hs
          simp only [Option.some.injEq] at hs; subst hs
          have hr0 := K.part hz
          have hp0 : 0 < row.remaining - umin L.rem row.remaining := by
            rw [UInt64.lt_iff_toNat_lt]
            have : (row.remaining - umin L.rem row.remaining).toNat ≠ 0 :=
              fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
            simp; omega
          have e6 := ev_premWhen_pos (P := program) (r := r) (ts := ts)
            (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
            (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                           prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? }) hz
          have e7 := ev_passiveNext (P := program)
            (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
            (r := r) (ts := ts)
            (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                           prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
          refine ⟨_, _, by dsimp only; rw [htr]; exact ite_to (Eval.block_cons_normal e1
            (Eval.block_cons_normal e2 (Eval.block_cons_normal e3 (Eval.block_cons_normal e4
            (Eval.block_cons_normal e5 (Eval.block_cons_normal e6 e7 (by simp)) (by simp)) (by simp))
            (by simp)) (by simp)) (by simp)), ?_⟩
          have hfs : Frame l (view s) (setRemDb (view s) h { row with remaining := row.remaining - umin L.rem row.remaining }) :=
            frame_setRem hw hf.hh
          obtain ⟨hmem', hbest'⟩ := best_frame hfs hW.mem hW.best
          refine ⟨invM_setRem hW.inv hW.mem hf.hh hf.hrow hp0 K.prle K.v1 K.w1 hcnt1 hlu1,
            K.v1 ▸ hmem', K.v1 ▸ hbest', ?_, rfl, hW.stop, rfl, hW.bestL, fun e => absurd hr0 e⟩
          rw [K.v1]
          exact book_step hw (K.v1 ▸ K.w1) hfs hW.mem hW.best hW.book hf.hside
            (by simp [hf.hside, hf.hL0]) (fun t' ht' => by simp [setHeadRem, sideL_setSideL_ne ht'])
            (by simp [setHeadRem])
            (view_setRem hw hf.hq hf.hlp hf.hos hf.hpv _ _ rfl)
  · -- a fill
    rw [if_neg (fun e => hconf ((acct_iff hf.rv).mp e))] at hs
    have K := wcore hw hf
    have hh1 : h ∈ (view (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })).queue l := by
      rw [K.q1]; exact List.mem_cons_self
    have hcnt1 := count_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
    have hlu1 := levelsUsed_writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }
    rw [← hW.rem, hf.rv.rem, ← K.premN, ← K.remN] at hs
    have e1 := ev_min (s := s) (r := r) (L := L) (ts := ts) hf.hp hf.hlo hf.hread
    have e2 := ev_subRem (P := program) (s := s) (r := r) (ts := ts)
      (L := { L with fill := umin L.rem row.remaining }) K.fle
    have e3 := ev_prem (P := program) (s := s) (r := r) (ts := ts)
      (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining })
      hf.hp hf.hlo hf.hread K.fler
    have e4 := ev_setRem (P := program) (s := s) (r := r) (ts := ts)
      (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                     prem := row.remaining - umin L.rem row.remaining })
      hf.hp hf.hlo hf.hread

    obtain ⟨lrow, hlrow⟩ : ∃ lrow, readLevel s l = some lrow := by
      have := hf.hll
      rw [readLevel_law]
      simp only [liveL] at this
      exact Option.isSome_iff_exists.mp this
    have hlp' : L0.price = lrow.price.toNat := by
      rw [hf.hlp]; rw [readLevel_law] at hlrow; simp [Db.levelPrice, hlrow]
    rw [← K.fN] at hs
    split at hs
    · rename_i hlenW
      have hlen : ts.length < capacity (S := S) + 1 := by
        rw [hW.trades, List.length_map]; exact hlenW
      let T := toNatTrade row.id r.id lrow.price (umin L.rem row.remaining)
      have hT : tradeObs (mkTrade { cap := capacity (S := S), r := r, isBuy := isBuy } p L0.price
          (umin L.rem row.remaining).toNat) = T := by
        simp only [tradeObs, mkTrade, T, toNatTrade, TradeObs.mk.injEq]
        exact ⟨hf.rv.id, by first | rfl | trivial, hlp', by first | rfl | trivial⟩
      have e4b := ev_emit (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
        (r := r) (ts := ts)
        (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                       prem := row.remaining - umin L.rem row.remaining })
        hcap hf.hp K.lo1 K.rd1 hW.bestL K.ll1 (by rw [K.rl1]; exact hlrow) hlen
      have e5 := ev_qNextN (P := program)
        (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
        (r := r) (ts := ts ++ [T])
        (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                       prem := row.remaining - umin L.rem row.remaining })
        hf.hp K.lo1 K.qd1
      rw [K.next1] at e5
      have ite_to : ∀ {st1 : St S},
          Eval program (Stmt.block fillStmts) (mkSt s r L ts) (st1, .normal) →
          Eval program innerBody (mkSt s r L ts) (st1, .normal) := fun hb =>
        Eval.ite_false (by rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_false hconf]) hb
      have htr' : (st.trades ++ [mkTrade { cap := capacity (S := S), r := r, isBuy := isBuy } p L0.price
          (umin L.rem row.remaining).toNat]).map tradeObs = ts ++ [T] := by
        rw [List.map_append, htr, List.map_singleton, hT]
      by_cases hz : row.remaining - umin L.rem row.remaining = 0
      · rw [if_pos (by rw [hz]; rfl)] at hs
        simp only [Option.some.injEq] at hs; subst hs
        obtain ⟨hv2, hw2, hc2, hl2, -⟩ := dropS_facts K.w1 hh1 K.hash1
        rw [K.v1, dropDb_setRem] at hv2
        have e6 := ev_premWhen_zero (P := program) (r := r) (ts := ts ++ [T])
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                         prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
          hz hW.bestL hf.hp K.w1 hh1 K.hash1 K.ll1
        have e7 := ev_passiveNext (P := program)
          (s := dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) l h)
          (r := r) (ts := ts ++ [T])
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                         prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
        refine ⟨_, _, by dsimp only; rw [htr']; exact ite_to (Eval.block_cons_normal e1
          (Eval.block_cons_normal e2 (Eval.block_cons_normal e3 (Eval.block_cons_normal e4
          (Eval.block_cons_normal e4b (Eval.block_cons_normal e5 (Eval.block_cons_normal e6 e7
          (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)), ?_⟩
        obtain ⟨hmem', hbest'⟩ := best_frame hfr hW.mem hW.best
        have hq' : (view (dropS (writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining }) l h)).queue l = qs := by
          rw [hv2]; simp only [dropDb, upd_same, hf.hq, List.erase_cons_head]
        refine ⟨invM_drop hW.inv hW.mem hf.hh hv2 hw2 (by rw [← hcnt1]; exact hc2)
            (by rw [hl2, hlu1]), hv2 ▸ hmem', hv2 ▸ hbest', ?_, rfl, hW.stop, rfl, hW.bestL,
          fun _ => by show qs.head? = _; rw [hq']⟩
        rw [hv2]
        exact book_step hw (hv2 ▸ hw2) hfr hW.mem hW.best hW.book hf.hside
          (by simp [hf.hside, hf.hL0]) (fun t' ht' => by simp [popHead, setHeadRem, sideL_setSideL_ne ht'])
          (by simp [popHead, setHeadRem]) (view_drop hw hf.hq hf.hlp hf.hos)
      · rw [if_neg (fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl)))] at hs
        simp only [Option.some.injEq] at hs; subst hs
        have hr0 := K.part hz
        have hp0 : 0 < row.remaining - umin L.rem row.remaining := by
          rw [UInt64.lt_iff_toNat_lt]
          have : (row.remaining - umin L.rem row.remaining).toNat ≠ 0 :=
            fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
          simp; omega
        have e6 := ev_premWhen_pos (P := program) (r := r) (ts := ts ++ [T])
          (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                         prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? }) hz
        have e7 := ev_passiveNext (P := program)
          (s := writeOrder s h { row with remaining := row.remaining - umin L.rem row.remaining })
          (r := r) (ts := ts ++ [T])
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                         prem := row.remaining - umin L.rem row.remaining, nextp := qs.head? })
        refine ⟨_, _, by dsimp only; rw [htr']; exact ite_to (Eval.block_cons_normal e1
          (Eval.block_cons_normal e2 (Eval.block_cons_normal e3 (Eval.block_cons_normal e4
          (Eval.block_cons_normal e4b (Eval.block_cons_normal e5 (Eval.block_cons_normal e6 e7
          (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)), ?_⟩
        have hfs : Frame l (view s) (setRemDb (view s) h { row with remaining := row.remaining - umin L.rem row.remaining }) :=
          frame_setRem hw hf.hh
        obtain ⟨hmem', hbest'⟩ := best_frame hfs hW.mem hW.best
        refine ⟨invM_setRem hW.inv hW.mem hf.hh hf.hrow hp0 K.prle K.v1 K.w1 hcnt1 hlu1,
          K.v1 ▸ hmem', K.v1 ▸ hbest', ?_, rfl, hW.stop, rfl, hW.bestL, fun e => absurd hr0 e⟩
        rw [K.v1]
        exact book_step hw (K.v1 ▸ K.w1) hfs hW.mem hW.best hW.book hf.hside
          (by simp [hf.hside, hf.hL0]) (fun t' ht' => by simp [setHeadRem, sideL_setSideL_ne ht'])
          (by simp [setHeadRem])
          (view_setRem hw hf.hq hf.hlp hf.hos hf.hpv _ _ rfl)
    · cases hs

-- ============================================================================
-- The trap: the walk's `none` is the program's error
-- ============================================================================

theorem seq_through {P : Program} {a b : Stmt} {st st₁ : St S} {res : St S × Outcome}
    (ha : Eval P a st (st₁, .normal)) (h : Eval P (.seq a b) st res) : Eval P b st₁ res := by
  rcases Eval.seq_inv h with ⟨x, hx, hb⟩ | ⟨v, hv, -⟩
  · have := Eval.det ha hx; cases this; exact hb
  · have := Eval.det ha hv; cases this

/-- **The body's trap.** Where one walk iteration is `none` (the trade buffer
    is full), the program's inner body has no successful run. -/
theorem w_inner_body_trap (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {l : LevelH} {s : S}
    {L : Loc} {ts : List TradeObs} {st : State} (hW : WR r isBuy l s L ts st)
    (ht : innerTest (wctx S r isBuy) st = true) (hs : innerStep (wctx S r isBuy) st = none) :
    ∀ res, ¬ Eval program innerBody (mkSt s r L ts) res := by
  intro res hev
  have hw := hW.inv.wf
  have hrem : L.rem ≠ 0 := by
    intro e; simp [innerTest, ← hW.rem, e] at ht
  have hqne : (view s).queue l ≠ [] := by
    intro hq
    have := ev_innerCond_walk hW
    rw [ev_innerCond, hW.passive hrem, hq, ht] at this
    simp at this
  obtain ⟨h, qs, hq⟩ : ∃ h qs, (view s).queue l = h :: qs := by
    cases e : (view s).queue l with
    | nil => exact absurd e hqne
    | cons h qs => exact ⟨h, qs, rfl⟩
  obtain ⟨row, L0, R, p, os, hf⟩ := whead hW hrem hq
  unfold innerStep at hs
  rw [wctx_contra, tBest_eq, hf.hside] at hs
  simp only [List.head?_cons, qFirst, hf.hL0] at hs
  simp only [wctx] at hs
  by_cases hconf : r.account ≠ 0 ∧ r.account = row.account ∧ r.stpMode ≠ 0
  · rw [if_pos ((acct_iff hf.rv).mpr hconf)] at hs
    split at hs
    · cases hs
    · split at hs
      · split at hs <;> cases hs
      · cases hs
  · rw [if_neg (fun e => hconf ((acct_iff hf.rv).mp e))] at hs
    split at hs
    · cases hs
    · rename_i hlenW
      have K := wcore hw hf
      rcases Eval.ite_inv hev with ⟨hc, -⟩ | ⟨-, hb⟩
      · rw [ev_stpCond hf.hp hf.hlo hf.hread, decide_eq_false hconf] at hc; cases hc
      · simp only [fillStmts, Stmt.block] at hb
        have e1 := ev_min (s := s) (r := r) (L := L) (ts := ts) hf.hp hf.hlo hf.hread
        have e2 := ev_subRem (P := program) (s := s) (r := r) (ts := ts)
          (L := { L with fill := umin L.rem row.remaining }) K.fle
        have e3 := ev_prem (P := program) (s := s) (r := r) (ts := ts)
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining })
          hf.hp hf.hlo hf.hread K.fler
        have e4 := ev_setRem (P := program) (s := s) (r := r) (ts := ts)
          (L := { L with fill := umin L.rem row.remaining, rem := L.rem - umin L.rem row.remaining,
                         prem := row.remaining - umin L.rem row.remaining })
          hf.hp hf.hlo hf.hread
        have hemit := seq_through e4 (seq_through e3 (seq_through e2 (seq_through e1 hb)))
        rcases Eval.seq_inv hemit with ⟨x, hx, -⟩ | ⟨v, hv, -⟩
        · obtain ⟨cap, hc1, hc2⟩ := Eval.emit_inv hx
          rw [boundVal_trade hcap] at hc1; cases hc1
          simp only [mkSt] at hc2
          rw [hW.trades, List.length_map] at hc2
          exact hlenW hc2
        · obtain ⟨cap, hc1, hc2⟩ := Eval.emit_inv hv
          rw [boundVal_trade hcap] at hc1; cases hc1
          simp only [mkSt] at hc2
          rw [hW.trades, List.length_map] at hc2
          exact hlenW hc2

-- ============================================================================
-- The inner loop
-- ============================================================================

/-- **The inner loop, run by run.** Where the walk's inner loop with budget `n`
    ends in `st'`, the program's inner loop with budget `n` ends normally in a
    state related to `st'`. -/
theorem w_inner_run (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {l : LevelH} :
    ∀ (n : Nat) (st st' : State) (s : S) (L : Loc) (ts : List TradeObs),
      innerRun (wctx S r isBuy) n st = some st' → WR r isBuy l s L ts st →
      ∃ s' L', LoopRun program innerCond innerBody n (mkSt s r L ts)
          (mkSt s' r L' (st'.trades.map tradeObs), .normal) ∧
        WR r isBuy l s' L' (st'.trades.map tradeObs) st' := by
  intro n
  induction n with
  | zero =>
    intro st st' s L ts hrun hW
    unfold innerRun at hrun
    split at hrun
    · cases hrun
    · rename_i ht
      simp only [Option.some.injEq] at hrun; subst hrun
      refine ⟨s, L, ?_, by rw [← hW.trades]; exact hW⟩
      rw [← hW.trades]
      exact .stop (by rw [ev_innerCond_walk hW]; simpa using ht)
  | succ n ih =>
    intro st st' s L ts hrun hW
    unfold innerRun at hrun
    split at hrun
    · rename_i ht
      cases hs : innerStep (wctx S r isBuy) st with
      | none => rw [hs] at hrun; cases hrun
      | some st1 =>
        rw [hs] at hrun
        simp only [Option.bind_some] at hrun
        obtain ⟨s1, L1, hev, hW1⟩ := w_inner_body hcap hW ht hs
        obtain ⟨s', L', hrun', hW'⟩ := ih st1 st' s1 L1 _ hrun hW1
        exact ⟨s', L', .step (by rw [ev_innerCond_walk hW, ht]) hev hrun', hW'⟩
    · rename_i ht
      simp only [Option.some.injEq] at hrun; subst hrun
      refine ⟨s, L, ?_, by rw [← hW.trades]; exact hW⟩
      rw [← hW.trades]
      exact .stop (by rw [ev_innerCond_walk hW]; simpa using ht)

/-- **The inner loop's trap, run by run.** Where the walk's inner loop with
    budget `n` is `none` (budget spent with the test still true, or a full
    trade buffer), the program's inner loop with budget `n` has no run. -/
theorem w_inner_run_none (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {l : LevelH} :
    ∀ (n : Nat) (st : State) (s : S) (L : Loc) (ts : List TradeObs),
      innerRun (wctx S r isBuy) n st = none → WR r isBuy l s L ts st →
      ∀ res, ¬ LoopRun program innerCond innerBody n (mkSt s r L ts) res := by
  intro n
  induction n with
  | zero =>
    intro st s L ts hrun hW res hl
    unfold innerRun at hrun
    split at hrun
    · rename_i ht
      cases hl with
      | stop hc => rw [ev_innerCond_walk hW, ht] at hc; cases hc
    · cases hrun
  | succ n ih =>
    intro st s L ts hrun hW res hl
    unfold innerRun at hrun
    split at hrun
    · rename_i ht
      have hct : evalExpr (mkSt s r L ts) innerCond = .ok (.bool true) := by
        rw [ev_innerCond_walk hW, ht]
      cases hs : innerStep (wctx S r isBuy) st with
      | none =>
        have trap := w_inner_body_trap hcap hW ht hs
        cases hl with
        | stop hc => rw [hct] at hc; cases hc
        | step _ hb _ => exact trap _ hb
        | ret _ hb => exact trap _ hb
      | some st1 =>
        rw [hs] at hrun
        simp only [Option.bind_some] at hrun
        obtain ⟨s1, L1, hev, hW1⟩ := w_inner_body hcap hW ht hs
        cases hl with
        | stop hc => rw [hct] at hc; cases hc
        | step _ hb hrest =>
          have := Eval.det hev hb; cases this
          exact ih st1 s1 L1 _ hrun hW1 _ hrest
        | ret _ hb => have := Eval.det hev hb; cases this
    · cases hrun

theorem boundVal_capPlus1' (hcap : CapOk S) :
    boundVal (S := S) (.capPlus 1) = .ok (capacity (S := S) + 1) := by
  unfold CapOk at hcap
  simp [boundVal, hcap]

/-- **The inner loop statement.** At the program's bound `capacity + 1`, the
    inner loop statement ends normally in a state related to the walk's
    `innerRun` result when that is `some`, and has no run at all when it is
    `none` (the program's `me_trap(2)` or `me_trap(3)`). -/
theorem w_inner_loop (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {l : LevelH} {s : S}
    {L : Loc} {ts : List TradeObs} {st : State} (hW : WR r isBuy l s L ts st) :
    (∀ st', innerRun (wctx S r isBuy) (capacity (S := S) + 1) st = some st' →
      ∃ s' L', Eval program (.loop (.capPlus 1) innerCond innerBody) (mkSt s r L ts)
          (mkSt s' r L' (st'.trades.map tradeObs), .normal) ∧
        WR r isBuy l s' L' (st'.trades.map tradeObs) st') ∧
    (innerRun (wctx S r isBuy) (capacity (S := S) + 1) st = none →
      ∀ res, ¬ Eval program (.loop (.capPlus 1) innerCond innerBody) (mkSt s r L ts) res) := by
  refine ⟨fun st' hrun => ?_, fun hrun res hev => ?_⟩
  · obtain ⟨s', L', hl, hW'⟩ := w_inner_run hcap _ st st' s L ts hrun hW
    exact ⟨s', L', Eval.loop (boundVal_capPlus1' hcap) hl, hW'⟩
  · exact w_inner_run_none hcap _ st s L ts hrun hW res
      (loopRun_of_eval (boundVal_capPlus1' hcap) hev)

end Walk

import Matcher.Refines

/-!
# Phase 4: cancel refines `processB`

Cancelling a resting order runs, in the matcher, `qRemove`, `hashRemove`,
`orderFree`, and when the level empties, `tRemove` and `levelFree`. The store
view it reaches is `cancelDb` (a pure function of the view before). This file
shows that `absBook (cancelDb …)` has the same `bookView` as the spec's
`cancelOrder`, that `Inv` holds again, and assembles `Refines` for cancel.

The book-level argument: the side the order is on is a price-sorted list in
both books; the two are permutations of each other level by level, so they are
equal (`List.Perm.eq_of_pairwise`). Queue positions shift when an order leaves,
but `bookView` does not see positions.
-/

namespace MatcherCancel

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines

-- ============================================================================
-- Views of the decoded book
-- ============================================================================

/-- The row of a handle, as `absQueue` reads it. -/
def rowOf (db : Db) (h : OrderH) : OrderRow := (db.orders h).getD OrderRow.dflt

theorem absQueue_views (db : Db) (t : Tree) :
    ∀ (i : Nat) (hs : List OrderH), (absQueue db t i hs).map orderView =
      hs.map fun h => orderView (restingOrder t (rowOf db h) 0)
  | _, [] => rfl
  | i, _ :: hs => by
    simp only [absQueue, List.map_cons, absQueue_views db t (i + 1) hs]
    rfl

theorem absQueue_congr {db db' : Db} {t : Tree} :
    ∀ (i : Nat) (hs : List OrderH), (∀ x ∈ hs, db'.orders x = db.orders x) →
      absQueue db' t i hs = absQueue db t i hs
  | _, [], _ => rfl
  | i, x :: hs, h => by
    simp only [absQueue]
    rw [h x List.mem_cons_self, absQueue_congr (i + 1) hs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem absLevel_congr {db db' : Db} {t : Tree} {l : LevelH}
    (hq : db'.queue l = db.queue l) (ho : ∀ x ∈ db.queue l, db'.orders x = db.orders x)
    (hp : db'.levelPrice l = db.levelPrice l) : absLevel db' t l = absLevel db t l := by
  simp only [absLevel, hq, hp, absQueue_congr 0 _ ho]

/-- `filterMap` against `filter`, seen through a view. -/
theorem filterMap_view {α β γ : Type} (T : List α) (G : α → Option β) (F : α → β) (V : β → γ)
    (p : α → Bool) (h : ∀ x ∈ T, (G x).map V = if p x then some (V (F x)) else none) :
    (T.filterMap G).map V = (T.filter p).map (V ∘ F) := by
  induction T with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hg : G x with
    | none =>
      rw [hg] at hx
      cases hp : p x
      · simp [hg, hp, ih']
      · simp [hp] at hx
    | some y =>
      rw [hg] at hx
      cases hp : p x
      · simp [hp] at hx
      · simp only [hp, if_true, Option.map_some, Option.some.injEq] at hx
        simp [hg, hp, ih', hx]

theorem prioB_asymm {t : Tree} {p q : Nat} (h₁ : prioB t p q = true) (h₂ : prioB t q p = true) :
    False := by
  cases t <;> simp [prioB] at h₁ h₂ <;> omega

/-- Two price-sorted sides that are permutations of each other have the same
    view. -/
theorem views_eq_of_perm {t : Tree} {L₁ L₂ : List PriceLevel}
    (h₁ : L₁.Pairwise fun a b => prioB t a.price b.price = true)
    (h₂ : L₂.Pairwise fun a b => prioB t a.price b.price = true)
    (hp : (L₁.map levelView).Perm (L₂.map levelView)) :
    L₁.map levelView = L₂.map levelView := by
  apply List.Perm.eq_of_pairwise (le := fun a b => prioB t a.price b.price = true)
  · intro a b _ _ hab hba; exact (prioB_asymm hab hba).elim
  · exact List.pairwise_map.mpr (h₁.imp id)
  · exact List.pairwise_map.mpr (h₂.imp id)
  · exact hp

-- ============================================================================
-- The store view after a cancel
-- ============================================================================

/-- The store view after cancelling order `h` from level `l` of tree `t0`:
    `qRemove`, `hashRemove`, `orderFree`, and when the level empties,
    `tRemove` and `levelFree`. -/
def cancelDb (db : Db) (t0 : Tree) (l : LevelH) (h : OrderH) : Db :=
  if ((db.queue l).erase h).isEmpty then
    { db with queue := upd db.queue l ((db.queue l).erase h), hash := db.hash.erase h,
              orders := upd db.orders h none, oLive := db.oLive.erase h,
              tree := upd db.tree t0 ((db.tree t0).erase l), levels := upd db.levels l none,
              lLive := db.lLive.erase l }
  else
    { db with queue := upd db.queue l ((db.queue l).erase h), hash := db.hash.erase h,
              orders := upd db.orders h none, oLive := db.oLive.erase h }

/-- On a well-formed store with the client invariant, an id names at most one
    resting order. -/
theorem resting_id_unique {db : Db} (hw : db.WF) (hc : ClientInv db)
    {t t' : Tree} {l l' : LevelH} {h h' : OrderH}
    (_hl : l ∈ db.tree t) (hh : h ∈ db.queue l) (_hl' : l' ∈ db.tree t') (hh' : h' ∈ db.queue l')
    (he : (rowOf db h').id.toNat = (rowOf db h).id.toNat) : h' = h := by
  have hash1 := (hc.hash_iff_queued h).mpr ⟨l, hh⟩
  have hash2 := (hc.hash_iff_queued h').mpr ⟨l', hh'⟩
  have live1 := (hw.queue_live l h hh).1
  have live2 := (hw.queue_live l' h' hh').1
  apply hw.hash_ids _ hash2 _ hash1
  have r1 : db.orderId h = (rowOf db h).id := by
    cases ho : db.orders h with
    | none => simp [Db.orderLive, ho] at live1
    | some row => simp [Db.orderId, rowOf, ho]
  have r2 : db.orderId h' = (rowOf db h').id := by
    cases ho : db.orders h' with
    | none => simp [Db.orderLive, ho] at live2
    | some row => simp [Db.orderId, rowOf, ho]
  rw [r1, r2]
  exact UInt64.toNat_inj.mp he

theorem restingOrder_id (t : Tree) (r : OrderRow) (i : Nat) : (restingOrder t r i).id = r.id.toNat := rfl

/-- Filtering a queue by id, seen through the view. -/
theorem absQueue_filter_views (db : Db) (t : Tree) (n : Nat) :
    ∀ (i : Nat) (hs : List OrderH),
      ((absQueue db t i hs).filter (fun o => o.id != n)).map orderView =
        (hs.filter (fun y => (rowOf db y).id.toNat != n)).map
          (fun y => orderView (restingOrder t (rowOf db y) 0))
  | _, [] => rfl
  | i, y :: hs => by
    simp only [absQueue, List.filter_cons, restingOrder_id]
    have ih := absQueue_filter_views db t n (i + 1) hs
    split
    · rename_i hy
      have : ((rowOf db y).id.toNat != n) = true := by simpa [rowOf] using hy
      simp only [this, if_true, List.map_cons, ih]
      rfl
    · rename_i hy
      have : ((rowOf db y).id.toNat != n) = false := by simpa [rowOf] using hy
      simp only [this, Bool.false_eq_true, if_false, ih]

-- ============================================================================
-- The cancelled side
-- ============================================================================

/-- One step of `removeLevelOrder`. -/
def dropStep (n : OrderId) (lv : PriceLevel) : Option PriceLevel :=
  if (lv.orders.filter (·.id != n)).isEmpty then none
  else some { lv with orders := lv.orders.filter (·.id != n) }

theorem removeLevelOrder_eq (L : List PriceLevel) (n : OrderId) :
    removeLevelOrder L n = L.filterMap (dropStep n) := rfl

section CancelSide

variable {db : Db} {t0 : Tree} {l : LevelH} {h : OrderH}

theorem cancelDb_queue (x : LevelH) :
    (cancelDb db t0 l h).queue x = upd db.queue l ((db.queue l).erase h) x := by
  unfold cancelDb; split <;> rfl

theorem cancelDb_orders (y : OrderH) :
    (cancelDb db t0 l h).orders y = upd db.orders h none y := by
  unfold cancelDb; split <;> rfl

theorem cancelDb_levels_of_ne {x : LevelH} (hx : x ≠ l) :
    (cancelDb db t0 l h).levels x = db.levels x := by
  unfold cancelDb; split
  · exact upd_other _ _ hx
  · rfl

theorem cancelDb_levels_of_nonempty (hne : ((db.queue l).erase h).isEmpty = false) (x : LevelH) :
    (cancelDb db t0 l h).levels x = db.levels x := by
  unfold cancelDb; simp [hne]

theorem cancelDb_tree (hw : db.WF) :
    (cancelDb db t0 l h).tree t0 =
      (db.tree t0).filter (fun x => !(((db.queue l).erase h).isEmpty && x == l)) := by
  unfold cancelDb
  split
  · rename_i he
    simp only [upd_same, he, Bool.true_and]
    rw [(hw.tree_nodup t0).erase_eq_filter]
    rfl
  · rename_i he
    simp only [Bool.not_eq_true] at he
    simp only [he, Bool.false_and, Bool.not_false]
    exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm

theorem cancelDb_tree_other {t : Tree} (ht : t ≠ t0) :
    (cancelDb db t0 l h).tree t = db.tree t := by
  unfold cancelDb; split
  · exact upd_other _ _ ht
  · rfl

/-- **The cancelled side**: through the view, the side of the cancelled order
    is exactly the spec's `removeLevelOrder` of the old side. -/
theorem cancel_side_view (hw : db.WF) (hc : ClientInv db) (hl : l ∈ db.tree t0)
    (hh : h ∈ db.queue l) (hw' : (cancelDb db t0 l h).WF) :
    (absSide (cancelDb db t0 l h) t0).map levelView =
      (removeLevelOrder (absSide db t0) (rowOf db h).id.toNat).map levelView := by
  have hnd : (db.queue l).Nodup := hw.queue_nodup l
  -- the order's id belongs to it alone
  have huniq : ∀ {t x y}, x ∈ db.tree t → y ∈ db.queue x →
      (rowOf db y).id.toNat = (rowOf db h).id.toNat → y = h :=
    fun hx hy he => resting_id_unique hw hc hl hh hx hy he
  have hqfilter : (db.queue l).filter (fun y => (rowOf db y).id.toNat != (rowOf db h).id.toNat) =
      (db.queue l).erase h := by
    rw [hnd.erase_eq_filter]
    apply List.filter_congr
    intro y hy
    by_cases hyh : y = h
    · simp [hyh]
    · have : (rowOf db y).id.toNat ≠ (rowOf db h).id.toNat :=
        fun he => hyh (huniq hl hy he)
      rw [bne_iff_ne.mpr this, bne_iff_ne.mpr hyh]
  -- the pointwise step
  have hpt : ∀ x ∈ db.tree t0,
      (dropStep (rowOf db h).id.toNat (absLevel db t0 x)).map levelView =
        if !(((db.queue l).erase h).isEmpty && x == l) then
          some (levelView (absLevel (cancelDb db t0 l h) t0 x)) else none := by
    intro x hx
    by_cases hxl : x = l
    · subst hxl
      have hviews := absQueue_filter_views db t0 (rowOf db h).id.toNat 0 (db.queue x)
      rw [hqfilter] at hviews
      have hrow : ∀ y ∈ (db.queue x).erase h,
          orderView (restingOrder t0 (rowOf (cancelDb db t0 x h) y) 0) =
            orderView (restingOrder t0 (rowOf db y) 0) := by
        intro y hy
        have hyh : y ≠ h := fun e => by subst e; exact hnd.not_mem_erase hy
        simp [rowOf, cancelDb_orders, upd_other _ _ hyh]
      by_cases he : ((db.queue x).erase h).isEmpty = true
      · have hnil : (db.queue x).erase h = [] := List.isEmpty_iff.mp he
        rw [hnil] at hviews
        have : ((absLevel db t0 x).orders.filter (·.id != (rowOf db h).id.toNat)) = [] := by
          simpa [absLevel] using hviews
        simp [dropStep, this, he]
      · have hne : ((db.queue x).erase h).isEmpty = false := by simpa using he
        have hlen := congrArg List.length hviews
        simp only [List.length_map] at hlen
        have hfne : ((absLevel db t0 x).orders.filter (·.id != (rowOf db h).id.toNat)).isEmpty = false := by
          have hpos : 0 < ((db.queue x).erase h).length := by
            cases hq : (db.queue x).erase h with
            | nil => simp [hq] at hne
            | cons _ _ => simp
          cases hf : (absLevel db t0 x).orders.filter (·.id != (rowOf db h).id.toNat) with
          | nil => simp only [absLevel] at hf; rw [hf] at hlen; simp at hlen; omega
          | cons _ _ => rfl
        have hd : dropStep (rowOf db h).id.toNat (absLevel db t0 x) =
            some { absLevel db t0 x with
              orders := (absLevel db t0 x).orders.filter (·.id != (rowOf db h).id.toNat) } := by
          unfold dropStep; rw [if_neg (by simp [hfne])]
        have hp : (!(((db.queue x).erase h).isEmpty && x == x)) = true := by simp [hne]
        rw [hd, if_pos hp, Option.map_some]
        simp only [levelView, absLevel, cancelDb_queue, upd_same, Option.some.injEq,
          LevelView.mk.injEq]
        refine ⟨by simp only [Db.levelPrice, cancelDb_levels_of_nonempty hne], ?_⟩
        rw [absQueue_views, hviews]
        exact (List.map_congr_left hrow).symm
    · have hxq : ∀ y ∈ db.queue x, y ≠ h := by
        intro y hy e; subst e; exact hxl (hw.queue_unique _ _ _ hy hh)
      have hkeep : ∀ o ∈ (absLevel db t0 x).orders, (o.id != (rowOf db h).id.toNat) = true := by
        intro o ho
        obtain ⟨y, hy, j, -, -, rfl⟩ := mem_absQueue ho
        simp only [restingOrder_id, bne_iff_ne, ne_eq]
        exact fun he => hxq y hy (huniq hx hy he)
      have hfilt : (absLevel db t0 x).orders.filter (·.id != (rowOf db h).id.toNat) =
          (absLevel db t0 x).orders := List.filter_eq_self.mpr hkeep
      have hne : (absLevel db t0 x).orders.isEmpty = false := by
        have := hc.level_nonempty t0 x hx
        simp only [absLevel]
        cases hq : db.queue x with
        | nil => exact absurd hq this
        | cons _ _ => simp [absQueue]
      have hcongr : absLevel (cancelDb db t0 l h) t0 x = absLevel db t0 x := by
        apply absLevel_congr
        · rw [cancelDb_queue, upd_other _ _ hxl]
        · intro y hy; rw [cancelDb_orders, upd_other _ _ (hxq y hy)]
        · simp only [Db.levelPrice, cancelDb_levels_of_ne hxl]
      have hp : (!(((db.queue l).erase h).isEmpty && x == l)) = true := by simp [hxl]
      have hd : dropStep (rowOf db h).id.toNat (absLevel db t0 x) = some (absLevel db t0 x) := by
        unfold dropStep; rw [hfilt, if_neg (by simp [hne])]
      rw [hd, if_pos hp, Option.map_some, hcongr]
  apply views_eq_of_perm (t := t0)
  · exact absSide_pairwise hw' t0
  · exact removeLevelOrder_pairwise (R := fun p q => prioB t0 p q = true) (absSide_pairwise hw t0)
  · have p1 : ((absSide (cancelDb db t0 l h) t0).map levelView).Perm
        (((cancelDb db t0 l h).tree t0).map (absLevel (cancelDb db t0 l h) t0) |>.map levelView) :=
      (sortLevels_perm t0 _).map _
    have p2 : ((removeLevelOrder (absSide db t0) (rowOf db h).id.toNat).map levelView).Perm
        (((db.tree t0).filterMap (fun x => dropStep (rowOf db h).id.toNat (absLevel db t0 x))).map
          levelView) := by
      rw [removeLevelOrder_eq]
      have := (((sortLevels_perm t0 ((db.tree t0).map (absLevel db t0))).filterMap
        (dropStep (rowOf db h).id.toNat)).map levelView)
      rw [List.filterMap_map] at this
      exact this
    have heq := filterMap_view (db.tree t0) (fun x => dropStep (rowOf db h).id.toNat (absLevel db t0 x))
      (absLevel (cancelDb db t0 l h) t0) levelView _ hpt
    rw [heq, ← cancelDb_tree hw] at p2
    rw [List.map_map] at p1
    exact p1.trans p2.symm

end CancelSide

-- ============================================================================
-- The other side, and the spec's cancel
-- ============================================================================

section CancelSpec

variable {db : Db} {t0 : Tree} {l : LevelH} {h : OrderH}

theorem tree_ne_of_mem {t t' : Tree} (hw : db.WF) {x y : LevelH} (hx : x ∈ db.tree t)
    (hy : y ∈ db.tree t') (hne : t ≠ t') : x ≠ y := by
  intro e; subst e
  cases t <;> cases t' <;> first | exact absurd rfl hne | exact (hw.tree_disjoint _ hx hy).elim | exact (hw.tree_disjoint _ hy hx).elim

theorem cancel_other_side (hw : db.WF) (hl : l ∈ db.tree t0) (hh : h ∈ db.queue l)
    {t : Tree} (ht : t ≠ t0) : absSide (cancelDb db t0 l h) t = absSide db t := by
  unfold absSide
  rw [cancelDb_tree_other ht]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hxl : x ≠ l := tree_ne_of_mem hw hx hl ht
  apply absLevel_congr
  · rw [cancelDb_queue, upd_other _ _ hxl]
  · intro y hy
    have hyh : y ≠ h := fun e => by subst e; exact hxl (hw.queue_unique _ _ _ hy hh)
    rw [cancelDb_orders, upd_other _ _ hyh]
  · simp only [Db.levelPrice, cancelDb_levels_of_ne hxl]

theorem side_has_id (t : Tree) (n : Nat) :
    (∃ lv ∈ absSide db t, ∃ o ∈ lv.orders, o.id = n) ↔
      ∃ x ∈ db.tree t, ∃ y ∈ db.queue x, (rowOf db y).id.toNat = n := by
  constructor
  · rintro ⟨lv, hlv, o, ho, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_absSide hlv
    obtain ⟨y, hy, j, -, -, rfl⟩ := mem_absQueue ho
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, e⟩
    have : (rowOf db y).id.toNat ∈ (absQueue db t 0 (db.queue x)).map Order.id := by
      rw [absQueue_ids]; exact List.mem_map_of_mem hy
    obtain ⟨o, ho, eo⟩ := List.mem_map.mp this
    exact ⟨absLevel db t x, mem_sortLevels.mpr (List.mem_map_of_mem hx), o, ho, eo.trans e⟩

theorem findSome_side_some {levels : List PriceLevel} {sd : Side} {n : OrderId} {r : Side × Order}
    (h : (levels.findSome? fun level => level.orders.findSome? fun order =>
        if order.id == n then some (sd, order) else none) = some r) : r.1 = sd := by
  obtain ⟨lv, _, hg⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨o, _, ho⟩ := List.exists_of_findSome?_eq_some hg
  split at ho
  · cases ho; rfl
  · cases ho

/-- Bids searched first: when the order is on tree `t0`, `findOrderOnBook`
    reports side `sideOfTree t0`. -/
theorem findOrderOnBook_side (hw : db.WF) (hc : ClientInv db) (hl : l ∈ db.tree t0)
    (hh : h ∈ db.queue l) :
    ∃ o, findOrderOnBook (absBook db) (rowOf db h).id.toNat = some (sideOfTree t0, o) := by
  have onside : ∀ t, (∃ lv ∈ absSide db t, ∃ o ∈ lv.orders, o.id = (rowOf db h).id.toNat) ↔
      t = t0 := by
    intro t
    rw [side_has_id]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      have hyh := resting_id_unique hw hc hl hh hx hy e
      subst hyh
      have hxl := hw.queue_unique _ _ _ hy hh
      subst hxl
      by_cases hne : t = t0
      · exact hne
      · exact absurd rfl (tree_ne_of_mem hw hx hl hne)
    · rintro rfl; exact ⟨l, hl, h, hh, rfl⟩
  unfold findOrderOnBook
  simp only
  cases t0 with
  | bids =>
    cases hb : ((absBook db).bids.findSome? fun level => level.orders.findSome? fun order =>
        if order.id == (rowOf db h).id.toNat then some (Side.buy, order) else none) with
    | none =>
      have := (onside .bids).mpr rfl
      obtain ⟨lv, hlv, o, ho, e⟩ := this
      exact absurd e (findSome_side_none.mp hb lv hlv o ho)
    | some r =>
      obtain ⟨sd, o⟩ := r
      have := findSome_side_some hb
      simp only at this; subst this
      exact ⟨o, rfl⟩
  | asks =>
    have hb : ((absBook db).bids.findSome? fun level => level.orders.findSome? fun order =>
        if order.id == (rowOf db h).id.toNat then some (Side.buy, order) else none) = none := by
      apply findSome_side_none.mpr
      intro lv hlv o ho e
      have := (onside .bids).mp ⟨lv, hlv, o, ho, e⟩
      cases this
    rw [hb]
    simp only
    cases ha : ((absBook db).asks.findSome? fun level => level.orders.findSome? fun order =>
        if order.id == (rowOf db h).id.toNat then some (Side.sell, order) else none) with
    | none =>
      have := (onside .asks).mpr rfl
      obtain ⟨lv, hlv, o, ho, e⟩ := this
      exact absurd e (findSome_side_none.mp ha lv hlv o ho)
    | some r =>
      obtain ⟨sd, o⟩ := r
      have := findSome_side_some ha
      simp only at this; subst this
      exact ⟨o, rfl⟩

/-- **The spec's cancel, through the view.** `cancelOrder` on the decoded book
    finds the order and leaves a book with the view of `cancelDb`. -/
theorem cancel_spec_view (hw : db.WF) (hc : ClientInv db) (hl : l ∈ db.tree t0)
    (hh : h ∈ db.queue l) (hw' : (cancelDb db t0 l h).WF) :
    ∃ b', cancelOrder (absBook db) (rowOf db h).id.toNat = some b' ∧
      bookView (absBook (cancelDb db t0 l h)) = bookView b' := by
  obtain ⟨o, hf⟩ := findOrderOnBook_side hw hc hl hh
  have hside := cancel_side_view hw hc hl hh hw'
  unfold cancelOrder
  rw [hf]
  cases t0 with
  | bids =>
    refine ⟨_, rfl, ?_⟩
    simp only [bookView, absBook, BookView.mk.injEq]
    refine ⟨hside, ?_, trivial⟩
    rw [cancel_other_side hw hl hh (by decide)]
  | asks =>
    refine ⟨_, rfl, ?_⟩
    simp only [bookView, absBook, BookView.mk.injEq]
    refine ⟨?_, hside, trivial⟩
    rw [cancel_other_side hw hl hh (by decide)]

end CancelSpec

-- ============================================================================
-- Inv after a cancel: pure facts about cancelDb
-- ============================================================================

section CancelInv

variable {db : Db} {t0 : Tree} {l : LevelH} {h : OrderH}

/-- The level empties. -/
abbrev Emptied (db : Db) (l : LevelH) (h : OrderH) : Prop := ((db.queue l).erase h).isEmpty = true

theorem mem_cancel_tree (hw : db.WF) (hl : l ∈ db.tree t0) {t : Tree} {x : LevelH} :
    x ∈ (cancelDb db t0 l h).tree t ↔ x ∈ db.tree t ∧ ¬(Emptied db l h ∧ x = l) := by
  by_cases ht : t = t0
  · subst ht
    rw [cancelDb_tree hw, List.mem_filter]
    constructor
    · rintro ⟨hx, hp⟩
      refine ⟨hx, fun ⟨he, hxl⟩ => ?_⟩
      simp [he, hxl] at hp
    · rintro ⟨hx, hn⟩
      refine ⟨hx, ?_⟩
      by_cases he : Emptied db l h
      · have : x ≠ l := fun e => hn ⟨he, e⟩
        simp [he, this]
      · simp only [Emptied] at he
        simp [he]
  · rw [cancelDb_tree_other ht]
    constructor
    · intro hx
      refine ⟨hx, fun ⟨_, hxl⟩ => ?_⟩
      subst hxl
      exact tree_ne_of_mem hw hx hl ht rfl
    · exact fun ⟨hx, _⟩ => hx

theorem mem_cancel_queue (hw : db.WF) (hh : h ∈ db.queue l) {x : LevelH} {y : OrderH} :
    y ∈ (cancelDb db t0 l h).queue x ↔ y ∈ db.queue x ∧ y ≠ h := by
  rw [cancelDb_queue]
  by_cases hxl : x = l
  · subst hxl
    rw [upd_same]
    constructor
    · intro hy
      have hne : y ≠ h := fun e => by subst e; exact (hw.queue_nodup x).not_mem_erase hy
      exact ⟨List.mem_of_mem_erase hy, hne⟩
    · rintro ⟨hy, hne⟩; exact (List.mem_erase_of_ne hne).mpr hy
  · rw [upd_other _ _ hxl]
    constructor
    · intro hy
      exact ⟨hy, fun e => by subst e; exact hxl (hw.queue_unique _ _ _ hy hh)⟩
    · exact fun ⟨hy, _⟩ => hy

theorem cancel_levelPrice (hw : db.WF) (hl : l ∈ db.tree t0) {t : Tree} {x : LevelH}
    (hx : x ∈ (cancelDb db t0 l h).tree t) :
    (cancelDb db t0 l h).levelPrice x = db.levelPrice x := by
  by_cases hxl : x = l
  · subst hxl
    have hne : ¬ Emptied db x h := fun he => ((mem_cancel_tree hw hl).mp hx).2 ⟨he, rfl⟩
    simp only [Emptied, Bool.not_eq_true] at hne
    simp only [Db.levelPrice, cancelDb_levels_of_nonempty hne]
  · simp only [Db.levelPrice, cancelDb_levels_of_ne hxl]

theorem cancel_queued (hw : db.WF) (hh : h ∈ db.queue l) (y : OrderH) :
    (cancelDb db t0 l h).queued y ↔ db.queued y ∧ y ≠ h := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hy, hne⟩ := (mem_cancel_queue hw hh).mp hx
    exact ⟨⟨x, hy⟩, hne⟩
  · rintro ⟨⟨x, hy⟩, hne⟩
    exact ⟨x, (mem_cancel_queue hw hh).mpr ⟨hy, hne⟩⟩

theorem cancel_clientInv (hw : db.WF) (hc : ClientInv db) (hl : l ∈ db.tree t0)
    (hh : h ∈ db.queue l) : ClientInv (cancelDb db t0 l h) where
  level_nonempty := by
    intro t x hx
    obtain ⟨hxt, hn⟩ := (mem_cancel_tree hw hl).mp hx
    rw [cancelDb_queue]
    by_cases hxl : x = l
    · subst hxl
      rw [upd_same]
      intro he
      exact hn ⟨by simp [Emptied, he], rfl⟩
    · rw [upd_other _ _ hxl]; exact hc.level_nonempty t x hxt
  queue_in_tree := by
    intro x y hy
    obtain ⟨hy', hne⟩ := (mem_cancel_queue hw hh).mp hy
    have hnot : ¬(Emptied db l h ∧ x = l) := by
      rintro ⟨he, rfl⟩
      rw [cancelDb_queue, upd_same] at hy
      rw [List.isEmpty_iff.mp he] at hy
      cases hy
    rcases hc.queue_in_tree x y hy' with hb | ha
    · exact Or.inl ((mem_cancel_tree hw hl).mpr ⟨hb, hnot⟩)
    · exact Or.inr ((mem_cancel_tree hw hl).mpr ⟨ha, hnot⟩)
  hash_iff_queued := by
    intro y
    rw [cancel_queued hw hh]
    have hin : h ∈ db.hash := (hc.hash_iff_queued h).mpr ⟨l, hh⟩
    show y ∈ (cancelDb db t0 l h).hash ↔ _
    have hhash : (cancelDb db t0 l h).hash = db.hash.erase h := by unfold cancelDb; split <;> rfl
    rw [hhash]
    constructor
    · intro hy
      have hne : y ≠ h := fun e => by subst e; exact hw.hash_nodup.not_mem_erase hy
      exact ⟨(hc.hash_iff_queued y).mp (List.mem_of_mem_erase hy), hne⟩
    · rintro ⟨hq, hne⟩
      exact (List.mem_erase_of_ne hne).mpr ((hc.hash_iff_queued y).mpr hq)
  order_ok := by
    intro t x hx y hy
    obtain ⟨hxt, _⟩ := (mem_cancel_tree hw hl).mp hx
    obtain ⟨hy', hne⟩ := (mem_cancel_queue hw hh).mp hy
    obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := hc.order_ok t x hxt y hy'
    refine ⟨r, ?_, h1, ?_, h3, h4, h5⟩
    · rw [cancelDb_orders, upd_other _ _ hne]; exact hr
    · rw [cancel_levelPrice hw hl hx]; exact h2
  price_pos := by
    intro t x hx
    rw [cancel_levelPrice hw hl hx]
    exact hc.price_pos t x ((mem_cancel_tree hw hl).mp hx).1
  uncrossed := by
    intro lb hb la ha
    rw [cancel_levelPrice hw hl hb, cancel_levelPrice hw hl ha]
    exact hc.uncrossed lb ((mem_cancel_tree hw hl).mp hb).1 la ((mem_cancel_tree hw hl).mp ha).1

end CancelInv

-- ============================================================================
-- Inv after a cancel: live rows and counts
-- ============================================================================

section CancelCounts

variable {db : Db} {t0 : Tree} {l : LevelH} {h : OrderH}

theorem sum_map_erase {α : Type} [DecidableEq α] (F : α → Nat) :
    ∀ {T : List α} {x : α}, x ∈ T → ((T.erase x).map F).sum + F x = (T.map F).sum
  | [], _, hx => by cases hx
  | y :: T, x, hx => by
    by_cases hxy : y = x
    · subst hxy; simp; omega
    · have hx' : x ∈ T := by
        rcases List.mem_cons.mp hx with e | e
        · exact absurd e.symm hxy
        · exact e
      simp only [List.erase_cons, beq_iff_eq, hxy, if_false, List.map_cons, List.sum_cons]
      have := sum_map_erase F hx'
      omega

theorem sum_map_update {α : Type} [DecidableEq α] (F G : α → Nat) {x : α}
    (hG : ∀ y, y ≠ x → G y = F y) :
    ∀ {T : List α}, T.Nodup → x ∈ T → (T.map G).sum + F x = (T.map F).sum + G x
  | [], _, hx => by cases hx
  | y :: T, hnd, hx => by
    simp only [List.map_cons, List.sum_cons]
    by_cases hxy : y = x
    · subst hxy
      have hnot : y ∉ T := (List.nodup_cons.mp hnd).1
      have : (T.map G) = (T.map F) := List.map_congr_left fun z hz =>
        hG z (fun e => by subst e; exact hnot hz)
      rw [this]; omega
    · have hx' : x ∈ T := by
        rcases List.mem_cons.mp hx with e | e
        · exact absurd e.symm hxy
        · exact e
      have := sum_map_update F G hG (List.nodup_cons.mp hnd).2 hx'
      rw [hG y hxy]; omega

theorem sum_map_same {α : Type} (F G : α → Nat) {T : List α} (h : ∀ y ∈ T, G y = F y) :
    (T.map G).sum = (T.map F).sum := by rw [List.map_congr_left h]

theorem cancel_restingCount (hw : db.WF) (hl : l ∈ db.tree t0) (hh : h ∈ db.queue l) :
    restingCount (cancelDb db t0 l h) + 1 = restingCount db := by
  have hlen : ((db.queue l).erase h).length + 1 = (db.queue l).length := by
    rw [List.length_erase_of_mem hh]
    have := List.length_pos_of_mem hh
    omega
  have hG : ∀ y, y ≠ l → ((cancelDb db t0 l h).queue y).length = (db.queue y).length := by
    intro y hy; rw [cancelDb_queue, upd_other _ _ hy]
  have hGl : ((cancelDb db t0 l h).queue l).length = ((db.queue l).erase h).length := by
    rw [cancelDb_queue, upd_same]
  have other : ∀ t, t ≠ t0 →
      (((cancelDb db t0 l h).tree t).map fun x => ((cancelDb db t0 l h).queue x).length).sum =
        ((db.tree t).map fun x => (db.queue x).length).sum := by
    intro t ht
    rw [cancelDb_tree_other ht]
    exact sum_map_same _ _ fun y hy => hG y (tree_ne_of_mem hw hy hl ht)
  have own : (((cancelDb db t0 l h).tree t0).map fun x => ((cancelDb db t0 l h).queue x).length).sum
      + 1 = ((db.tree t0).map fun x => (db.queue x).length).sum := by
    by_cases he : Emptied db l h
    · have ht : (cancelDb db t0 l h).tree t0 = (db.tree t0).erase l := by
        unfold cancelDb; simp only [Emptied] at he; simp [he]
      rw [ht]
      have hz : ((db.queue l).erase h).length = 0 := by
        simp only [Emptied] at he; rw [List.isEmpty_iff.mp he]; rfl
      have e1 := sum_map_erase (fun x => (db.queue x).length) hl
      have e2 : (((db.tree t0).erase l).map fun x => ((cancelDb db t0 l h).queue x).length) =
          (((db.tree t0).erase l).map fun x => (db.queue x).length) :=
        List.map_congr_left fun y hy => hG y (fun e => by
          subst e; exact (hw.tree_nodup t0).not_mem_erase hy)
      rw [e2]; simp only at e1; omega
    · have ht : (cancelDb db t0 l h).tree t0 = db.tree t0 := by
        unfold cancelDb; simp only [Emptied, Bool.not_eq_true] at he; simp [he]
      rw [ht]
      have := sum_map_update (fun x => (db.queue x).length)
        (fun x => ((cancelDb db t0 l h).queue x).length) hG (hw.tree_nodup t0) hl
      simp only at this
      rw [hGl] at this
      omega
  unfold restingCount
  simp only [List.map_append, List.sum_append_nat]
  cases t0 with
  | bids => rw [other .asks (by decide)]; omega
  | asks => rw [other .bids (by decide)]; omega

theorem cancel_tree_length (_hw : db.WF) (hl : l ∈ db.tree t0) :
    ((cancelDb db t0 l h).tree .bids ++ (cancelDb db t0 l h).tree .asks).length +
      (if Emptied db l h then 1 else 0) = (db.tree .bids ++ db.tree .asks).length := by
  by_cases he : Emptied db l h
  · have ht : (cancelDb db t0 l h).tree = upd db.tree t0 ((db.tree t0).erase l) := by
      unfold cancelDb; rw [if_pos he]
    rw [if_pos he, ht, List.length_append, List.length_append]
    have e := List.length_erase_of_mem hl
    have p := List.length_pos_of_mem hl
    cases t0 <;> simp only [upd, reduceCtorEq, if_true, if_false] <;> omega
  · have ht : (cancelDb db t0 l h).tree = db.tree := by
      unfold cancelDb; rw [if_neg he]
    rw [if_neg he, ht, Nat.add_zero]

theorem cancel_orders_resting (hw : db.WF) (hh : h ∈ db.queue l)
    (hr : ∀ y, db.orderLive y ↔ db.queued y) (y : OrderH) :
    (cancelDb db t0 l h).orderLive y ↔ (cancelDb db t0 l h).queued y := by
  rw [cancel_queued hw hh]
  simp only [Db.orderLive, cancelDb_orders]
  by_cases hyh : y = h
  · subst hyh; simp
  · rw [upd_other _ _ hyh]; exact ⟨fun h1 => ⟨(hr y).mp h1, hyh⟩, fun ⟨h1, _⟩ => (hr y).mpr h1⟩

theorem cancel_levels_resting (hw : db.WF) (hl : l ∈ db.tree t0)
    (hr : ∀ x, db.levelLive x ↔ (x ∈ db.tree .bids ∨ x ∈ db.tree .asks)) (x : LevelH) :
    (cancelDb db t0 l h).levelLive x ↔
      (x ∈ (cancelDb db t0 l h).tree .bids ∨ x ∈ (cancelDb db t0 l h).tree .asks) := by
  rw [mem_cancel_tree hw hl, mem_cancel_tree hw hl]
  by_cases hc : Emptied db l h ∧ x = l
  · obtain ⟨he, rfl⟩ := hc
    have : (cancelDb db t0 x h).levels x = none := by
      unfold cancelDb; rw [if_pos he]; exact upd_same _ _ _
    simp only [Db.levelLive, this, Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro (⟨_, hn⟩ | ⟨_, hn⟩) <;> exact hn ⟨he, by trivial⟩
  · have hlev : (cancelDb db t0 l h).levels x = db.levels x := by
      by_cases hxl : x = l
      · subst hxl
        have hne : ((db.queue x).erase h).isEmpty = false := by
          cases hb : ((db.queue x).erase h).isEmpty
          · rfl
          · exact absurd ⟨hb, rfl⟩ hc
        exact cancelDb_levels_of_nonempty hne x
      · exact cancelDb_levels_of_ne hxl
    show ((cancelDb db t0 l h).levels x).isSome = true ↔ _
    rw [hlev]
    show db.levelLive x ↔ _
    rw [hr x]
    exact ⟨fun h' => h'.imp (fun hb => ⟨hb, hc⟩) (fun ha => ⟨ha, hc⟩),
      fun h' => h'.imp (·.1) (·.1)⟩

end CancelCounts

-- ============================================================================
-- Cancel of a resting order refines processB
-- ============================================================================

section CancelRun

variable {S : Type} [EngineDb S]

open EngineDb

theorem queuedB_false_of {db : Db} {h : OrderH} (hq : ¬ db.queued h) : queuedB db h = false := by
  unfold queuedB
  rw [List.any_eq_false]
  intro x _ hx
  exact hq ⟨x, List.contains_iff_mem.mp (by simpa using hx)⟩

theorem evalExpr_eq_def (st : St S) (a b : Expr) :
    evalExpr st (.bin .eq a b) =
      (evalExpr st a).bind fun va => (evalExpr st b).bind fun vb => evalBin .eq va vb := rfl

theorem le_sum_of_mem_nat : ∀ {L : List Nat} {x : Nat}, x ∈ L → x ≤ L.sum
  | [], _, hx => by cases hx
  | y :: L, x, hx => by
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := le_sum_of_mem_nat hx; omega

/-- The environment of `gen_cancel_order` after the lookups. -/
def cancelEnv3 (id : UInt64) (h : OrderH) (l : LevelH) (sd : UInt8) : List (Ident × Val) :=
  [("id", .u64 id), ("ord", .order (some h)), ("lvl", .level (some l)), ("side", .code sd)]

/-- **Cancel of a resting order.** -/
theorem refines_cancel_resting {s : S} {id : UInt64} {h : OrderH} (hI : Inv s) (hcap : CapOk S)
    (hf : hashFind s id = some h) : Refines s (.cancel id) := by
  have hw := hI.wf
  have hc := hI.client
  -- the order, its level, its tree, its row
  have hpost := hashFind_law s id hw
  rw [hf] at hpost
  obtain ⟨hhash, hid⟩ := hpost
  have hqd : (view s).queued h := (hc.hash_iff_queued h).mp hhash
  have howner := owner_law s h hw
  cases ho : owner s h with
  | none => rw [ho] at howner; exact absurd hqd howner
  | some l =>
  rw [ho] at howner
  have hh : h ∈ (view s).queue l := howner
  have hlive : (view s).orderLive h := (hw.queue_live l h hh).1
  have hllive : (view s).levelLive l := (hw.queue_live l h hh).2
  obtain ⟨t0, hl⟩ : ∃ t0, l ∈ (view s).tree t0 := by
    rcases hc.queue_in_tree l h hh with hb | ha
    · exact ⟨.bids, hb⟩
    · exact ⟨.asks, ha⟩
  obtain ⟨row, hrow, hside, -, -, -, -⟩ := hc.order_ok t0 l hl h hh
  have hn : (rowOf (view s) h).id.toNat = id.toNat := by
    have : (view s).orderId h = row.id := by simp [Db.orderId, hrow]
    simp [rowOf, hrow, ← this, hid]
  -- the store chain
  obtain ⟨s1, hs1⟩ : ∃ x, x = qRemove s l h := ⟨_, rfl⟩
  have hv1 : view s1 = { view s with queue := upd (view s).queue l (((view s).queue l).erase h) } := by
    rw [hs1]; exact qRemove_law s l h hw hh
  have hw1 : (view s1).WF := qRemove_preserves_WF hw hv1
  obtain ⟨s2, hs2⟩ : ∃ x, x = hashRemove s1 h := ⟨_, rfl⟩
  have hhash1 : h ∈ (view s1).hash := by rw [hv1]; exact hhash
  have hv2 : view s2 = { view s1 with hash := (view s1).hash.erase h } := by
    rw [hs2]; exact hashRemove_law s1 h hw1 hhash1
  have hw2 : (view s2).WF := hashRemove_preserves_WF hw1 hv2
  have hnq2 : ¬ (view s2).queued h := by
    rintro ⟨x, hx⟩
    rw [hv2, hv1] at hx
    by_cases hxl : x = l
    · subst hxl
      simp only [upd_same] at hx
      exact (hw.queue_nodup x).not_mem_erase hx
    · simp only [upd_other _ _ hxl] at hx
      exact hxl (hw.queue_unique _ _ _ hx hh)
  have hnh2 : h ∉ (view s2).hash := by
    rw [hv2]; exact hw1.hash_nodup.not_mem_erase
  have hlive2 : (view s2).orderLive h := by rw [hv2, hv1]; exact hlive
  have hpre3 : orderFree.pre (view s2) h := ⟨hlive2, hnq2, hnh2⟩
  obtain ⟨s3, hs3⟩ : ∃ x, x = orderFree s2 h := ⟨_, rfl⟩
  have hv3 : view s3 =
      { view s2 with orders := upd (view s2).orders h none, oLive := (view s2).oLive.erase h } := by
    rw [hs3]; exact orderFree_law s2 h hw2 hpre3
  have hw3 : (view s3).WF := orderFree_preserves_WF hw2 hpre3 hv3
  have hq3 : (view s3).queue l = ((view s).queue l).erase h := by
    rw [hv3, hv2, hv1]; exact upd_same _ _ _
  have hlv3 : (view s3).levels = (view s).levels := by rw [hv3, hv2, hv1]
  have htree3 : (view s3).tree = (view s).tree := by rw [hv3, hv2, hv1]
  have hc3 : count s3 + 1 = count s := by
    have a := count_qRemove s l h
    have b := count_hashRemove s1 h
    have c := count_orderFree s2 h hw2 hpre3
    rw [← hs1] at a; rw [← hs2] at b; rw [← hs3] at c
    omega
  have hlu3 : levelsUsed s3 = levelsUsed s := by
    rw [hs3, levelsUsed_orderFree, hs2, levelsUsed_hashRemove, hs1, levelsUsed_qRemove]
  -- the level count the program reads
  have hcnt3 : levelCount s3 l = (((view s).queue l).erase h).length := by
    rw [levelCount_law]; simp only [EngineDbApi.levelCount, hq3]
  have hlen : (((view s).queue l).erase h).length < 2 ^ 64 := by
    have h1 := List.length_erase_le (l := (view s).queue l) (a := h)
    have hle : ((view s).queue l).length ≤ restingCount (view s) := by
      unfold restingCount
      apply le_sum_of_mem_nat
      apply List.mem_map.mpr
      exact ⟨l, by cases t0 <;> simp [hl], rfl⟩
    have h2 := hI.count_eq; have h3 := hI.count_le
    unfold CapOk at hcap
    omega
  have hl3 : liveL (view s3) l = true := by
    simp only [liveL, hlv3]; exact hllive
  let E := cancelEnv3 id h l row.side
  have ev_count : evalExpr ({ store := s3, env := E, trades := [] } : St S)
      (b2 .eq (.getL (v "lvl") .count) (u 0)) = .ok (.bool (decide (Emptied (view s) l h))) := by
    have hv : evalExpr ({ store := s3, env := E, trades := [] } : St S) (.getL (v "lvl") .count) =
        .ok (.u64 (((view s).queue l).erase h).length.toUInt64) := by
      simp (config := {decide := true}) [v, evalExpr, lookupVar, E, cancelEnv3, List.lookup,
        liveLevel, viewOf, hl3, hcnt3, hlen, bind, Except.bind]
    show evalExpr _ (.bin .eq (.getL (v "lvl") .count) (.lit 0)) = _
    rw [evalExpr_eq_def, hv]
    simp only [Except.bind, evalExpr, evalBin]
    congr 2
    by_cases he : Emptied (view s) l h
    · rw [decide_eq_true he]
      have hnil : ((view s).queue l).erase h = [] := List.isEmpty_iff.mp he
      rw [hnil]; rfl
    · rw [decide_eq_false he]
      have hne : ((view s).queue l).erase h ≠ [] := fun e => he (List.isEmpty_iff.mpr e)
      have hpos := List.length_pos_iff.mpr hne
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e
      have e2 := congrArg UInt64.toNat e
      rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlen, UInt64.toNat_zero] at e2
      omega
  -- the level check and the final store
  obtain ⟨sf, hvf, hwf, hcf, hluf, hev7⟩ : ∃ sf : S, view sf = cancelDb (view s) t0 l h ∧
      (view sf).WF ∧ count sf + 1 = count s ∧
      levelsUsed sf + (if Emptied (view s) l h then 1 else 0) = levelsUsed s ∧
      Eval program (whenS (b2 .eq (.getL (v "lvl") .count) (u 0)) (Stmt.block [
          .ite (eqc "side" SIDE_BUY) (call0 (.tRemove .bids) [v "lvl"])
            (call0 (.tRemove .asks) [v "lvl"]),
          call0 .levelFree [v "lvl"]]))
        { store := s3, env := E, trades := [] } ({ store := sf, env := E, trades := [] }, .normal) := by
    by_cases he : Emptied (view s) l h
    · -- remove the level from its tree, then free it
      have hpre4 : tRemove.pre (view s3) t0 l := by
        show l ∈ (view s3).tree t0; rw [htree3]; exact hl
      obtain ⟨s4, hs4⟩ : ∃ x, x = tRemove s3 t0 l := ⟨_, rfl⟩
      have hv4 : view s4 = { view s3 with tree := upd (view s3).tree t0 (((view s3).tree t0).erase l) } := by
        rw [hs4]; exact tRemove_law s3 t0 l hw3 hpre4
      have hw4 : (view s4).WF := tRemove_preserves_WF hw3 hv4
      have hnotin : ∀ t, l ∉ (view s4).tree t := by
        intro t hm
        rw [hv4, htree3] at hm
        by_cases ht : t = t0
        · subst ht; simp only [upd_same] at hm; exact (hw.tree_nodup t).not_mem_erase hm
        · simp only [upd_other _ _ ht] at hm; exact tree_ne_of_mem hw hm hl ht rfl
      have hq4 : (view s4).queue l = [] := by
        rw [hv4, hq3]; exact List.isEmpty_iff.mp he
      have hpre5 : levelFree.pre (view s4) l :=
        ⟨by show ((view s4).levels l).isSome = true; rw [hv4, hlv3]; exact hllive,
         hnotin .bids, hnotin .asks, hq4⟩
      obtain ⟨s5, hs5⟩ : ∃ x, x = levelFree s4 l := ⟨_, rfl⟩
      have hv5 : view s5 =
          { view s4 with levels := upd (view s4).levels l none, lLive := (view s4).lLive.erase l } := by
        rw [hs5]; exact levelFree_law s4 l hw4 hpre5
      have hw5 : (view s5).WF := levelFree_preserves_WF hw4 hpre5 hv5
      refine ⟨s5, ?_, hw5, ?_, ?_, ?_⟩
      · rw [hv5, hv4, hv3, hv2, hv1]; unfold cancelDb; rw [if_pos he]
      · rw [hs5, count_levelFree, hs4, count_tRemove]; exact hc3
      · have e := levelsUsed_levelFree s4 l hw4 hpre5
        rw [← hs5] at e
        rw [if_pos he]
        have e2 : levelsUsed s4 = levelsUsed s3 := by rw [hs4, levelsUsed_tRemove]
        omega
      · apply Eval.when_true (by rw [ev_count, decide_eq_true he])
        have hin : inTreeB (viewOf ({ store := s3, env := E, trades := [] } : St S)) t0 l = true := by
          simp only [inTreeB, viewOf, htree3]; exact List.contains_iff_mem.mpr hl
        have hext4 : Eval program (call0 (.tRemove t0) [v "lvl"]) { store := s3, env := E, trades := [] }
            ({ store := s4, env := E, trades := [] }, .normal) := by
          have := Eval.ext (P := program) (dst := none) (op := .tRemove t0) (args := [v "lvl"])
            (st := { store := s3, env := E, trades := [] }) (vals := [.level (some l)])
            (by simp (config := {decide := true}) [v, evalExpr, lookupVar, E, cancelEnv3, List.lookup,
              List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
            (runExt_tRemove hl3 hin) (by rfl)
          rw [← hs4] at this; exact this
        have hite : Eval program (.ite (eqc "side" SIDE_BUY) (call0 (.tRemove .bids) [v "lvl"])
            (call0 (.tRemove .asks) [v "lvl"])) { store := s3, env := E, trades := [] }
            ({ store := s4, env := E, trades := [] }, .normal) := by
          cases t0 with
          | bids =>
            refine Eval.ite_true ?_ hext4
            simp (config := {decide := true}) [eqc, b2, v, c, evalExpr, lookupVar, E, cancelEnv3,
              List.lookup, evalBin, hside, sideCode, SIDE_BUY, bind, Except.bind]
          | asks =>
            refine Eval.ite_false ?_ hext4
            simp (config := {decide := true}) [eqc, b2, v, c, evalExpr, lookupVar, E, cancelEnv3,
              List.lookup, evalBin, hside, sideCode, SIDE_BUY, bind, Except.bind]
        have hl4 : liveL (view s4) l = true := by
          simp only [liveL, hv4, hlv3]; exact hllive
        have hany : inAnyTreeB (view s4) l = false := by
          simp only [inAnyTreeB, inTreeB, Bool.or_eq_false_iff]
          exact ⟨by simpa using hnotin .bids, by simpa using hnotin .asks⟩
        have hfree : Eval program (call0 .levelFree [v "lvl"]) { store := s4, env := E, trades := [] }
            ({ store := s5, env := E, trades := [] }, .normal) := by
          have := Eval.ext (P := program) (dst := none) (op := .levelFree) (args := [v "lvl"])
            (st := { store := s4, env := E, trades := [] }) (vals := [.level (some l)])
            (by simp (config := {decide := true}) [v, evalExpr, lookupVar, E, cancelEnv3, List.lookup,
              List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
            (runExt_levelFree hl4 hany (by simp [viewOf, hq4])) (by rfl)
          rw [← hs5] at this; exact this
        exact Eval.block_cons_normal hite hfree (by simp)
    · refine ⟨s3, ?_, hw3, hc3, ?_, ?_⟩
      · rw [hv3, hv2, hv1]; unfold cancelDb; rw [if_neg he]
      · rw [if_neg he, Nat.add_zero, hlu3]
      · exact Eval.when_false (by rw [ev_count, decide_eq_false he])
  -- statements 1–6 of gen_cancel_order
  have hlo : liveO (view s) h = true := hlive
  have hll : liveL (view s) l = true := hllive
  let E1 := cancelEnv id (some h)
  let E2 : List (Ident × Val) :=
    [("id", .u64 id), ("ord", .order (some h)), ("lvl", .level (some l)), ("side", .code 0)]
  have st1 : Eval program (call1 "ord" .hashFind [v "id"])
      ({ store := s, env := cancelEnv id none, trades := [] } : St S)
      ({ store := s, env := E1, trades := [] }, .normal) := by
    have := eval_cancel_find s id; rw [hf] at this; exact this
  have st2 : Eval program (whenS (.isNullO (v "ord")) (MatcherProgram.retc .rejectedUnknownId))
      ({ store := s, env := E1, trades := [] } : St S) ({ store := s, env := E1, trades := [] }, .normal) :=
    Eval.when_false (by simp (config := {decide := true}) [E1, cancelEnv, v, evalExpr, lookupVar,
      List.lookup, bind, Except.bind])
  have st3 : Eval program (call1 "lvl" .owner [v "ord"])
      ({ store := s, env := E1, trades := [] } : St S) ({ store := s, env := E2, trades := [] }, .normal) :=
    Eval.ext (vals := [.order (some h)]) (s' := s) (res := some (.level (some l)))
      (by simp (config := {decide := true}) [E1, cancelEnv, v, evalExpr, lookupVar, List.lookup,
        List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
      (by rw [runExt_owner (by exact hlo), ho])
      (by simp (config := {decide := true}) [bindResult, setVar, E1, E2, cancelEnv, List.lookup, Val.ty])
  have st4 : Eval program (whenS (.isNullL (v "lvl")) (MatcherProgram.retc .rejectedUnknownId))
      ({ store := s, env := E2, trades := [] } : St S) ({ store := s, env := E2, trades := [] }, .normal) :=
    Eval.when_false (by simp (config := {decide := true}) [E2, v, evalExpr, lookupVar, List.lookup,
      bind, Except.bind])
  have hread : readOrder s h = some row := by rw [readOrder_law]; exact hrow
  have st5 : Eval program (.assign "side" (.getO (v "ord") .side))
      ({ store := s, env := E2, trades := [] } : St S) ({ store := s, env := E, trades := [] }, .normal) :=
    Eval.assign (v := .code row.side)
      (by simp (config := {decide := true}) [E2, v, evalExpr, lookupVar, List.lookup, liveOrder,
        viewOf, hlo, hread, getOField, bind, Except.bind])
      (by simp (config := {decide := true}) [setVar, E2, E, cancelEnv3, List.lookup, Val.ty])
  have hmem : ((view s).queue l).contains h = true := List.contains_iff_mem.mpr hh
  have st6a : Eval program (call0 .qRemove [v "lvl", v "ord"])
      ({ store := s, env := E, trades := [] } : St S) ({ store := s1, env := E, trades := [] }, .normal) := by
    have := Eval.ext (P := program) (dst := none) (op := .qRemove) (args := [v "lvl", v "ord"])
      (st := ({ store := s, env := E, trades := [] } : St S))
      (vals := [.level (some l), .order (some h)])
      (by simp (config := {decide := true}) [E, cancelEnv3, v, evalExpr, lookupVar, List.lookup,
        List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
      (runExt_qRemove hll hlo hmem) (by rfl)
    rw [← hs1] at this; exact this
  have hlo1 : liveO (view s1) h = true := by simp only [liveO, hv1]; exact hlo
  have hin1 : inHashB (view s1) h = true := List.contains_iff_mem.mpr hhash1
  have st6b : Eval program (call0 .hashRemove [v "ord"])
      ({ store := s1, env := E, trades := [] } : St S) ({ store := s2, env := E, trades := [] }, .normal) := by
    have := Eval.ext (P := program) (dst := none) (op := .hashRemove) (args := [v "ord"])
      (st := ({ store := s1, env := E, trades := [] } : St S)) (vals := [.order (some h)])
      (by simp (config := {decide := true}) [E, cancelEnv3, v, evalExpr, lookupVar, List.lookup,
        List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
      (runExt_hashRemove hlo1 hin1) (by rfl)
    rw [← hs2] at this; exact this
  have hlo2 : liveO (view s2) h = true := hlive2
  have st6c : Eval program (call0 .orderFree [v "ord"])
      ({ store := s2, env := E, trades := [] } : St S) ({ store := s3, env := E, trades := [] }, .normal) := by
    have := Eval.ext (P := program) (dst := none) (op := .orderFree) (args := [v "ord"])
      (st := ({ store := s2, env := E, trades := [] } : St S)) (vals := [.order (some h)])
      (by simp (config := {decide := true}) [E, cancelEnv3, v, evalExpr, lookupVar, List.lookup,
        List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
      (runExt_orderFree hlo2 (queuedB_false_of hnq2) (by simpa [inHashB] using hnh2)) (by rfl)
    rw [← hs3] at this; exact this
  have st6 : Eval program (removeResting "lvl" "ord")
      ({ store := s, env := E, trades := [] } : St S) ({ store := s3, env := E, trades := [] }, .normal) :=
    Eval.block_cons_normal st6a (Eval.block_cons_normal st6b st6c (by simp)) (by simp)
  have st8 : Eval program (MatcherProgram.retc .cancelled)
      ({ store := sf, env := E, trades := [] } : St S)
      ({ store := sf, env := E, trades := [] }, .ret (.code (codeOf .cancelled))) := Eval.retcode _
  have hbody : Eval program (Stmt.block cancelOrderStmts)
      ({ store := s, env := cancelEnv id none, trades := [] } : St S)
      ({ store := sf, env := E, trades := [] }, .ret (.code (codeOf .cancelled))) := by
    simp only [cancelOrderStmts]
    exact Eval.block_cons_normal st1 (Eval.block_cons_normal st2 (Eval.block_cons_normal st3
      (Eval.block_cons_normal st4 (Eval.block_cons_normal st5 (Eval.block_cons_normal st6
      (Eval.block_cons_normal hev7 st8 (by simp)) (by simp)) (by simp)) (by simp)) (by simp))
      (by simp)) (by simp)
  obtain ⟨fuel, hrun⟩ := cancel_run hbody
  -- the spec
  have hwc : (cancelDb (view s) t0 l h).WF := hvf ▸ hwf
  obtain ⟨b', hcan, hview⟩ := cancel_spec_view hw hc hl hh hwc
  rw [hn] at hcan
  have hspec : specStep s (.cancel id) = (.cancelled, { book := b', trades := [] }) := by
    unfold specStep processB; simp only; rw [hcan]
  refine ⟨fuel, sf, [], ?_, ?_, ?_, ?_⟩
  · rw [hspec]; exact hrun
  · rw [hspec]; rfl
  · rw [hspec, hvf]; exact hview
  · refine { wf := hwf, client := ?_, orders_resting := ?_, levels_resting := ?_,
             count_eq := ?_, levels_eq := ?_, count_le := ?_ }
    · rw [hvf]; exact cancel_clientInv hw hc hl hh
    · rw [hvf]; exact cancel_orders_resting hw hh hI.orders_resting
    · rw [hvf]; exact cancel_levels_resting hw hl hI.levels_resting
    · rw [hvf]
      have := cancel_restingCount hw hl hh
      have := hI.count_eq
      omega
    · rw [hvf]
      have := cancel_tree_length (h := h) hw hl
      have := hI.levels_eq
      omega
    · have := hI.count_le; omega

end CancelRun

end MatcherCancel

namespace MatcherCancel
open MatcherRefines EngineDbApi

/-- **Cancel refines `processB`**, for every id. -/
theorem refines_cancel {S : Type} [EngineDb S] {s : S} (id : UInt64) (hI : Inv s)
    (hcap : CapOk S) : Refines s (.cancel id) := by
  cases hf : EngineDb.hashFind s id with
  | none => exact refines_cancel_unknown hI hf
  | some h => exact refines_cancel_resting hI hcap hf

end MatcherCancel

import Matcher.Cancel

/-!
# Phase 4: the store side of the matching loop

What the matching loop does to the store view, as pure functions of `Db`:

* `dropDb db l h`: the head order `h` of level `l` leaves (`qRemove`,
  `hashRemove`, `orderFree`); the level stays in its tree, possibly empty.
* `setRemDb db h row`: an order's row is rewritten (its remaining quantity).
* `freeDb db t l`: an empty level leaves tree `t` and is freed.

`ClientInvM db l` is `ClientInv` except that level `l` may be empty: it holds
inside an outer iteration of the matching loop, `l` being the level that
iteration bound (LOOP-INVARIANT.md). `InvM s l` is `Inv` with it.

Views: `absSide_best` splits a decoded side into its best level and the rest
(`restSide`); `Frame` says a step touched only level `l`'s queue and the rows
queued there, which leaves `restSide` and the other side unchanged.
-/

namespace MatcherStore

open EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel

-- ============================================================================
-- The best level and the rest of a side
-- ============================================================================

/-- A side without level `l`, decoded and sorted. -/
def restSide (db : Db) (t : Tree) (l : LevelH) : List PriceLevel :=
  sortLevels t (((db.tree t).erase l).map (absLevel db t))

theorem prioB_of_better {t : Tree} {p q : UInt64} (hb : better t p q) (hne : p ≠ q) :
    prioB t p.toNat q.toNat = true := by
  have hne' : p.toNat ≠ q.toNat := fun e => hne (UInt64.toNat_inj.mp e)
  cases t <;> simp only [better] at hb <;> simp only [prioB, decide_eq_true_eq] <;>
    rw [UInt64.le_iff_toNat_le] at hb <;> omega

theorem erase_levels_distinct {db : Db} (hw : db.WF) (t : Tree) (l : LevelH) :
    (((db.tree t).erase l).map (absLevel db t)).Pairwise (fun a b => a.price ≠ b.price) := by
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ ((hw.tree_nodup t).sublist (List.erase_sublist))
  intro a b ha hb hne heq
  exact hne (hw.tree_prices t a (List.mem_of_mem_erase ha) b (List.mem_of_mem_erase hb)
    (UInt64.toNat_inj.mp heq))

/-- **The best level heads the decoded side.** -/
theorem absSide_best {db : Db} {t : Tree} {l : LevelH} (hw : db.WF) (hl : l ∈ db.tree t)
    (hb : ∀ l' ∈ db.tree t, better t (db.levelPrice l) (db.levelPrice l')) :
    absSide db t = absLevel db t l :: restSide db t l := by
  apply List.Perm.eq_of_pairwise (le := fun a b => prioB t a.price b.price = true)
  · intro a b _ _ hab hba; exact (prioB_asymm hab hba).elim
  · exact absSide_pairwise hw t
  · refine List.Pairwise.cons ?_ (sortLevels_pairwise (erase_levels_distinct hw t l))
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_sortLevels.mp hy)
    have hxl : x ≠ l := fun e => by subst e; exact (hw.tree_nodup t).not_mem_erase hx
    have hxt := List.mem_of_mem_erase hx
    have hne : db.levelPrice l ≠ db.levelPrice x := fun e => hxl (hw.tree_prices t x hxt l hl e.symm)
    exact prioB_of_better (hb x hxt) hne
  · unfold absSide restSide
    refine (sortLevels_perm t _).trans ?_
    refine (List.Perm.trans ?_ ((sortLevels_perm t _).symm.cons _))
    have := (List.perm_cons_erase hl).map (absLevel db t)
    simpa using this

/-- The view of a level: its price and its queue's rows. -/
def ordV (db : Db) (t : Tree) (h : OrderH) : OrderView := orderView (restingOrder t (rowOf db h) 0)

theorem levelView_absLevel (db : Db) (t : Tree) (l : LevelH) :
    levelView (absLevel db t l) =
      { price := (db.levelPrice l).toNat, orders := (db.queue l).map (ordV db t) } := by
  simp only [levelView, absLevel, absQueue_views]; rfl

-- ============================================================================
-- Frames
-- ============================================================================

/-- `db'` differs from `db` at most in level `l`'s queue, the rows queued at
    `l`, the hash and the live-order list. -/
structure Frame (l : LevelH) (db db' : Db) : Prop where
  tree : db'.tree = db.tree
  levels : db'.levels = db.levels
  queue : ∀ x, x ≠ l → db'.queue x = db.queue x
  orders : ∀ x, x ≠ l → ∀ h ∈ db.queue x, db'.orders h = db.orders h

theorem Frame.refl (l : LevelH) (db : Db) : Frame l db db :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Frame.trans {l : LevelH} {db db' db'' : Db} (h₁ : Frame l db db') (h₂ : Frame l db' db'') :
    Frame l db db'' :=
  ⟨h₂.tree.trans h₁.tree, h₂.levels.trans h₁.levels,
   fun x hx => (h₂.queue x hx).trans (h₁.queue x hx),
   fun x hx h hh => (h₂.orders x hx h (by rw [h₁.queue x hx]; exact hh)).trans (h₁.orders x hx h hh)⟩

theorem Frame.absLevel_eq {l x : LevelH} {db db' : Db} (hf : Frame l db db') (t : Tree) (hx : x ≠ l) :
    absLevel db' t x = absLevel db t x :=
  absLevel_congr (hf.queue x hx) (hf.orders x hx) (by simp only [Db.levelPrice, hf.levels])

theorem Frame.restSide_eq {l : LevelH} {db db' : Db} (hw : db.WF) (hf : Frame l db db') (t : Tree) :
    restSide db' t l = restSide db t l := by
  unfold restSide
  rw [hf.tree]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact hf.absLevel_eq t (fun e => by subst e; exact (hw.tree_nodup t).not_mem_erase hx)

theorem Frame.absSide_other {l : LevelH} {db db' : Db} (hf : Frame l db db') {t : Tree}
    (hl : l ∉ db.tree t) : absSide db' t = absSide db t := by
  unfold absSide
  rw [hf.tree]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact hf.absLevel_eq t (fun e => by subst e; exact hl hx)

theorem Frame.levelPrice_eq {l : LevelH} {db db' : Db} (hf : Frame l db db') (x : LevelH) :
    db'.levelPrice x = db.levelPrice x := by simp only [Db.levelPrice, hf.levels]

-- ============================================================================
-- The operations, as views
-- ============================================================================

def dropDb (db : Db) (l : LevelH) (h : OrderH) : Db :=
  { db with queue := upd db.queue l ((db.queue l).erase h), hash := db.hash.erase h,
            orders := upd db.orders h none, oLive := db.oLive.erase h }

def setRemDb (db : Db) (h : OrderH) (row : OrderRow) : Db :=
  { db with orders := upd db.orders h (some row) }

def freeDb (db : Db) (t : Tree) (l : LevelH) : Db :=
  { db with tree := upd db.tree t ((db.tree t).erase l), levels := upd db.levels l none,
            lLive := db.lLive.erase l }

theorem frame_drop {db : Db} {l : LevelH} {h : OrderH} (hw : db.WF) (hh : h ∈ db.queue l) :
    Frame l db (dropDb db l h) where
  tree := rfl
  levels := rfl
  queue := fun x hx => upd_other _ _ hx
  orders := fun x hx y hy => by
    have : y ≠ h := fun e => by subst e; exact hx (hw.queue_unique _ _ _ hy hh)
    exact upd_other _ _ this

theorem frame_setRem {db : Db} {l : LevelH} {h : OrderH} {row : OrderRow} (hw : db.WF)
    (hh : h ∈ db.queue l) : Frame l db (setRemDb db h row) where
  tree := rfl
  levels := rfl
  queue := fun _ _ => rfl
  orders := fun x hx y hy => by
    have : y ≠ h := fun e => by subst e; exact hx (hw.queue_unique _ _ _ hy hh)
    exact upd_other _ _ this

-- ============================================================================
-- The matching-loop invariant
-- ============================================================================

/-- `ClientInv` except that level `l0` may be empty. -/
structure ClientInvM (db : Db) (l0 : LevelH) : Prop where
  level_nonempty : ∀ t, ∀ l ∈ db.tree t, l ≠ l0 → db.queue l ≠ []
  queue_in_tree  : ∀ l h, h ∈ db.queue l → l ∈ db.tree .bids ∨ l ∈ db.tree .asks
  hash_iff_queued : ∀ h, h ∈ db.hash ↔ db.queued h
  order_ok       : ∀ t, ∀ l ∈ db.tree t, ∀ h ∈ db.queue l, ∃ r,
                     db.orders h = some r ∧ r.side = sideCode t ∧
                     r.price = db.levelPrice l ∧ 0 < r.remaining ∧
                     r.remaining ≤ r.qty ∧ r.stpMode ≤ 4
  price_pos      : ∀ t, ∀ l ∈ db.tree t, 0 < db.levelPrice l
  uncrossed      : ∀ lb ∈ db.tree .bids, ∀ la ∈ db.tree .asks,
                     db.levelPrice lb < db.levelPrice la

theorem ClientInv.toM {db : Db} (hc : ClientInv db) (l0 : LevelH) : ClientInvM db l0 :=
  ⟨fun t l hl _ => hc.level_nonempty t l hl, hc.queue_in_tree, hc.hash_iff_queued, hc.order_ok,
   hc.price_pos, hc.uncrossed⟩

theorem ClientInvM.toInv {db : Db} {l0 : LevelH} (hc : ClientInvM db l0)
    (h0 : db.queue l0 ≠ [] ∨ ∀ t, l0 ∉ db.tree t) : ClientInv db :=
  ⟨fun t l hl => by
     by_cases e : l = l0
     · subst e
       rcases h0 with h0 | h0
       · exact h0
       · exact absurd hl (h0 t)
     · exact hc.level_nonempty t l hl e,
   hc.queue_in_tree, hc.hash_iff_queued, hc.order_ok, hc.price_pos, hc.uncrossed⟩

section Views

variable {db : Db} {t : Tree} {l : LevelH} {h : OrderH}

theorem mem_drop_queue (hw : db.WF) (hh : h ∈ db.queue l) {x : LevelH} {y : OrderH} :
    y ∈ (dropDb db l h).queue x ↔ y ∈ db.queue x ∧ y ≠ h := by
  simp only [dropDb]
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

theorem drop_queued (hw : db.WF) (hh : h ∈ db.queue l) (y : OrderH) :
    (dropDb db l h).queued y ↔ db.queued y ∧ y ≠ h := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hy, hne⟩ := (mem_drop_queue hw hh).mp hx
    exact ⟨⟨x, hy⟩, hne⟩
  · rintro ⟨⟨x, hy⟩, hne⟩
    exact ⟨x, (mem_drop_queue hw hh).mpr ⟨hy, hne⟩⟩

theorem drop_clientInvM (hw : db.WF) (hc : ClientInvM db l) (hh : h ∈ db.queue l) :
    ClientInvM (dropDb db l h) l where
  level_nonempty := by
    intro t x hx hxl
    simp only [dropDb, upd_other _ _ hxl]
    exact hc.level_nonempty t x hx hxl
  queue_in_tree := by
    intro x y hy
    exact hc.queue_in_tree x y ((mem_drop_queue hw hh).mp hy).1
  hash_iff_queued := by
    intro y
    rw [drop_queued hw hh]
    show y ∈ db.hash.erase h ↔ _
    constructor
    · intro hy
      have hne : y ≠ h := fun e => by subst e; exact hw.hash_nodup.not_mem_erase hy
      exact ⟨(hc.hash_iff_queued y).mp (List.mem_of_mem_erase hy), hne⟩
    · rintro ⟨hq, hne⟩
      exact (List.mem_erase_of_ne hne).mpr ((hc.hash_iff_queued y).mpr hq)
  order_ok := by
    intro t x hx y hy
    obtain ⟨hy', hne⟩ := (mem_drop_queue hw hh).mp hy
    obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := hc.order_ok t x hx y hy'
    exact ⟨r, by simp only [dropDb, upd_other _ _ hne]; exact hr, h1, h2, h3, h4, h5⟩
  price_pos := hc.price_pos
  uncrossed := hc.uncrossed

theorem drop_orders_resting (hw : db.WF) (hh : h ∈ db.queue l)
    (hr : ∀ y, db.orderLive y ↔ db.queued y) (y : OrderH) :
    (dropDb db l h).orderLive y ↔ (dropDb db l h).queued y := by
  rw [drop_queued hw hh]
  simp only [Db.orderLive, dropDb]
  by_cases hyh : y = h
  · subst hyh; simp
  · rw [upd_other _ _ hyh]; exact ⟨fun h1 => ⟨(hr y).mp h1, hyh⟩, fun ⟨h1, _⟩ => (hr y).mpr h1⟩

theorem drop_restingCount (hw : db.WF) (hl : l ∈ db.tree t) (hh : h ∈ db.queue l) :
    restingCount (dropDb db l h) + 1 = restingCount db := by
  have hlen : ((db.queue l).erase h).length + 1 = (db.queue l).length := by
    rw [List.length_erase_of_mem hh]
    have := List.length_pos_of_mem hh
    omega
  have hG : ∀ y, y ≠ l → ((dropDb db l h).queue y).length = (db.queue y).length := by
    intro y hy; simp only [dropDb, upd_other _ _ hy]
  have hGl : ((dropDb db l h).queue l).length = ((db.queue l).erase h).length := by
    simp only [dropDb, upd_same]
  have other : ∀ t', t' ≠ t →
      (((dropDb db l h).tree t').map fun x => ((dropDb db l h).queue x).length).sum =
        ((db.tree t').map fun x => (db.queue x).length).sum := by
    intro t' ht
    exact sum_map_same _ _ fun y hy => hG y (tree_ne_of_mem hw hy hl ht)
  have own : (((dropDb db l h).tree t).map fun x => ((dropDb db l h).queue x).length).sum
      + 1 = ((db.tree t).map fun x => (db.queue x).length).sum := by
    have := sum_map_update (fun x => (db.queue x).length)
      (fun x => ((dropDb db l h).queue x).length) hG (hw.tree_nodup t) hl
    simp only at this
    rw [hGl] at this
    show (((db.tree t).map fun x => ((dropDb db l h).queue x).length).sum) + 1 = _
    omega
  unfold restingCount
  simp only [List.map_append, List.sum_append_nat]
  cases t with
  | bids => rw [other .asks (by decide)]; show _ + _ + 1 = _; omega
  | asks => rw [other .bids (by decide)]; show _ + _ + 1 = _; omega

theorem setRem_clientInvM (hc : ClientInvM db l) (hh : h ∈ db.queue l) (_hl : l ∈ db.tree t)
    {row : OrderRow} (hrow : db.orders h = some row) {p : UInt64} (hp0 : 0 < p)
    (hp : p ≤ row.remaining) :
    ClientInvM (setRemDb db h { row with remaining := p }) l where
  level_nonempty := hc.level_nonempty
  queue_in_tree := hc.queue_in_tree
  hash_iff_queued := hc.hash_iff_queued
  order_ok := by
    intro t' x hx y hy
    obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := hc.order_ok t' x hx y hy
    by_cases hyh : y = h
    · subst hyh
      rw [hrow] at hr; cases hr
      refine ⟨{ row with remaining := p }, by simp [setRemDb], h1, h2, hp0, ?_, h5⟩
      exact UInt64.le_trans hp h4
    · exact ⟨r, by simp only [setRemDb, upd_other _ _ hyh]; exact hr, h1, h2, h3, h4, h5⟩
  price_pos := hc.price_pos
  uncrossed := hc.uncrossed

theorem free_clientInv (hw : db.WF) (hc : ClientInvM db l) (hl : l ∈ db.tree t)
    (he : db.queue l = []) : ClientInv (freeDb db t l) := by
  have memT : ∀ t' x, x ∈ (freeDb db t l).tree t' ↔ x ∈ db.tree t' ∧ x ≠ l := by
    intro t' x
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
  have lp : ∀ x, x ≠ l → (freeDb db t l).levelPrice x = db.levelPrice x := by
    intro x hx; simp only [Db.levelPrice, freeDb, upd_other _ _ hx]
  exact
  { level_nonempty := by
      intro t' x hx
      obtain ⟨hx, hne⟩ := (memT t' x).mp hx
      exact hc.level_nonempty t' x hx hne
    queue_in_tree := by
      intro x y hy
      have hne : x ≠ l := fun e => by
        subst e; have hy' : y ∈ db.queue x := hy; rw [he] at hy'; cases hy'
      rcases hc.queue_in_tree x y hy with hb | ha
      · exact Or.inl ((memT _ _).mpr ⟨hb, hne⟩)
      · exact Or.inr ((memT _ _).mpr ⟨ha, hne⟩)
    hash_iff_queued := hc.hash_iff_queued
    order_ok := by
      intro t' x hx y hy
      obtain ⟨hx, hne⟩ := (memT t' x).mp hx
      obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := hc.order_ok t' x hx y hy
      exact ⟨r, hr, h1, by rw [lp x hne]; exact h2, h3, h4, h5⟩
    price_pos := by
      intro t' x hx
      obtain ⟨hx, hne⟩ := (memT t' x).mp hx
      rw [lp x hne]; exact hc.price_pos t' x hx
    uncrossed := by
      intro lb hb la ha
      obtain ⟨hb, hbne⟩ := (memT _ _).mp hb
      obtain ⟨ha, hane⟩ := (memT _ _).mp ha
      rw [lp lb hbne, lp la hane]; exact hc.uncrossed lb hb la ha }

theorem free_restingCount (_hw : db.WF) (hl : l ∈ db.tree t) (he : db.queue l = []) :
    restingCount (freeDb db t l) = restingCount db := by
  unfold restingCount
  simp only [List.map_append, List.sum_append_nat, freeDb]
  have hs := sum_map_erase (fun x => (db.queue x).length) hl
  simp only [he, List.length_nil, Nat.add_zero] at hs
  cases t <;> simp only [upd, reduceCtorEq, if_true, if_false] <;> omega

theorem free_tree_length (hl : l ∈ db.tree t) :
    ((freeDb db t l).tree .bids ++ (freeDb db t l).tree .asks).length + 1 =
      (db.tree .bids ++ db.tree .asks).length := by
  have e := List.length_erase_of_mem hl
  have p := List.length_pos_of_mem hl
  simp only [freeDb, List.length_append]
  cases t <;> simp only [upd, reduceCtorEq, if_true, if_false] <;> omega

theorem free_absSide (hw : db.WF) (hl : l ∈ db.tree t) :
    absSide (freeDb db t l) t = restSide db t l := by
  unfold absSide restSide
  simp only [freeDb, upd_same]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hxl : x ≠ l := fun e => by subst e; exact (hw.tree_nodup t).not_mem_erase hx
  exact absLevel_congr rfl (fun _ _ => rfl) (by simp only [Db.levelPrice, upd_other _ _ hxl])

theorem free_absSide_other (hw : db.WF) (hl : l ∈ db.tree t) {t' : Tree} (ht : t' ≠ t) :
    absSide (freeDb db t l) t' = absSide db t' := by
  unfold absSide
  simp only [freeDb, upd_other _ _ ht]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hxl : x ≠ l := tree_ne_of_mem hw hx hl ht
  exact absLevel_congr rfl (fun _ _ => rfl) (by simp only [Db.levelPrice, upd_other _ _ hxl])

end Views

-- ============================================================================
-- The store-level invariant inside an outer iteration
-- ============================================================================

variable {S : Type} [EngineDb S]

open EngineDb

/-- `Inv` with level `l0` allowed empty. -/
structure InvM (s : S) (l0 : LevelH) : Prop where
  wf : (view s).WF
  client : ClientInvM (view s) l0
  orders_resting : ∀ h, (view s).orderLive h ↔ (view s).queued h
  levels_resting : ∀ l, (view s).levelLive l ↔ (l ∈ (view s).tree .bids ∨ l ∈ (view s).tree .asks)
  count_eq : count s = restingCount (view s)
  levels_eq : levelsUsed s = ((view s).tree .bids ++ (view s).tree .asks).length
  count_le : count s ≤ capacity (S := S)

theorem Inv.toM {s : S} (hI : Inv s) (l0 : LevelH) : InvM s l0 :=
  ⟨hI.wf, ClientInv.toM hI.client l0, hI.orders_resting, hI.levels_resting, hI.count_eq, hI.levels_eq,
   hI.count_le⟩

theorem InvM.toInv {s : S} {l0 : LevelH} (hI : InvM s l0) (hne : (view s).queue l0 ≠ []) : Inv s :=
  ⟨hI.wf, ClientInvM.toInv hI.client (Or.inl hne), hI.orders_resting, hI.levels_resting, hI.count_eq,
   hI.levels_eq, hI.count_le⟩

/-- Under the client invariant, a tree holds no more levels than there are
    resting orders. -/
theorem levels_le_count {db : Db} (hc : ClientInv db) :
    (db.tree .bids ++ db.tree .asks).length ≤ restingCount db := by
  unfold restingCount
  have : ∀ (T : List LevelH), (∀ x ∈ T, db.queue x ≠ []) →
      T.length ≤ (T.map fun x => (db.queue x).length).sum := by
    intro T hT
    induction T with
    | nil => simp
    | cons x T ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 := hT x List.mem_cons_self
      have h2 := ih (fun y hy => hT y (List.mem_cons_of_mem _ hy))
      have : 0 < (db.queue x).length := List.length_pos_iff.mpr h1
      omega
  apply this
  intro x hx
  rcases List.mem_append.mp hx with hb | ha
  · exact hc.level_nonempty _ x hb
  · exact hc.level_nonempty _ x ha

end MatcherStore

import Bridge.EngineDbApi

/-!
# EngineDb API Laws

Consequences of the contract in `EngineDbApi.lean` that a client proof uses:

- `WF_empty` and `*_preserves_WF`: the representation invariant holds
  initially and every operation keeps it when called within its precondition.
- `hashFind_unique`, `tFind_unique`, `tBest_unique`: lookups are functional,
  so the relational postconditions determine the result.
- The storage laws: an inserted key is found, a removed key is not, the queue
  is FIFO, and every operation leaves the other indexes untouched.
-/

namespace EngineDbApi

open Db

theorem WF_empty : Db.empty.WF where
  queue_live := by intro l h hh; cases hh
  queue_nodup := by intro l; exact List.nodup_nil
  queue_unique := by intro l₁ l₂ h hh; cases hh
  hash_live := by intro h hh; cases hh
  hash_nodup := List.nodup_nil
  hash_ids := by intro h₁ hh; cases hh
  tree_live := by intro t l hl; cases hl
  tree_nodup := by intro t; exact List.nodup_nil
  tree_disjoint := by intro l hl; cases hl
  tree_prices := by intro t l₁ hl; cases hl
  orders_live := by intro h; simp [Db.orderLive, Db.empty]
  oLive_nodup := List.nodup_nil
  levels_live := by intro l; simp [Db.levelLive, Db.empty]
  lLive_nodup := List.nodup_nil

-- ============================================================================
-- Determinism of lookups
-- ============================================================================

theorem hashFind_unique {db : Db} (hw : db.WF) {id : UInt64} {r₁ r₂ : Option OrderH}
    (h₁ : hashFind.post db id r₁) (h₂ : hashFind.post db id r₂) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> simp only [hashFind.post] at h₁ h₂
  · rfl
  · exact absurd h₂.2 (h₁ _ h₂.1)
  · exact absurd h₁.2 (h₂ _ h₁.1)
  · rw [hw.hash_ids _ h₁.1 _ h₂.1 (h₁.2.trans h₂.2.symm)]

theorem tFind_unique {db : Db} (hw : db.WF) {t : Tree} {p : UInt64} {r₁ r₂ : Option LevelH}
    (h₁ : tFind.post db t p r₁) (h₂ : tFind.post db t p r₂) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> simp only [tFind.post] at h₁ h₂
  · rfl
  · exact absurd h₂.2 (h₁ _ h₂.1)
  · exact absurd h₁.2 (h₂ _ h₁.1)
  · rw [hw.tree_prices _ _ h₁.1 _ h₂.1 (h₁.2.trans h₂.2.symm)]

theorem better_antisymm {t : Tree} {p q : UInt64} (h₁ : better t p q) (h₂ : better t q p) :
    p = q := by
  cases t <;> simp only [better] at h₁ h₂ <;> exact UInt64.le_antisymm (by assumption) (by assumption)

theorem tBest_unique {db : Db} (hw : db.WF) {t : Tree} {r₁ r₂ : Option LevelH}
    (h₁ : tBest.post db t r₁) (h₂ : tBest.post db t r₂) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> simp only [tBest.post] at h₁ h₂
  · rfl
  · rw [h₁] at h₂; cases h₂.1
  · rw [h₂] at h₁; cases h₁.1
  · rename_i l₁ l₂
    have hp := better_antisymm (h₁.2 l₂ h₂.1) (h₂.2 l₁ h₁.1)
    rw [hw.tree_prices _ _ h₁.1 _ h₂.1 hp]

-- ============================================================================
-- Storage laws: what the client may rely on
-- ============================================================================

/-- Insert then find: after a successful hash insert, looking up the row's id
    returns that row, and nothing else satisfies the lookup. -/
theorem hash_find_after_insert {db db' : Db} {h : OrderH}
    (hw : db'.WF) (hpost : hashInsert.post db h true db') :
    hashFind.post db' (db'.orderId h) (some h) ∧
    ∀ r, hashFind.post db' (db'.orderId h) r → r = some h := by
  unfold hashInsert.post at hpost
  split at hpost
  · cases hpost.1
  · obtain ⟨-, rfl⟩ := hpost
    have hf : hashFind.post { db with hash := h :: db.hash } (Db.orderId _ h) (some h) :=
      ⟨List.mem_cons_self, rfl⟩
    exact ⟨hf, fun r hr => hashFind_unique hw hr hf⟩

/-- A refused insert means the id was already present, and nothing changed. -/
theorem hash_insert_refused {db db' : Db} {h : OrderH}
    (hpost : hashInsert.post db h false db') :
    db' = db ∧ ∃ h' ∈ db.hash, db.orderId h' = db.orderId h := by
  unfold hashInsert.post at hpost
  split at hpost
  · exact ⟨hpost.2, by assumption⟩
  · cases hpost.1

/-- Remove then find: after removing a row, its id is no longer found. -/
theorem hash_find_after_remove {db db' : Db} {h : OrderH}
    (hw : db.WF) (hpre : hashRemove.pre db h) (hpost : hashRemove.post db h db') :
    hashFind.post db' (db.orderId h) none := by
  subst hpost
  intro h' hh' heq
  have hne : h' ≠ h := by
    intro he; subst he
    exact (List.Nodup.not_mem_erase hw.hash_nodup) hh'
  exact hne (hw.hash_ids _ (List.mem_of_mem_erase hh') _ hpre heq)

/-- FIFO: `InsertTail` appends; the other queues are untouched. -/
theorem queue_after_insertTail {db db' : Db} {l : LevelH} {h : OrderH}
    (hpost : qInsertTail.post db l h db') :
    db'.queue l = db.queue l ++ [h] ∧ ∀ l', l' ≠ l → db'.queue l' = db.queue l' := by
  subst hpost
  exact ⟨upd_same _ _ _, fun l' hl => upd_other _ _ hl⟩

/-- FIFO: the first order of a level stays first until it is removed. -/
theorem first_stable_under_insertTail {db db' : Db} {l : LevelH} {h a : OrderH}
    (hfirst : (db.queue l).head? = some a) (hpost : qInsertTail.post db l h db') :
    (db'.queue l).head? = some a := by
  rw [(queue_after_insertTail hpost).1]
  cases hq : db.queue l with
  | nil => rw [hq] at hfirst; cases hfirst
  | cons x xs => rw [hq] at hfirst; simpa using hfirst

/-- Removing the head of a queue makes the next order the head. -/
theorem first_after_remove_head {db db' : Db} {l : LevelH} {a : OrderH} {rest : List OrderH}
    (hq : db.queue l = a :: rest) (hpost : qRemove.post db l a db') :
    db'.queue l = rest := by
  subst hpost
  simp [hq]

/-- Tree insert then find: the inserted level is found at its price. -/
theorem tree_find_after_insert {db db' : Db} {t : Tree} {l : LevelH}
    (hw : db'.WF) (hpost : tInsert.post db t l db') :
    ∀ r, tFind.post db' t (db'.levelPrice l) r → r = some l := by
  intro r hr
  have hf : tFind.post db' t (db'.levelPrice l) (some l) := by
    subst hpost
    exact ⟨by simp, rfl⟩
  exact tFind_unique hw hr hf

/-- Tree remove then find: the removed price is no longer found. -/
theorem tree_find_after_remove {db db' : Db} {t : Tree} {l : LevelH}
    (hw : db.WF) (hpre : tRemove.pre db t l) (hpost : tRemove.post db t l db') :
    tFind.post db' t (db.levelPrice l) none := by
  subst hpost
  intro l' hl' heq
  simp only [upd_same] at hl'
  have hne : l' ≠ l := by
    intro he; subst he
    exact (List.Nodup.not_mem_erase (hw.tree_nodup t)) hl'
  exact hne (hw.tree_prices t _ (List.mem_of_mem_erase hl') _ hpre heq)

-- ============================================================================
-- Every operation preserves WF
-- ============================================================================

section Preservation

variable {db db' : Db}

private theorem live_alloc {α β : Type} [DecidableEq α] {f : α → Option β} {L : List α}
    (hf : ∀ x, (f x).isSome = true ↔ x ∈ L) (h : α) (v : β) :
    ∀ x, (upd f h (some v) x).isSome = true ↔ x ∈ h :: L := by
  intro x
  by_cases he : x = h
  · subst he; simp
  · rw [upd_other _ _ he, hf x]; simp [he]

private theorem live_write {α β : Type} [DecidableEq α] {f : α → Option β} {L : List α}
    (hf : ∀ x, (f x).isSome = true ↔ x ∈ L) {h : α} (hh : h ∈ L) (v : β) :
    ∀ x, (upd f h (some v) x).isSome = true ↔ x ∈ L := by
  intro x
  by_cases he : x = h
  · subst he; simp [hh]
  · rw [upd_other _ _ he, hf x]

private theorem live_free {α β : Type} [DecidableEq α] {f : α → Option β} {L : List α}
    (hf : ∀ x, (f x).isSome = true ↔ x ∈ L) (hn : L.Nodup) (h : α) :
    ∀ x, (upd f h none x).isSome = true ↔ x ∈ L.erase h := by
  intro x
  by_cases he : x = h
  · subst he; simp [hn.not_mem_erase]
  · rw [upd_other _ _ he, hf x, List.mem_erase_of_ne he]

private theorem orderId_upd_other (db : Db) {h x : OrderH} (r : Option OrderRow) (hx : x ≠ h) :
    Db.orderId { db with orders := upd db.orders h r } x = db.orderId x := by
  simp [Db.orderId, upd_other _ _ hx]

private theorem orderLive_upd_other (db : Db) {h x : OrderH} (r : Option OrderRow) (hx : x ≠ h) :
    Db.orderLive { db with orders := upd db.orders h r } x = db.orderLive x := by
  simp [Db.orderLive, upd_other _ _ hx]

private theorem levelPrice_upd_other (db : Db) {l x : LevelH} (r : Option LevelRow) (hx : x ≠ l) :
    Db.levelPrice { db with levels := upd db.levels l r } x = db.levelPrice x := by
  simp [Db.levelPrice, upd_other _ _ hx]

private theorem levelLive_upd_other (db : Db) {l x : LevelH} (r : Option LevelRow) (hx : x ≠ l) :
    Db.levelLive { db with levels := upd db.levels l r } x = db.levelLive x := by
  simp [Db.levelLive, upd_other _ _ hx]

theorem mapTotal_isSome (db : Db) (l x : LevelH) (f : UInt64 → UInt64) :
    (db.mapTotal l f x).isSome = (db.levels x).isSome := by
  by_cases he : x = l
  · subst he; cases hl : db.levels x <;> simp [Db.mapTotal, hl]
  · simp [Db.mapTotal, upd_other _ _ he]

theorem mapTotal_priceOf (db : Db) (l x : LevelH) (f : UInt64 → UInt64) :
    (db.mapTotal l f x).map LevelRow.price = (db.levels x).map LevelRow.price := by
  by_cases he : x = l
  · subst he; cases hl : db.levels x <;> simp [Db.mapTotal, hl]
  · simp [Db.mapTotal, upd_other _ _ he]

theorem orderAlloc_preserves_WF {r : Option OrderH}
    (hw : db.WF) (hpost : orderAlloc.post db r db') : db'.WF := by
  cases r with
  | none => subst hpost; exact hw
  | some h =>
    obtain ⟨hdead, row, rfl⟩ := hpost
    have hnot : ∀ x, db.orderLive x → x ≠ h := by
      intro x hx he; subst he; simp [Db.orderLive, hdead] at hx
    refine { hw with
    queue_live := ?_, hash_live := ?_, hash_ids := ?_, orders_live := ?_, oLive_nodup := ?_ }
    · intro l x hx
      have := hw.queue_live l x hx
      exact ⟨by simp only [Db.orderLive, upd_other _ _ (hnot x this.1)]; exact this.1, this.2⟩
    · intro x hx
      have := hw.hash_live x hx
      simp only [Db.orderLive, upd_other _ _ (hnot x this)]; exact this
    · intro x₁ h₁ x₂ h₂ he
      simp only [Db.orderId, upd_other _ _ (hnot _ (hw.hash_live _ h₁)),
        upd_other _ _ (hnot _ (hw.hash_live _ h₂))] at he
      exact hw.hash_ids _ h₁ _ h₂ he
    · exact live_alloc hw.orders_live h row
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, hw.oLive_nodup⟩
      have := (hw.orders_live h).mpr hm
      simp [Db.orderLive, hdead] at this

theorem orderFree_preserves_WF {h : OrderH}
    (hw : db.WF) (hpre : orderFree.pre db h) (hpost : orderFree.post db h db') : db'.WF := by
  subst hpost
  obtain ⟨-, hnq, hnh⟩ := hpre
  have hq : ∀ l x, x ∈ db.queue l → x ≠ h := fun l x hx he => hnq ⟨l, he ▸ hx⟩
  have hh : ∀ x ∈ db.hash, x ≠ h := fun x hx he => hnh (he ▸ hx)
  refine { hw with
    queue_live := ?_, hash_live := ?_, hash_ids := ?_, orders_live := ?_, oLive_nodup := ?_ }
  · intro l x hx
    have := hw.queue_live l x hx
    exact ⟨by simp only [Db.orderLive, upd_other _ _ (hq l x hx)]; exact this.1, this.2⟩
  · intro x hx
    simp only [Db.orderLive, upd_other _ _ (hh x hx)]; exact hw.hash_live x hx
  · intro x₁ h₁ x₂ h₂ he
    simp only [Db.orderId, upd_other _ _ (hh _ h₁), upd_other _ _ (hh _ h₂)] at he
    exact hw.hash_ids _ h₁ _ h₂ he
  · exact live_free hw.orders_live hw.oLive_nodup h
  · exact hw.oLive_nodup.erase h

theorem levelAlloc_preserves_WF {r : Option LevelH}
    (hw : db.WF) (hpost : levelAlloc.post db r db') : db'.WF := by
  cases r with
  | none => subst hpost; exact hw
  | some l =>
    obtain ⟨hdead, row, rfl⟩ := hpost
    have hnot : ∀ x, db.levelLive x → x ≠ l := by
      intro x hx he; subst he; simp [Db.levelLive, hdead] at hx
    refine { hw with
    queue_live := ?_, tree_live := ?_, tree_prices := ?_, levels_live := ?_, lLive_nodup := ?_ }
    · intro l' x hx
      have := hw.queue_live l' x hx
      exact ⟨this.1, by simp only [Db.levelLive, upd_other _ _ (hnot l' this.2)]; exact this.2⟩
    · intro t x hx
      simp only [Db.levelLive, upd_other _ _ (hnot x (hw.tree_live t x hx))]
      exact hw.tree_live t x hx
    · intro t x₁ h₁ x₂ h₂ he
      simp only [Db.levelPrice, upd_other _ _ (hnot _ (hw.tree_live t _ h₁)),
        upd_other _ _ (hnot _ (hw.tree_live t _ h₂))] at he
      exact hw.tree_prices t _ h₁ _ h₂ he
    · exact live_alloc hw.levels_live l row
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, hw.lLive_nodup⟩
      have := (hw.levels_live l).mpr hm
      simp [Db.levelLive, hdead] at this

theorem levelFree_preserves_WF {l : LevelH}
    (hw : db.WF) (hpre : levelFree.pre db l) (hpost : levelFree.post db l db') : db'.WF := by
  subst hpost
  obtain ⟨-, hnb, hna, hempty⟩ := hpre
  have ht : ∀ t, ∀ x ∈ db.tree t, x ≠ l := by
    intro t x hx he; subst he; cases t
    · exact hnb hx
    · exact hna hx
  refine { hw with
    queue_live := ?_, tree_live := ?_, tree_prices := ?_, levels_live := ?_, lLive_nodup := ?_ }
  · intro l' x hx
    have := hw.queue_live l' x hx
    have hne : l' ≠ l := by intro he; subst he; rw [hempty] at hx; cases hx
    exact ⟨this.1, by simp only [Db.levelLive, upd_other _ _ hne]; exact this.2⟩
  · intro t x hx
    simp only [Db.levelLive, upd_other _ _ (ht t x hx)]; exact hw.tree_live t x hx
  · intro t x₁ h₁ x₂ h₂ he
    simp only [Db.levelPrice, upd_other _ _ (ht t _ h₁), upd_other _ _ (ht t _ h₂)] at he
    exact hw.tree_prices t _ h₁ _ h₂ he
  · exact live_free hw.levels_live hw.lLive_nodup l
  · exact hw.lLive_nodup.erase l

theorem writeOrder_preserves_WF {h : OrderH} {row : OrderRow}
    (hw : db.WF) (hpre : writeOrder.pre db h row) (hpost : writeOrder.post db h row db') :
    db'.WF := by
  subst hpost
  obtain ⟨old, hold, hkey⟩ := hpre
  have hid : ∀ x ∈ db.hash, Db.orderId { db with orders := upd db.orders h (some row) } x =
      db.orderId x := by
    intro x hx
    by_cases he : x = h
    · subst he; simp [Db.orderId, hold, hkey hx]
    · exact orderId_upd_other _ _ he
  have hlive : ∀ x, db.orderLive x → Db.orderLive
      { db with orders := upd db.orders h (some row) } x := by
    intro x hx
    by_cases he : x = h
    · subst he; simp [Db.orderLive]
    · simp only [Db.orderLive, upd_other _ _ he]; exact hx
  refine { hw with queue_live := ?_, hash_live := ?_, hash_ids := ?_, orders_live := ?_ }
  · intro l x hx
    have := hw.queue_live l x hx
    exact ⟨hlive x this.1, this.2⟩
  · intro x hx; exact hlive x (hw.hash_live x hx)
  · intro x₁ h₁ x₂ h₂ he
    rw [hid _ h₁, hid _ h₂] at he
    exact hw.hash_ids _ h₁ _ h₂ he
  · exact live_write hw.orders_live ((hw.orders_live h).mp (by simp [Db.orderLive, hold])) row

theorem writeLevel_preserves_WF {l : LevelH} {row : LevelRow}
    (hw : db.WF) (hpre : writeLevel.pre db l row) (hpost : writeLevel.post db l row db') :
    db'.WF := by
  subst hpost
  obtain ⟨old, hold, hkey⟩ := hpre
  have hprice : ∀ t, ∀ x ∈ db.tree t, Db.levelPrice
      { db with levels := upd db.levels l (some row) } x = db.levelPrice x := by
    intro t x hx
    by_cases he : x = l
    · subst he
      have : x ∈ db.tree .bids ∨ x ∈ db.tree .asks := by cases t <;> simp_all
      simp [Db.levelPrice, hold, hkey this]
    · exact levelPrice_upd_other _ _ he
  have hlive : ∀ x, db.levelLive x → Db.levelLive
      { db with levels := upd db.levels l (some row) } x := by
    intro x hx
    by_cases he : x = l
    · subst he; simp [Db.levelLive]
    · simp only [Db.levelLive, upd_other _ _ he]; exact hx
  refine { hw with queue_live := ?_, tree_live := ?_, tree_prices := ?_, levels_live := ?_ }
  · intro l' x hx
    have := hw.queue_live l' x hx
    exact ⟨this.1, hlive l' this.2⟩
  · intro t x hx; exact hlive x (hw.tree_live t x hx)
  · intro t x₁ h₁ x₂ h₂ he
    rw [hprice t _ h₁, hprice t _ h₂] at he
    exact hw.tree_prices t _ h₁ _ h₂ he
  · exact live_write hw.levels_live ((hw.levels_live l).mp (by simp [Db.levelLive, hold])) row

theorem hashInsert_preserves_WF {h : OrderH} {ok : Bool}
    (hw : db.WF) (hpre : hashInsert.pre db h) (hpost : hashInsert.post db h ok db') :
    db'.WF := by
  unfold hashInsert.post at hpost
  split at hpost
  · rw [hpost.2]; exact hw
  · rename_i hfresh
    obtain ⟨-, rfl⟩ := hpost
    refine { hw with hash_live := ?_, hash_nodup := ?_, hash_ids := ?_ }
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpre.1
      · exact hw.hash_live x hx
    · exact List.nodup_cons.mpr ⟨hpre.2, hw.hash_nodup⟩
    · intro x₁ h₁ x₂ h₂ he
      dsimp only at h₁ h₂ he
      rcases List.mem_cons.mp h₁ with e₁ | m₁ <;> rcases List.mem_cons.mp h₂ with e₂ | m₂
      · rw [e₁, e₂]
      · subst e₁; exact absurd ⟨x₂, m₂, he.symm⟩ hfresh
      · subst e₂; exact absurd ⟨x₁, m₁, he⟩ hfresh
      · exact hw.hash_ids _ m₁ _ m₂ he

theorem hashRemove_preserves_WF {h : OrderH}
    (hw : db.WF) (hpost : hashRemove.post db h db') : db'.WF := by
  subst hpost
  refine { hw with hash_live := ?_, hash_nodup := ?_, hash_ids := ?_ }
  · intro x hx; exact hw.hash_live x (List.mem_of_mem_erase hx)
  · exact hw.hash_nodup.erase h
  · intro x₁ h₁ x₂ h₂ he
    exact hw.hash_ids _ (List.mem_of_mem_erase h₁) _ (List.mem_of_mem_erase h₂) he

theorem qInsertTail_preserves_WF {l : LevelH} {h : OrderH}
    (hw : db.WF) (hpre : qInsertTail.pre db l h) (hpost : qInsertTail.post db l h db') :
    db'.WF := by
  subst hpost
  obtain ⟨hl, hh, hnq⟩ := hpre
  have hmem : ∀ l' x, x ∈ upd db.queue l (db.queue l ++ [h]) l' →
      x ∈ db.queue l' ∨ (l' = l ∧ x = h) := by
    intro l' x hx
    by_cases he : l' = l
    · subst he; simp only [upd_same, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨rfl, hx⟩
    · rw [upd_other _ _ he] at hx; exact Or.inl hx
  refine { hw with
    queue_live := ?_, queue_nodup := ?_, queue_unique := ?_, tree_live := ?_, tree_prices := ?_,
    levels_live := ?_ }
  · intro l' x hx
    simp only [Db.levelLive, mapTotal_isSome]
    rcases hmem l' x hx with hx | ⟨rfl, rfl⟩
    · exact hw.queue_live l' x hx
    · exact ⟨hh, hl⟩
  · intro l'
    by_cases he : l' = l
    · subst he
      simp only [upd_same]
      exact List.nodup_append.mpr ⟨hw.queue_nodup l', List.nodup_cons.mpr
        ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun a ha b hb => by
          simp only [List.mem_singleton] at hb; subst hb
          intro hab; subst hab; exact hnq ⟨l', ha⟩⟩
    · simp only [upd_other _ _ he]; exact hw.queue_nodup l'
  · intro l₁ l₂ x h₁ h₂
    rcases hmem l₁ x h₁ with m₁ | ⟨e₁, x₁⟩ <;> rcases hmem l₂ x h₂ with m₂ | ⟨e₂, x₂⟩
    · exact hw.queue_unique _ _ _ m₁ m₂
    · subst x₂; exact absurd ⟨l₁, m₁⟩ hnq
    · subst x₁; exact absurd ⟨l₂, m₂⟩ hnq
    · rw [e₁, e₂]
  · intro t x hx; simp only [Db.levelLive, mapTotal_isSome]; exact hw.tree_live t x hx
  · intro t x₁ h₁ x₂ h₂ he
    simp only [Db.levelPrice, mapTotal_priceOf] at he
    exact hw.tree_prices t _ h₁ _ h₂ he
  · intro x; simp only [Db.levelLive, mapTotal_isSome]; exact hw.levels_live x

theorem qRemove_preserves_WF {l : LevelH} {h : OrderH}
    (hw : db.WF) (hpost : qRemove.post db l h db') : db'.WF := by
  subst hpost
  have hsub : ∀ l' x, x ∈ upd db.queue l ((db.queue l).erase h) l' → x ∈ db.queue l' := by
    intro l' x hx
    by_cases he : l' = l
    · subst he; simp only [upd_same] at hx; exact List.mem_of_mem_erase hx
    · rw [upd_other _ _ he] at hx; exact hx
  refine { hw with
    queue_live := ?_, queue_nodup := ?_, queue_unique := ?_, tree_live := ?_, tree_prices := ?_,
    levels_live := ?_ }
  · intro l' x hx; simp only [Db.levelLive, mapTotal_isSome]; exact hw.queue_live l' x (hsub l' x hx)
  · intro l'
    by_cases he : l' = l
    · subst he; simp only [upd_same]; exact (hw.queue_nodup l').erase h
    · simp only [upd_other _ _ he]; exact hw.queue_nodup l'
  · intro l₁ l₂ x h₁ h₂
    exact hw.queue_unique _ _ _ (hsub _ _ h₁) (hsub _ _ h₂)
  · intro t x hx; simp only [Db.levelLive, mapTotal_isSome]; exact hw.tree_live t x hx
  · intro t x₁ h₁ x₂ h₂ he
    simp only [Db.levelPrice, mapTotal_priceOf] at he
    exact hw.tree_prices t _ h₁ _ h₂ he
  · intro x; simp only [Db.levelLive, mapTotal_isSome]; exact hw.levels_live x

theorem tInsert_preserves_WF {t : Tree} {l : LevelH}
    (hw : db.WF) (hpre : tInsert.pre db t l) (hpost : tInsert.post db t l db') : db'.WF := by
  subst hpost
  obtain ⟨hl, hnb, hna, hfresh⟩ := hpre
  have hmem : ∀ t' x, x ∈ upd db.tree t (l :: db.tree t) t' →
      x ∈ db.tree t' ∨ (t' = t ∧ x = l) := by
    intro t' x hx
    by_cases he : t' = t
    · subst he; simp only [upd_same, List.mem_cons] at hx
      rcases hx with hx | hx
      · exact Or.inr ⟨rfl, hx⟩
      · exact Or.inl hx
    · rw [upd_other _ _ he] at hx; exact Or.inl hx
  have hnot : ∀ t', l ∉ db.tree t' := by intro t'; cases t' <;> assumption
  refine { hw with tree_live := ?_, tree_nodup := ?_, tree_disjoint := ?_, tree_prices := ?_ }
  · intro t' x hx
    rcases hmem t' x hx with hx | ⟨-, rfl⟩
    · exact hw.tree_live t' x hx
    · exact hl
  · intro t'
    by_cases he : t' = t
    · subst he; simp only [upd_same]
      exact List.nodup_cons.mpr ⟨hnot t', hw.tree_nodup t'⟩
    · simp only [upd_other _ _ he]; exact hw.tree_nodup t'
  · intro x hb ha
    rcases hmem _ x hb with mb | ⟨eb, xb⟩ <;> rcases hmem _ x ha with ma | ⟨ea, xa⟩
    · exact hw.tree_disjoint x mb ma
    · subst xa; exact hnb mb
    · subst xb; exact hna ma
    · rw [← ea] at eb; cases eb
  · intro t' x₁ h₁ x₂ h₂ he
    rcases hmem t' x₁ h₁ with m₁ | ⟨e₁, y₁⟩ <;> rcases hmem _ x₂ h₂ with m₂ | ⟨e₂, y₂⟩
    · simp only [Db.levelPrice] at he
      exact hw.tree_prices t' _ m₁ _ m₂ he
    · subst y₂ e₂; exact absurd he (hfresh _ m₁)
    · subst y₁ e₁; exact absurd he.symm (hfresh _ m₂)
    · rw [y₁, y₂]

theorem tRemove_preserves_WF {t : Tree} {l : LevelH}
    (hw : db.WF) (hpost : tRemove.post db t l db') : db'.WF := by
  subst hpost
  have hsub : ∀ t' x, x ∈ upd db.tree t ((db.tree t).erase l) t' → x ∈ db.tree t' := by
    intro t' x hx
    by_cases he : t' = t
    · subst he; simp only [upd_same] at hx; exact List.mem_of_mem_erase hx
    · rw [upd_other _ _ he] at hx; exact hx
  refine { hw with tree_live := ?_, tree_nodup := ?_, tree_disjoint := ?_, tree_prices := ?_ }
  · intro t' x hx; exact hw.tree_live t' x (hsub t' x hx)
  · intro t'
    by_cases he : t' = t
    · subst he; simp only [upd_same]; exact (hw.tree_nodup t').erase l
    · simp only [upd_other _ _ he]; exact hw.tree_nodup t'
  · intro x hb ha; exact hw.tree_disjoint x (hsub _ x hb) (hsub _ x ha)
  · intro t' x₁ h₁ x₂ h₂ he
    exact hw.tree_prices t' _ (hsub _ _ h₁) _ (hsub _ _ h₂) he

end Preservation

-- ============================================================================
-- Handle validity (§4): which handles each operation keeps valid
-- ============================================================================

section Validity

variable {db db' : Db}

/-- An order handle is valid while its row is live; likewise a level handle. -/
abbrev Db.validO (db : Db) (h : OrderH) : Prop := db.orderLive h
abbrev Db.validL (db : Db) (l : LevelH) : Prop := db.levelLive l

theorem mem_nextIn {xs : List Nat} {x y : Nat} (h : nextIn xs x = some y) : y ∈ xs := by
  induction xs with
  | nil => simp [nextIn] at h
  | cons a rest ih =>
    cases rest with
    | nil => simp [nextIn] at h
    | cons b rest' =>
      simp only [nextIn] at h
      split at h
      · cases h; simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- Allocation that succeeds returns a handle that is now valid, and changes
    the validity of no other handle. -/
theorem orderAlloc_valid {h : OrderH} (hpost : orderAlloc.post db (some h) db') :
    db'.validO h ∧ ∀ x, x ≠ h → (db'.validO x ↔ db.validO x) := by
  obtain ⟨-, row, rfl⟩ := hpost
  refine ⟨by simp [Db.orderLive], fun x hx => ?_⟩
  simp [Db.orderLive, upd_other _ _ hx]

/-- Allocation that fails (`full`) leaves the store unchanged. -/
theorem orderAlloc_full (hpost : orderAlloc.post db none db') : db' = db := hpost

/-- `Free` invalidates the freed handle and nothing else. -/
theorem orderFree_valid {h : OrderH} (hpost : orderFree.post db h db') :
    ¬ db'.validO h ∧ ∀ x, x ≠ h → (db'.validO x ↔ db.validO x) := by
  subst hpost
  refine ⟨by simp [Db.orderLive], fun x hx => ?_⟩
  simp [Db.orderLive, upd_other _ _ hx]

theorem levelAlloc_valid {l : LevelH} (hpost : levelAlloc.post db (some l) db') :
    db'.validL l ∧ ∀ x, x ≠ l → (db'.validL x ↔ db.validL x) := by
  obtain ⟨-, row, rfl⟩ := hpost
  refine ⟨by simp [Db.levelLive], fun x hx => ?_⟩
  simp [Db.levelLive, upd_other _ _ hx]

theorem levelAlloc_full (hpost : levelAlloc.post db none db') : db' = db := hpost

theorem levelFree_valid {l : LevelH} (hpost : levelFree.post db l db') :
    ¬ db'.validL l ∧ ∀ x, x ≠ l → (db'.validL x ↔ db.validL x) := by
  subst hpost
  refine ⟨by simp [Db.levelLive], fun x hx => ?_⟩
  simp [Db.levelLive, upd_other _ _ hx]

/-- The other pool changes no order handle's validity. -/
theorem levelAlloc_validO {r : Option LevelH} (hpost : levelAlloc.post db r db') (x : OrderH) :
    db'.validO x ↔ db.validO x := by
  cases r with
  | none => rw [hpost]
  | some l => obtain ⟨-, row, rfl⟩ := hpost; rfl

theorem levelFree_validO {l : LevelH} (hpost : levelFree.post db l db') (x : OrderH) :
    db'.validO x ↔ db.validO x := by subst hpost; rfl

theorem orderAlloc_validL {r : Option OrderH} (hpost : orderAlloc.post db r db') (x : LevelH) :
    db'.validL x ↔ db.validL x := by
  cases r with
  | none => rw [hpost]
  | some h => obtain ⟨-, row, rfl⟩ := hpost; rfl

theorem orderFree_validL {h : OrderH} (hpost : orderFree.post db h db') (x : LevelH) :
    db'.validL x ↔ db.validL x := by subst hpost; rfl

/-- Writes through a valid handle keep every handle's validity. -/
theorem writeOrder_valid {h : OrderH} {row : OrderRow} (hpre : writeOrder.pre db h row)
    (hpost : writeOrder.post db h row db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  subst hpost
  obtain ⟨old, hold, -⟩ := hpre
  refine ⟨fun x => ?_, fun x => Iff.rfl⟩
  by_cases he : x = h
  · subst he; simp [Db.orderLive, hold]
  · simp [Db.orderLive, upd_other _ _ he]

theorem writeLevel_valid {l : LevelH} {row : LevelRow} (hpre : writeLevel.pre db l row)
    (hpost : writeLevel.post db l row db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  subst hpost
  obtain ⟨old, hold, -⟩ := hpre
  refine ⟨fun x => Iff.rfl, fun x => ?_⟩
  by_cases he : x = l
  · subst he; simp [Db.levelLive, hold]
  · simp [Db.levelLive, upd_other _ _ he]

/-- Index operations (hash, queue, tree) change no handle's validity. -/
theorem hashInsert_valid {h : OrderH} {ok : Bool} (hpost : hashInsert.post db h ok db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  unfold hashInsert.post at hpost
  split at hpost
  · rw [hpost.2]; exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · rw [hpost.2]; exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem hashRemove_valid {h : OrderH} (hpost : hashRemove.post db h db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  subst hpost; exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem qInsertTail_valid {l : LevelH} {h : OrderH} (hpost : qInsertTail.post db l h db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  subst hpost
  exact ⟨fun _ => Iff.rfl, fun x => by simp only [Db.levelLive, mapTotal_isSome]⟩

theorem qRemove_valid {l : LevelH} {h : OrderH} (hpost : qRemove.post db l h db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  subst hpost
  exact ⟨fun _ => Iff.rfl, fun x => by simp only [Db.levelLive, mapTotal_isSome]⟩

theorem tInsert_valid {t : Tree} {l : LevelH} (hpost : tInsert.post db t l db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  subst hpost; exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem tRemove_valid {t : Tree} {l : LevelH} (hpost : tRemove.post db t l db') :
    (∀ x, db'.validO x ↔ db.validO x) ∧ (∀ x, db'.validL x ↔ db.validL x) := by
  subst hpost; exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- Every lookup returns a valid handle or `none`. -/
theorem hashFind_valid (hw : db.WF) {id : UInt64} {h : OrderH}
    (hpost : hashFind.post db id (some h)) : db.validO h := hw.hash_live h hpost.1

theorem tFind_valid (hw : db.WF) {t : Tree} {p : UInt64} {l : LevelH}
    (hpost : tFind.post db t p (some l)) : db.validL l := hw.tree_live t l hpost.1

theorem tBest_valid (hw : db.WF) {t : Tree} {l : LevelH}
    (hpost : tBest.post db t (some l)) : db.validL l := hw.tree_live t l hpost.1

theorem qFirst_valid (hw : db.WF) {l : LevelH} {h : OrderH}
    (hpost : qFirst.post db l (some h)) : db.validO h :=
  (hw.queue_live l h (List.mem_of_mem_head? hpost.symm)).1

theorem qNext_valid (hw : db.WF) {h h' : OrderH}
    (hpost : qNext.post db h (some h')) : db.validO h' := by
  obtain ⟨l, -, hr⟩ := hpost
  exact (hw.queue_live l h' (mem_nextIn hr.symm)).1

theorem owner_valid (hw : db.WF) {h : OrderH} {l : LevelH}
    (hpost : owner.post db h (some l)) : db.validL l := (hw.queue_live l h hpost).2

end Validity

end EngineDbApi

import Walk.Equiv
import Matcher.Accept

/-!
# A3 infrastructure: `Inv` implies `WF`

`WF_of_Inv`: `main`'s store invariant `Inv s`, with `CapOk S`, gives the
walk's book hypothesis `WF (capacity S) (absBook (view s))`, clause by clause.
Nothing is added to `Inv` and nothing is weakened in `WF`.

Counted as infrastructure in A4: it is a fact about the decoding of a store,
needed by any route that states its spec hypothesis on the decoded book.
-/

namespace Walk

open EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel MatcherStore

-- ============================================================================
-- Generic list facts
-- ============================================================================

theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: as, hn, hi => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj (List.nodup_cons.mp hn).2
      (fun x hx y hy => hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
    have := hi y (List.mem_cons_of_mem _ hy) a List.mem_cons_self e
    subst this
    exact (List.nodup_cons.mp hn).1 hy

theorem nodup_flatMap_of {α β : Type} {Q : α → List β} :
    ∀ {T : List α}, T.Nodup → (∀ x ∈ T, (Q x).Nodup) →
      (∀ x ∈ T, ∀ y ∈ T, ∀ b, b ∈ Q x → b ∈ Q y → x = y) → (T.flatMap Q).Nodup
  | [], _, _, _ => List.nodup_nil
  | a :: as, hn, hq, hu => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hq a List.mem_cons_self,
      nodup_flatMap_of (List.nodup_cons.mp hn).2 (fun x hx => hq x (List.mem_cons_of_mem _ hx))
        (fun x hx y hy => hu x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)), ?_⟩
    intro b hb b' hb' e
    subst e
    obtain ⟨y, hy, hby⟩ := List.mem_flatMap.mp hb'
    have := hu a List.mem_cons_self y (List.mem_cons_of_mem _ hy) b hb hby
    subst this
    exact (List.nodup_cons.mp hn).1 hy

-- ============================================================================
-- Decoded ids
-- ============================================================================

theorem absQueue_ids (db : Db) (t : Tree) :
    ∀ (i : Nat) (hs : List OrderH), (absQueue db t i hs).map (·.id) =
      hs.map fun h => (rowOf db h).id.toNat
  | _, [] => rfl
  | i, _ :: hs => by simp [absQueue, absQueue_ids db t (i + 1) hs, restingOrder, rowOf]

theorem absSide_ids_perm (db : Db) (t : Tree) :
    (((absSide db t).flatMap (·.orders)).map (·.id)).Perm
      (((db.tree t).flatMap db.queue).map fun h => (rowOf db h).id.toNat) := by
  unfold absSide
  have hp := ((sortLevels_perm t ((db.tree t).map (absLevel db t))).flatMap_right (·.orders)).map
    (·.id)
  refine hp.trans ?_
  rw [List.flatMap_map, List.map_flatMap, List.map_flatMap]
  apply List.Perm.of_eq
  congr 1
  funext l
  simp only [absLevel]
  exact absQueue_ids db t 0 _

/-- **`Inv` implies `WF`** on the decoded book. -/
theorem WF_of_Inv {S : Type} [EngineDb S] {s : S} (hI : Inv s) (hcap : CapOk S) :
    WF (EngineDb.capacity (S := S)) (absBook (EngineDb.view s)) := by
  have hw := hI.wf
  have hc := hI.client
  have h2 := hI.count_eq
  have h3 := hI.count_le
  generalize EngineDb.view s = db at hw hc h2 ⊢
  -- the decoded orders of tree `t`
  have mem_side : ∀ t, ∀ l ∈ sideL (absBook db) t, ∃ lh ∈ db.tree t, l = absLevel db t lh := by
    intro t l hl
    have : l ∈ absSide db t := by cases t <;> exact hl
    obtain ⟨lh, hlh, e⟩ := List.mem_map.mp (mem_sortLevels.mp this)
    exact ⟨lh, hlh, e.symm⟩
  refine ⟨hcap, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- count
    have h1 := bookSize_absBook db
    rw [count_eq_bookSize rfl, h1]
    omega
  · -- no empty level
    intro t l hl
    obtain ⟨lh, hlh, rfl⟩ := mem_side t l hl
    exact absQueue_ne_nil (hc.level_nonempty t lh hlh)
  · -- resting orders
    intro t l hl o ho
    obtain ⟨lh, hlh, rfl⟩ := mem_side t l hl
    obtain ⟨h, hh, j, -, -, rfl⟩ := mem_absQueue ho
    obtain ⟨row, hrow, -, -, hpos, -, -⟩ := hc.order_ok t lh hlh h hh
    refine ⟨?_, rfl, rfl, rfl⟩
    simp only [restingOrder, hrow, Option.getD_some]
    exact UInt64.lt_iff_toNat_lt.mp hpos
  · -- unique ids
    have hperm : ((allBookOrders (absBook db)).map (·.id)).Perm
        ((((db.tree .bids).flatMap db.queue) ++ ((db.tree .asks).flatMap db.queue)).map
          fun h => (rowOf db h).id.toNat) := by
      simp only [allBookOrders, absBook, List.map_append]
      exact (absSide_ids_perm db .bids).append (absSide_ids_perm db .asks)
    rw [hperm.nodup_iff, ← List.flatMap_append]
    apply nodup_map_of_inj
    · apply nodup_flatMap_of
      · rw [List.nodup_append]
        exact ⟨hw.tree_nodup _, hw.tree_nodup _, fun a ha b hb e => by
          subst e; exact hw.tree_disjoint a ha hb⟩
      · intro x _; exact hw.queue_nodup x
      · intro x _ y _ b hbx hby; exact hw.queue_unique x y b hbx hby
    · intro x hx y hy e
      obtain ⟨lx, -, hlx⟩ := List.mem_flatMap.mp hx
      obtain ⟨ly, -, hly⟩ := List.mem_flatMap.mp hy
      have hxh : x ∈ db.hash := (hc.hash_iff_queued x).mpr ⟨lx, hlx⟩
      have hyh : y ∈ db.hash := (hc.hash_iff_queued y).mpr ⟨ly, hly⟩
      apply hw.hash_ids x hxh y hyh
      obtain ⟨rx, hrx⟩ := Option.isSome_iff_exists.mp (hw.hash_live x hxh)
      obtain ⟨ry, hry⟩ := Option.isSome_iff_exists.mp (hw.hash_live y hyh)
      simp only [rowOf, hrx, hry, Option.getD_some] at e
      simp only [Db.orderId, hrx, hry, Option.map_some, Option.getD_some]
      exact UInt64.toNat_inj.mp e
  · -- sorted sides
    intro t
    have := absSide_pairwise hw t
    cases t <;> exact this

end Walk

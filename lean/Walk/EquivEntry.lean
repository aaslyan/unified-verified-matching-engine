import Walk.Basic
import Matcher.Run

/-!
# A2, part 1: entry checks and cancel

`WF cap b` is what the equivalence needs of the book: the facts every book the
C can hold has, stated on the reference `BookState`. The entry checks of
`Walk.processOrder` are `staticCode` (the request-only checks, shared with
`main`) followed by the duplicate and capacity checks; `processB` makes the
same decisions (`processB_static`, `processB_after_static` on `main`). A
cancel gives exactly `processB`'s result.
-/

namespace Walk

open EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherSpec

/-- What the equivalence needs of a book. -/
structure WF (cap : Nat) (b : BookState) : Prop where
  cap64    : cap + 1 < 2 ^ 64
  stops    : b.stops = []
  count    : count b ≤ cap
  nonempty : ∀ t, ∀ l ∈ sideL b t, l.orders ≠ []
  resting  : ∀ t, ∀ l ∈ sideL b t, ∀ o ∈ l.orders,
    0 < o.remainingQty ∧ o.visibleQty = o.remainingQty ∧ o.displayQty = none ∧
      o.side = sideOfTree t
  ids      : ((allBookOrders b).map (·.id)).Nodup
  sorted   : ∀ t, (sideL b t).Pairwise (fun x y => prioB t x.price y.price = true)

-- ============================================================================
-- Book queries
-- ============================================================================

theorem find_isSome_any (l : List Order) (n : Nat) :
    (l.find? (fun o => decide (o.id = n))).isSome = l.any (fun o => o.id == n) := by
  induction l with
  | nil => rfl
  | cons x xs ih => by_cases h : x.id = n <;> simp_all

theorem hashFind_isSome (b : BookState) (n : Nat) :
    (hashFind b n).isSome = idOnBook b n := find_isSome_any _ n

theorem eq_of_nodup_ids : ∀ {l : List Order}, (l.map (·.id)).Nodup →
    ∀ {x y : Order}, x ∈ l → y ∈ l → x.id = y.id → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: as, h, x, y, hx, hy, e => by
    have hna : a.id ∉ as.map (·.id) := (List.nodup_cons.mp h).1
    have ih : ∀ {x y : Order}, x ∈ as → y ∈ as → x.id = y.id → x = y :=
      eq_of_nodup_ids (List.nodup_cons.mp h).2
    rcases List.mem_cons.mp hx with hxa | hx' <;> rcases List.mem_cons.mp hy with hya | hy'
    · rw [hxa, hya]
    · subst hxa; exact absurd (e ▸ List.mem_map_of_mem hy') hna
    · subst hya; exact absurd (e.symm ▸ List.mem_map_of_mem hx') hna
    · exact ih hx' hy' e

theorem count_eq_bookSize {b : BookState} (hs : b.stops = []) : count b = bookSize b := by
  simp [count, bookSize, hs]

theorem allBookOrders_sides (b : BookState) :
    allBookOrders b = (sideL b .bids).flatMap (·.orders) ++ (sideL b .asks).flatMap (·.orders) := rfl

-- ============================================================================
-- Entry checks
-- ============================================================================

/-- `Walk.processOrder` is the request-only checks, then the duplicate and
    capacity checks, then the side. -/
theorem processOrder_eq {cap : Nat} {b : BookState} {r : CRequest} (hcap : cap + 1 < 2 ^ 64) :
    processOrder cap b r =
      match staticCode cap r with
      | some c => reject c b
      | none =>
        if (hashFind b r.id.toNat).isSome then reject .rejectedDuplicate b
        else if (r.orderType = 0 ∨ r.orderType = 3) ∧ cap ≤ count b then
          reject .rejectedCapacity b
        else sideProc { cap := cap, r := r, isBuy := decide (r.side = 0) } b := by
  unfold processOrder staticCode
  by_cases h1 : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3
  · simp only [h1, not_true_eq_false, if_false]
    by_cases h2 : r.side = 0 ∨ r.side = 1
    · simp only [h2, not_true_eq_false, if_false]
      by_cases h3 : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4
      · simp only [h3, not_true_eq_false, if_false]
        by_cases h4 : r.qty = 0
        · simp [h4]
        · simp only [h4, if_false]
          by_cases h5 : r.orderType ≠ 1 ∧ r.price = 0
          · rw [if_pos h5, if_pos h5]
          · simp only [h5, if_false, hcap, not_true_eq_false]
            by_cases h6 : qmax cap < r.qty.toNat
            · simp [h6]
            · simp [h6]
      · simp [h3]
    · simp [h2]
  · simp [h1]

/-- Two results agree: same code, same trades, same book up to the view. -/
def Agree (w p : ResultCode × ProcessResult) : Prop :=
  w.1 = p.1 ∧ w.2.trades = p.2.trades ∧ MatcherRun.nB w.2.book = MatcherRun.nB p.2.book

theorem Agree.refl (x : ResultCode × ProcessResult) : Agree x x := ⟨rfl, rfl, rfl⟩

theorem Agree.obs {w p : ResultCode × ProcessResult} (h : Agree w p) : obsSpec w = obsSpec p := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [obsSpec, h1, h2, (MatcherRun.bookView_iff _ _).mpr h3]

/-- The order-request branch, up to the side: every entry rejection agrees,
    and an order that passes them runs `sideProc` where `processB` runs
    `processWithId`. -/
theorem processOrder_entry {cap : Nat} {b : BookState} {r : CRequest} (hw : WF cap b) :
    (∃ w, processOrder cap b r = some w ∧ w = processB cap b (.order r)) ∨
    (∃ o, r.toSpec = some o ∧ o.id = r.id.toNat ∧ idOnBook b o.id = false ∧
      ¬ (requestMayRest r = true ∧ cap ≤ bookSize b) ∧
      staticCode cap r = none ∧
      processOrder cap b r = sideProc { cap := cap, r := r, isBuy := decide (r.side = 0) } b ∧
      processB cap b (.order r) = (postOnlyCode o b, processWithId b o)) := by
  rw [processOrder_eq hw.cap64]
  cases hs : staticCode cap r with
  | some c => exact Or.inl ⟨_, rfl, (processB_static hs).symm⟩
  | none =>
    obtain ⟨o, hto, hid, hp⟩ := processB_after_static (b := b) hs
    simp only
    have hfind : (hashFind b r.id.toNat).isSome = idOnBook b o.id := by rw [hashFind_isSome, hid]
    rw [hfind]
    by_cases hd : idOnBook b o.id = true
    · rw [if_pos hd]; rw [if_pos hd] at hp
      exact Or.inl ⟨_, rfl, hp.symm⟩
    · rw [if_neg hd]
      rw [if_neg hd] at hp
      have hc : ((r.orderType = 0 ∨ r.orderType = 3) ∧ cap ≤ count b) ↔
          (requestMayRest r && decide (cap ≤ bookSize b)) = true := by
        rw [count_eq_bookSize hw.stops, Bool.and_eq_true, requestMayRest_iff, decide_eq_true_eq]
      by_cases hcp : (r.orderType = 0 ∨ r.orderType = 3) ∧ cap ≤ count b
      · rw [if_pos hcp]; rw [if_pos (hc.mp hcp)] at hp
        exact Or.inl ⟨_, rfl, hp.symm⟩
      · rw [if_neg hcp]
        rw [if_neg (fun h => hcp (hc.mpr h))] at hp
        refine Or.inr ⟨o, hto, hid, by simpa using hd, ?_, by first | trivial | exact hs, rfl, hp⟩
        rw [← requestMayRest_iff, count_eq_bookSize hw.stops] at hcp
        exact hcp

-- ============================================================================
-- Cancel
-- ============================================================================

/-- The levels of one side after `Walk.cancel` removes the order with id `n`
    from level `l` (the first level holding it). -/
def walkRemove (L : List PriceLevel) (p n : Nat) : List PriceLevel :=
  let L1 := modAt p (fun l => { l with orders := l.orders.eraseP (·.id = n) }) L
  if (L1.find? (·.price = p)).map levelCount = some 0 then L1.eraseP (·.price = p) else L1

theorem eraseP_eq_filter {os : List Order} {n : Nat}
    (h : ∀ x ∈ os, ∀ y ∈ os, x.id = n → y.id = n → x = y) (hnd : (os.map (·.id)).Nodup) :
    os.eraseP (fun o => decide (o.id = n)) = os.filter (fun o => o.id != n) := by
  induction os with
  | nil => rfl
  | cons x xs ih =>
    have hnd' : (xs.map (·.id)).Nodup := (List.nodup_cons.mp hnd).2
    have hx : x.id ∉ xs.map (·.id) := (List.nodup_cons.mp hnd).1
    by_cases hxn : x.id = n
    · have hxs : ∀ y ∈ xs, y.id ≠ n := fun y hy e =>
        hx (hxn ▸ e ▸ List.mem_map_of_mem hy)
      simp only [List.eraseP_cons, hxn, decide_true, cond_true, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, if_false]
      exact (List.filter_eq_self.mpr fun y hy => by simpa using hxs y hy).symm
    · simp only [List.eraseP_cons, hxn, decide_false, cond_false, List.filter_cons]
      rw [if_pos (by simpa using hxn),
        ih (fun a ha c hc => h a (List.mem_cons_of_mem _ ha) c (List.mem_cons_of_mem _ hc)) hnd']

theorem removeLevelOrder_keep {A : List PriceLevel} {n : Nat}
    (h : ∀ a ∈ A, a.orders ≠ [] ∧ ∀ o ∈ a.orders, o.id ≠ n) : removeLevelOrder A n = A := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    have hf : a.orders.filter (·.id != n) = a.orders :=
      List.filter_eq_self.mpr fun o ho => by simpa using ha.2 o ho
    have hr := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold removeLevelOrder at hr ⊢
    simp only [List.filterMap_cons, hf]
    rw [hr]
    have : a.orders.isEmpty = false := by simpa using ha.1
    simp [this]

theorem modAt_append_cons {p : Nat} {f : PriceLevel → PriceLevel} {A B : List PriceLevel}
    {l : PriceLevel} (hA : ∀ a ∈ A, a.price ≠ p) (hl : l.price = p) :
    modAt p f (A ++ l :: B) = A ++ f l :: B := by
  induction A with
  | nil => simp [modAt, hl]
  | cons a as ih =>
    have ha := hA a List.mem_cons_self
    simp only [List.cons_append, modAt, ha, if_false]
    rw [ih fun x hx => hA x (List.mem_cons_of_mem _ hx)]

/-- One side of the cancel: `Walk.cancel` and `removeLevelOrder` agree on a
    side with distinct prices, no empty level and unique ids. -/
theorem walkRemove_eq {L : List PriceLevel} {n : Nat} {l : PriceLevel} (t : Tree)
    (hs : L.Pairwise (fun x y => prioB t x.price y.price = true))
    (hne : ∀ x ∈ L, x.orders ≠ [])
    (hnd : ((L.flatMap (·.orders)).map (·.id)).Nodup)
    (hf : L.find? (fun l => l.orders.any (·.id = n)) = some l) :
    walkRemove L l.price n = removeLevelOrder L n := by
  obtain ⟨hl, A, B, rfl, hA⟩ := List.find?_eq_some_iff_append.mp hf
  simp only [List.any_eq_true, decide_eq_true_eq] at hl
  obtain ⟨o, ho, hon⟩ := hl
  have hA' : ∀ a ∈ A, ∀ x ∈ a.orders, x.id ≠ n := by
    intro a ha x hx e
    have h1 := hA a ha
    simp at h1
    exact h1 x hx e
  -- prices in A differ from l's
  have hpair := List.pairwise_append.mp hs
  have hApr : ∀ a ∈ A, a.price ≠ l.price := by
    intro a ha e
    have := hpair.2.2 a ha l List.mem_cons_self
    rw [e] at this; cases t <;> simp [prioB] at this
  -- ids: the order with id n in l is the only one in the side
  have hflat : ((A ++ l :: B).flatMap (·.orders)).map (·.id) =
      (A.flatMap (·.orders)).map (·.id) ++ (l.orders.map (·.id) ++ (B.flatMap (·.orders)).map (·.id)) := by
    simp
  rw [hflat] at hnd
  have hnd2 := (List.nodup_append.mp hnd).2.1
  have hlnd : (l.orders.map (·.id)).Nodup := (List.nodup_append.mp hnd2).1
  have hB : ∀ a ∈ B, ∀ x ∈ a.orders, x.id ≠ n := by
    intro a ha x hx e
    have h1 : n ∈ l.orders.map (·.id) := hon ▸ List.mem_map_of_mem ho
    have h2 : n ∈ (B.flatMap (·.orders)).map (·.id) :=
      e ▸ List.mem_map_of_mem (List.mem_flatMap.mpr ⟨a, ha, hx⟩)
    exact (List.nodup_append.mp hnd2).2.2 n h1 n h2 rfl
  have hl1 : ∀ x ∈ l.orders, ∀ y ∈ l.orders, x.id = n → y.id = n → x = y := by
    intro x hx y hy ex ey
    exact eq_of_nodup_ids hlnd hx hy (ex.trans ey.symm)
  have hera := eraseP_eq_filter hl1 hlnd
  have hne' : ∀ x ∈ A ++ l :: B, x.orders ≠ [] := hne
  have hrA := removeLevelOrder_keep (A := A) (n := n) fun a ha =>
    ⟨hne' a (List.mem_append_left _ ha), hA' a ha⟩
  have hrB := removeLevelOrder_keep (A := B) (n := n) fun a ha =>
    ⟨hne' a (List.mem_append_right _ (List.mem_cons_of_mem _ ha)), hB a ha⟩
  unfold walkRemove
  simp only
  rw [modAt_append_cons hApr rfl]
  have hfind : (A ++ { l with orders := l.orders.eraseP (fun o => decide (o.id = n)) } :: B).find?
      (fun x => decide (x.price = l.price)) =
      some { l with orders := l.orders.eraseP (fun o => decide (o.id = n)) } := by
    rw [List.find?_append, List.find?_eq_none.mpr (fun a ha => by simpa using hApr a ha)]
    simp
  rw [hfind]
  have hrm : removeLevelOrder (A ++ l :: B) n =
      A ++ (if (l.orders.filter (·.id != n)).isEmpty then []
            else [{ l with orders := l.orders.filter (·.id != n) }]) ++ B := by
    rw [MatcherCancel.removeLevelOrder_eq] at hrA hrB ⊢
    rw [List.filterMap_append, List.filterMap_cons, hrA, hrB]
    unfold MatcherCancel.dropStep
    by_cases hc : (l.orders.filter (·.id != n)).isEmpty = true <;> simp [hc]
  rw [hrm, hera]
  by_cases he : (l.orders.filter (·.id != n)).isEmpty = true
  · have he' : l.orders.filter (·.id != n) = [] := List.isEmpty_iff.mp he
    rw [if_pos he, if_pos (by simp [levelCount, he'])]
    rw [List.eraseP_append_right _ (fun a ha => by simpa using hApr a ha)]
    simp
  · have he' : l.orders.filter (·.id != n) ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
    rw [if_neg he, if_neg (by simpa [levelCount] using he')]
    simp

theorem none_of_isSome_false {α : Type} {o : Option α} (h : o.isSome = false) : o = none := by
  cases o <;> simp_all

/-- An order with id `n` sits on one of these levels. -/
def hasId (L : List PriceLevel) (n : Nat) : Bool := L.any fun l => l.orders.any (·.id = n)

theorem srch_fst (sd : Side) (n : Nat) : ∀ (L : List PriceLevel),
    (L.findSome? (fun level => level.orders.findSome? fun order =>
        if order.id == n then some (sd, order) else none)).map Prod.fst =
      if hasId L n then some sd else none := by
  have inner : ∀ (os : List Order), (os.findSome? fun order =>
      if order.id == n then some (sd, order) else none).map Prod.fst =
        if os.any (·.id = n) then some sd else none := by
    intro os; induction os with
    | nil => rfl
    | cons o os ih =>
      by_cases h : o.id = n
      · simp [h]
      · have hb : (o.id == n) = false := by simp [h]
        simp only [List.findSome?_cons, hb, Bool.false_eq_true, if_false, List.any_cons, h,
          decide_false, Bool.false_or]
        exact ih
  intro L; induction L with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.findSome?_cons, hasId, List.any_cons]
    have hl := inner l.orders
    cases hf : l.orders.findSome? (fun order => if order.id == n then some (sd, order) else none) with
    | some y =>
      rw [hf] at hl
      by_cases ha : l.orders.any (·.id = n) = true
      · simp [ha] at hl ⊢; exact hl
      · simp [ha] at hl
    | none =>
      rw [hf] at hl
      by_cases ha : l.orders.any (·.id = n) = true
      · simp [ha] at hl
      · simp only [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_or]
        exact ih

theorem find_some_of_hasId {L : List PriceLevel} {n : Nat} (h : hasId L n = true) :
    ∃ l, L.find? (fun l => l.orders.any (·.id = n)) = some l := by
  cases hf : L.find? (fun l => l.orders.any (·.id = n)) with
  | some l => exact ⟨l, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    simp only [hasId] at h
    rw [List.any_eq_true] at h
    obtain ⟨l, hl, hl2⟩ := h
    exact absurd hl2 (hf l hl)

theorem find_none_of_hasId {L : List PriceLevel} {n : Nat} (h : hasId L n = false) :
    L.find? (fun l => l.orders.any (·.id = n)) = none := by
  rw [List.find?_eq_none]
  intro l hl h2
  simp only [hasId, List.any_eq_false] at h
  exact h l hl h2

theorem flat_find {L : List PriceLevel} {n : Nat} :
    ((L.flatMap (·.orders)).find? fun o => decide (o.id = n)).isSome = hasId L n := by
  rw [find_isSome_any]
  have e : ∀ a b : Nat, (a == b) = decide (a = b) := fun a b => by by_cases h : a = b <;> simp [h]
  simp [hasId, List.any_flatMap, e]

theorem sideL_setSideL_twice (b : BookState) (t : Tree) (L1 L2 : List PriceLevel) :
    setSideL (setSideL b t L1) t L2 = setSideL b t L2 := by cases t <;> rfl

/-- The walk's cancel on one tree is `walkRemove`. -/
theorem cancel_side {b : BookState} {t : Tree} {o : Order} {l : PriceLevel} {n : Nat}
    (ho : o.id = n) (hside : (if o.side = .buy then Tree.bids else .asks) = t) :
    (let b1 := qRemove b t l.price o
     if (tFind b1 t l.price).map levelCount = some 0 then
       tRemove b1 (if o.side = .buy then .bids else .asks) l.price else b1) =
      setSideL b t (walkRemove (sideL b t) l.price n) := by
  simp only [hside, qRemove, tFind, tRemove, walkRemove, sideL_setSideL, ho]
  split <;> simp [sideL_setSideL_twice]

theorem nodup_side {b : BookState} (h : ((allBookOrders b).map (·.id)).Nodup) (t : Tree) :
    (((sideL b t).flatMap (·.orders)).map (·.id)).Nodup := by
  rw [allBookOrders_sides, List.map_append] at h
  cases t
  · exact (List.nodup_append.mp h).1
  · exact (List.nodup_append.mp h).2.1

theorem mem_side_of_find {L : List PriceLevel} {n : Nat} {o : Order}
    (h : (L.flatMap (·.orders)).find? (fun o => decide (o.id = n)) = some o) :
    o.id = n ∧ ∃ l ∈ L, o ∈ l.orders := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hp, List.mem_flatMap.mp hm⟩

/-- **Cancel.** On a `WF` book the walk's cancel is `processB`'s, exactly. -/
theorem cancel_eq {cap : Nat} {b : BookState} (hw : WF cap b) (id : UInt64) :
    cancel b id = processB cap b (.cancel id) := by
  unfold cancel processB cancelOrder findOrderOnBook
  simp only
  have hb := srch_fst .buy id.toNat b.bids
  have ha := srch_fst .sell id.toNat b.asks
  have hf : hashFind b id.toNat = ((b.bids.flatMap (·.orders)).find? fun o => decide (o.id = id.toNat)).or
      ((b.asks.flatMap (·.orders)).find? fun o => decide (o.id = id.toNat)) := by
    simp [hashFind, allBookOrders, List.find?_append]
  cases hB : hasId b.bids id.toNat
  · -- not on the bids
    have hfb : ((b.bids.flatMap (·.orders)).find? fun o => decide (o.id = id.toNat)) = none := by
      have := (flat_find (L := b.bids) (n := id.toNat)); rw [hB] at this
      exact none_of_isSome_false this
    rw [hB, if_neg (by simp)] at hb
    cases hsb : (b.bids.findSome? fun level => level.orders.findSome? fun order =>
        if order.id == id.toNat then some (Side.buy, order) else none) with
    | some x => rw [hsb] at hb; cases hb
    | none =>
      simp only
      cases hA : hasId b.asks id.toNat
      · have hfa : ((b.asks.flatMap (·.orders)).find? fun o => decide (o.id = id.toNat)) = none := by
          have := (flat_find (L := b.asks) (n := id.toNat)); rw [hA] at this
          exact none_of_isSome_false this
        rw [hA, if_neg (by simp)] at ha
        cases hsa : (b.asks.findSome? fun level => level.orders.findSome? fun order =>
            if order.id == id.toNat then some (Side.sell, order) else none) with
        | some x => rw [hsa] at ha; cases ha
        | none => rw [hf, hfb, hfa]; rfl
      · rw [hA, if_pos rfl] at ha
        cases hsa : (b.asks.findSome? fun level => level.orders.findSome? fun order =>
            if order.id == id.toNat then some (Side.sell, order) else none) with
        | none => rw [hsa] at ha; cases ha
        | some x =>
          obtain ⟨sd, o'⟩ := x
          rw [hsa] at ha
          simp only [Option.map_some, Option.some.injEq] at ha
          subst ha
          have hfa : ((b.asks.flatMap (·.orders)).find? fun o => decide (o.id = id.toNat)).isSome := by
            rw [flat_find, hA]
          obtain ⟨o, hfo⟩ := Option.isSome_iff_exists.mp hfa
          obtain ⟨hoid, l0, hl0, hol0⟩ := mem_side_of_find hfo
          have hos : o.side = .sell := (hw.resting .asks l0 hl0 o hol0).2.2.2
          rw [hf, hfb, hfo]
          simp only [Option.none_or]
          have hown : owner b o = some (.asks, (b.asks.find? fun l => l.orders.any (·.id = id.toNat)).get
              (by obtain ⟨l, hl⟩ := find_some_of_hasId hA; rw [hl]; rfl)) := by
            unfold owner
            rw [hoid, find_none_of_hasId hB]
            obtain ⟨l, hl⟩ := find_some_of_hasId hA
            simp [hl]
          obtain ⟨l, hl⟩ := find_some_of_hasId hA
          have hown' : owner b o = some (.asks, l) := by rw [hown]; simp [hl]
          rw [hown']
          simp only
          rw [cancel_side hoid (by simp [hos])]
          rw [walkRemove_eq .asks (hw.sorted .asks) (hw.nonempty .asks) (nodup_side hw.ids .asks) hl]
          rfl
  · -- on the bids
    rw [hB, if_pos rfl] at hb
    cases hsb : (b.bids.findSome? fun level => level.orders.findSome? fun order =>
        if order.id == id.toNat then some (Side.buy, order) else none) with
    | none => rw [hsb] at hb; cases hb
    | some x =>
      obtain ⟨sd, o'⟩ := x
      rw [hsb] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      have hfb : ((b.bids.flatMap (·.orders)).find? fun o => decide (o.id = id.toNat)).isSome := by
        rw [flat_find, hB]
      obtain ⟨o, hfo⟩ := Option.isSome_iff_exists.mp hfb
      obtain ⟨hoid, l0, hl0, hol0⟩ := mem_side_of_find hfo
      have hos : o.side = .buy := (hw.resting .bids l0 hl0 o hol0).2.2.2
      rw [hf, hfo]
      simp only [Option.some_or]
      obtain ⟨l, hl⟩ := find_some_of_hasId hB
      have hown' : owner b o = some (.bids, l) := by
        unfold owner; rw [hoid, hl]
      rw [hown']
      simp only
      rw [cancel_side hoid (by simp [hos])]
      rw [walkRemove_eq .bids (hw.sorted .bids) (hw.nonempty .bids) (nodup_side hw.ids .bids) hl]
      rfl

end Walk

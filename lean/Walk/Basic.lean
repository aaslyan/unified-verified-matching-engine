import Walk.Spec

/-!
# Sanity lemmas for the walking spec (A1)

* `innerStep_progress`: an inner iteration either pops the head order of
  the best contra level or ends the match (`rem = 0`).
* `innerRun_stable`, `outerRun_stable`: a loop whose test is false returns
  its state; more fuel than a run used gives the same result.
* `innerRun_ok`, `outerRun_ok`: with the bound `cap + 1` neither loop
  exhausts its bound, and the trade buffer never fills.
* `run_fuel_sufficient`: on a book with at most `cap` orders and no empty
  level, `Walk.process` never traps.
-/

namespace Walk

open EngineDbApi EngineDbAbs ProcessB

-- ============================================================================
-- Primitives
-- ============================================================================

@[simp] theorem sideL_setSideL (b : BookState) (t : Tree) (ls : List PriceLevel) :
    sideL (setSideL b t ls) t = ls := by cases t <;> rfl

@[simp] theorem modHead_cons (f : PriceLevel → PriceLevel) (l : PriceLevel) (ls : List PriceLevel) :
    modHead f (l :: ls) = f l :: ls := rfl

@[simp] theorem sideL_popHead (b : BookState) (t : Tree) :
    sideL (popHead b t) t = modHead (fun l => { l with orders := l.orders.tail }) (sideL b t) := by
  cases t <;> rfl

@[simp] theorem sideL_setHeadRem (b : BookState) (t : Tree) (q : Nat) :
    sideL (setHeadRem b t q) t = modHead (fun l =>
      { l with orders := match l.orders with
        | [] => []
        | o :: os => { o with remainingQty := q, visibleQty := q } :: os }) (sideL b t) := by
  cases t <;> rfl

@[simp] theorem sideL_dropBest (b : BookState) (t : Tree) :
    sideL (dropBest b t) t = (sideL b t).tail := by
  cases t <;> rfl

theorem tBest_eq (b : BookState) (t : Tree) : tBest b t = (sideL b t).head? := rfl

/-- Orders on one tree. -/
def sideCount (ls : List PriceLevel) : Nat := (ls.map levelCount).sum

/-- Orders on the contra side of a state's book. -/
def contraCount (c : Ctx) (st : State) : Nat := sideCount (sideL st.book c.contra)

/-- The potential that bounds emitted trades: trades so far plus contra orders. -/
def pot (c : Ctx) (st : State) : Nat := st.trades.length + contraCount c st

@[simp] theorem sideCount_cons (l : PriceLevel) (ls : List PriceLevel) :
    sideCount (l :: ls) = l.orders.length + sideCount ls := by
  simp [sideCount, levelCount]

-- ============================================================================
-- One inner iteration
-- ============================================================================

/-- A fill that leaves the maker with quantity ends the match. -/
theorem rem_zero_of_prem_pos {r q : Nat} (h : ¬ q - min r q = 0) : r - min r q = 0 := by omega

/-- The shape of one inner iteration at head level `best :: rest`, head order
    `p :: os`: only the head level changes, and either the match ends or the
    head order is gone with at most one trade emitted. -/
theorem innerStep_shape {c : Ctx} {st st' : State} {best : PriceLevel} {rest : List PriceLevel}
    {p : Order} {os : List Order}
    (h : sideL st.book c.contra = best :: rest) (hp : best.orders = p :: os)
    (hs : innerStep c st = some st') :
    st'.stop = st.stop ∧ ∃ l', sideL st'.book c.contra = l' :: rest ∧ l'.price = best.price ∧
      (st'.rem = 0 ∨ (l'.orders = os ∧ st'.trades.length ≤ st.trades.length + 1)) := by
  unfold innerStep at hs
  rw [tBest_eq, h] at hs
  simp only [List.head?_cons, qFirst, hp] at hs
  refine ⟨?_, ?_⟩
  · repeat' (first | (simp only [Option.some.injEq] at hs; subst hs; rfl) | split at hs | split)
    all_goals first | cases hs | (simp only [Option.some.injEq] at hs; subst hs; rfl)
  · split at hs
    · -- self-trade prevention
      split at hs
      · simp only [Option.some.injEq] at hs; subst hs
        exact ⟨best, h, rfl, Or.inl rfl⟩
      · split at hs
        · split at hs <;> (simp only [Option.some.injEq] at hs; subst hs) <;>
          · simp only [sideL_popHead, h, modHead_cons]
            refine ⟨_, rfl, rfl, Or.inr ⟨by simp [hp], by first | exact Nat.le_succ _ | simp⟩⟩
        · simp only [Option.some.injEq] at hs; subst hs
          split
          · simp only [sideL_popHead, sideL_setHeadRem, h, modHead_cons]
            refine ⟨_, rfl, rfl, Or.inr ⟨by simp [hp], by first | exact Nat.le_succ _ | simp⟩⟩
          · simp only [sideL_setHeadRem, h, modHead_cons]
            refine ⟨_, rfl, rfl, Or.inl (rem_zero_of_prem_pos ‹_›)⟩
    · -- a fill
      split at hs
      · simp only [Option.some.injEq] at hs; subst hs
        split
        · simp only [sideL_popHead, sideL_setHeadRem, h, modHead_cons]
          refine ⟨_, rfl, rfl, Or.inr ⟨by simp [hp], by first | exact Nat.le_succ _ | simp⟩⟩
        · simp only [sideL_setHeadRem, h, modHead_cons]
          refine ⟨_, rfl, rfl, Or.inl (rem_zero_of_prem_pos ‹_›)⟩
      · cases hs

/-- An inner iteration traps only on a full trade buffer. -/
theorem innerStep_isSome {c : Ctx} {st : State} (htr : st.trades.length ≤ c.cap) :
    (innerStep c st).isSome := by
  unfold innerStep
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · rfl
        · split
          · split <;> rfl
          · rfl
      · rw [if_pos (by omega)]; rfl

/-- **Progress.** An inner iteration whose test holds either ends the match or
    removes one order from the contra side. -/
theorem innerStep_progress {c : Ctx} {st st' : State} (ht : innerTest c st = true)
    (hs : innerStep c st = some st') :
    st'.rem = 0 ∨ contraCount c st' + 1 = contraCount c st := by
  unfold innerTest at ht
  rw [tBest_eq] at ht
  cases h : sideL st.book c.contra with
  | nil => simp [h] at ht
  | cons best rest =>
    cases hp : best.orders with
    | nil => simp [h, qFirst, hp] at ht
    | cons p os =>
      obtain ⟨-, l', h', -, hr⟩ := innerStep_shape h hp hs
      rcases hr with hr | ⟨ho, -⟩
      · exact Or.inl hr
      · right; simp [contraCount, h, h', ho, hp]; omega

-- ============================================================================
-- Stability
-- ============================================================================

theorem innerRun_exit {c : Ctx} {st : State} (ht : innerTest c st = false) (n : Nat) :
    innerRun c n st = some st := by
  cases n <;> simp [innerRun, ht]

theorem outerRun_exit {c : Ctx} {st : State} (ht : outerTest st = false) (n : Nat) :
    outerRun c n st = some st := by
  cases n <;> simp [outerRun, ht]

/-- More fuel than a finished inner run used changes nothing. -/
theorem innerRun_stable {c : Ctx} : ∀ {n : Nat} {st st' : State},
    innerRun c n st = some st' → innerRun c (n + 1) st = some st'
  | 0, st, st', h => by
    unfold innerRun at h
    split at h
    · cases h
    · rename_i ht; simp only [Bool.not_eq_true] at ht
      rw [innerRun_exit ht]; exact h
  | n + 1, st, st', h => by
    unfold innerRun at h ⊢
    split at h
    · rw [if_pos ‹_›]
      cases hs : innerStep c st with
      | none => rw [hs] at h; cases h
      | some s1 => rw [hs] at h; exact innerRun_stable h
    · rw [if_neg ‹_›]; exact h

/-- More fuel than a finished outer run used changes nothing. -/
theorem outerRun_stable {c : Ctx} : ∀ {n : Nat} {st st' : State},
    outerRun c n st = some st' → outerRun c (n + 1) st = some st'
  | 0, st, st', h => by
    unfold outerRun at h
    split at h
    · cases h
    · rename_i ht; simp only [Bool.not_eq_true] at ht
      rw [outerRun_exit ht]; exact h
  | n + 1, st, st', h => by
    unfold outerRun at h ⊢
    split at h
    · rw [if_pos ‹_›]
      cases hs : outerStep c st with
      | none => rw [hs] at h; cases h
      | some s1 => rw [hs] at h; exact outerRun_stable h
    · rw [if_neg ‹_›]; exact h

-- ============================================================================
-- Fuel sufficiency
-- ============================================================================

/-- The inner loop at head level `best :: rest` with at least as many
    iterations as `best` has orders, and room in the trade buffer for every
    order of the contra side, does not trap. It leaves `rest` alone, and if
    the match is not over the head level is empty and the potential has not
    grown. -/
theorem innerRun_ok {c : Ctx} {rest : List PriceLevel} : ∀ (n : Nat) (st : State) (best : PriceLevel),
    sideL st.book c.contra = best :: rest → best.orders.length ≤ n →
    (0 < st.rem → pot c st ≤ c.cap) →
    ∃ st', innerRun c n st = some st' ∧ st'.stop = st.stop ∧
      ∃ l', sideL st'.book c.contra = l' :: rest ∧
        (0 < st'.rem → l'.orders = [] ∧ pot c st' ≤ pot c st)
  | n, st, best, h, hn, hpot => by
    by_cases ht : innerTest c st = true
    · have hrem : 0 < st.rem := by
        unfold innerTest at ht; simp at ht; exact ht.2
      have htest := ht
      unfold innerTest at htest
      rw [tBest_eq, h] at htest
      cases hp : best.orders with
      | nil => simp [qFirst, hp] at htest
      | cons p os =>
        rw [hp] at hn
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
        have hP := hpot hrem
        have htr : st.trades.length ≤ c.cap := by
          unfold pot at hP; omega
        obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (innerStep_isSome (c := c) htr)
        obtain ⟨hstop, l1, h1, -, hr⟩ := innerStep_shape h hp hs1
        have hrun : innerRun c (k + 1) st = innerRun c k s1 := by
          simp [innerRun, ht, hs1]
        rw [hrun]
        rcases hr with hr | ⟨ho, htr1⟩
        · have ht1 : innerTest c s1 = false := by simp [innerTest, hr]
          exact ⟨s1, innerRun_exit ht1 k, hstop, l1, h1, fun h0 => by omega⟩
        · have hpot1 : pot c s1 ≤ pot c st := by
            simp [pot, contraCount, h, h1, ho, hp]; omega
          obtain ⟨s2, hs2, hstop2, l2, h2, hr2⟩ := innerRun_ok k s1 l1 h1
            (by rw [ho]; simp at hn; omega) (fun _ => Nat.le_trans hpot1 hP)
          exact ⟨s2, hs2, hstop2.trans hstop, l2, h2, fun h0 =>
            ⟨(hr2 h0).1, Nat.le_trans (hr2 h0).2 hpot1⟩⟩
    · simp only [Bool.not_eq_true] at ht
      refine ⟨st, innerRun_exit ht n, rfl, best, h, fun h0 => ⟨?_, Nat.le_refl _⟩⟩
      unfold innerTest at ht
      rw [tBest_eq, h] at ht
      cases hp : best.orders with
      | nil => rfl
      | cons p os => simp [qFirst, hp, h0] at ht

theorem length_le_sideCount : ∀ {ls : List PriceLevel}, (∀ l ∈ ls, l.orders ≠ []) →
    ls.length ≤ sideCount ls
  | [], _ => Nat.le_refl _
  | l :: ls, h => by
    have := length_le_sideCount (ls := ls) (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hl := h l List.mem_cons_self
    have : 0 < l.orders.length := List.length_pos_iff.mpr hl
    simp; omega

/-- The outer loop with more iterations than contra levels, and room in the
    trade buffer for every contra order, does not trap. -/
theorem outerRun_ok {c : Ctx} (hb : c.bound = some (c.cap + 1)) : ∀ (n : Nat) (st : State),
    (sideL st.book c.contra).length < n → (0 < st.rem → pot c st ≤ c.cap) →
    (outerRun c n st).isSome
  | 0, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, st, hn, hpot => by
    unfold outerRun
    by_cases ht : outerTest st = true
    · rw [if_pos ht]
      have hrem : 0 < st.rem := by simp [outerTest] at ht; exact ht.1
      unfold outerStep
      rw [tBest_eq]
      cases h : sideL st.book c.contra with
      | nil =>
        simp only [List.head?_nil, Option.bind_some]
        rw [outerRun_exit (by simp [outerTest])]; rfl
      | cons best rest =>
        simp only [List.head?_cons]
        by_cases hpc : c.r.orderType ≠ 1 ∧ ¬c.crosses best.price = true
        · rw [if_pos hpc, Option.bind_some, outerRun_exit (by simp [outerTest])]; rfl
        · have hP := hpot hrem
          have hlen : best.orders.length ≤ c.cap + 1 := by
            simp [pot, contraCount, h] at hP; omega
          obtain ⟨s1, hs1, -, l1, h1, hr1⟩ := innerRun_ok (c.cap + 1) st best h hlen (fun _ => hP)
          simp only [if_neg hpc, hb, hs1, Option.bind_eq_bind, Option.bind_some]
          rw [tBest_eq, h1, List.head?_cons]
          simp only
          by_cases hz : levelCount l1 = 0
          · rw [if_pos hz, Option.bind_some]
            apply outerRun_ok hb n
            · simp only [sideL_dropBest, h1, List.tail_cons]
              simp [h] at hn; omega
            · intro h0
              have ⟨he, hp1⟩ := hr1 h0
              refine Nat.le_trans ?_ (Nat.le_trans hp1 hP)
              simp [pot, contraCount, h1, he]
          · rw [if_neg hz, Option.bind_some]
            have hr0 : s1.rem = 0 := by
              cases Nat.eq_zero_or_pos s1.rem with
              | inl h0 => exact h0
              | inr h0 => exact absurd (by simp [levelCount, (hr1 h0).1]) hz
            rw [outerRun_exit (by simp [outerTest, hr0])]; rfl
    · rw [if_neg ht]; rfl

/-- The contra side's orders are among the book's. -/
theorem sideCount_le_count (b : BookState) (t : Tree) : sideCount (sideL b t) ≤ count b := by
  have e : ∀ ls : List PriceLevel, sideCount ls = (ls.flatMap (·.orders)).length := by
    intro ls; induction ls with
    | nil => rfl
    | cons l ls ih => simp [ih]
  cases t <;> simp [sideL, count, allBookOrders, e]

/-- A matching phase whose outer loop does not trap does not trap. -/
theorem sideProc_isSome {c : Ctx} {b : BookState} {st : State} (hb : c.bound = some (c.cap + 1))
    (hst : outerRun c (c.cap + 1) { book := b, rem := c.r.qty.toNat, stop := false, trades := [] }
      = some st) :
    (sideProc c b).isSome := by
  unfold sideProc
  dsimp only
  repeat' split
  all_goals simp [hb, hst]

/-- **Fuel sufficiency.** On a book with at most `cap` orders and no empty
    level, and a capacity whose `cap + 1` fits `uint64_t`, the walking spec
    never traps: neither loop exhausts its bound `cap + 1` and the trade
    buffer never fills. -/
theorem run_fuel_sufficient {cap : Nat} {b : BookState} (req : Req)
    (hcap : cap + 1 < 2 ^ 64) (hcount : count b ≤ cap)
    (hne : ∀ t, ∀ l ∈ sideL b t, l.orders ≠ []) :
    (process cap b req).isSome := by
  cases req with
  | cancel id => rfl
  | order r =>
    let c : Ctx := { cap := cap, r := r, isBuy := decide (r.side = 0) }
    have hb : c.bound = some (c.cap + 1) := by simp [c, Ctx.bound, hcap]
    have hsc := sideCount_le_count b c.contra
    obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp
      (outerRun_ok hb (c.cap + 1) { book := b, rem := r.qty.toNat, stop := false, trades := [] }
        (Nat.lt_succ_of_le (Nat.le_trans (length_le_sideCount (hne c.contra))
          (Nat.le_trans hsc hcount)))
        (fun _ => by simpa [pot, contraCount] using Nat.le_trans hsc hcount))
    have hs := sideProc_isSome hb hst
    simp only [process, processOrder, reject]
    repeat' split
    all_goals first | rfl | exact absurd hcap ‹_› | exact hs

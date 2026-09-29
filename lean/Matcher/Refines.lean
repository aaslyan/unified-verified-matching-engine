import Matcher.Program
import Matcher.Logic
import Bridge.EngineDbFrame
import Bridge.ProcessB

/-!
# Phase 4: the generated matcher refines `processB`

Target (plan v2 §2): for a store `s` with `Inv s` and any request, running the
matcher program ends without error, reports the same result code and trades
as `processB (capacity) (absBook (view s)) req`, leaves a store whose decoded
book has the same `bookView`, and re-establishes `Inv`.

This file, so far: the coupling invariant `Inv`, the refinement statement
`Refines`, and the branches that do not reach the matching loop — the four
entry rejections and cancel. The matching loop follows the loop-invariant
review (STATUS-v2, Phase 4 checkpoint).

Standing hypothesis: `capacity + 1 < 2^64`, as an explicit theorem hypothesis
(`CapOk`), not an `Inv` clause.
-/

namespace MatcherRefines

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB EngineDb

variable {S : Type} [EngineDb S]

-- ============================================================================
-- Requests as matcher calls
-- ============================================================================

def entryOf : Req → Ident
  | .order _ => "gen_process_order"
  | .cancel _ => "gen_cancel_order"

def argsOf : Req → List Val
  | .order r => [.u64 r.id, .u64 r.account, .code r.side, .code r.orderType, .code r.stpMode,
                 .u64 r.price, .u64 r.qty]
  | .cancel id => [.u64 id]

/-- If `runEntry` completes successfully at some fuel, it has the same result
    at every larger fuel.  The fuel bounds recursive interpreter evaluation:
    statement sequencing, branches, function calls, and loop iterations.  It
    is not a matcher capacity or a C run-time limit. -/
theorem runEntry_fuel_stable {P : Program} {f f' : Nat} {fname : Ident}
    {args : List Val} {s : S} {r}
    (h : runEntry P f fname args s = .ok r) (hle : f ≤ f') :
    runEntry P f' fname args s = .ok r := by
  unfold runEntry at h ⊢
  cases hf : lookupFun P fname with
  | error e => rw [hf] at h; cases h
  | ok fd =>
    rw [hf] at h
    simp only [bind, Except.bind] at h ⊢
    cases hp : bindParams fd.params args with
    | error e => rw [hp] at h; cases h
    | ok penv =>
      rw [hp] at h
      simp only at h ⊢
      cases he : execStmt P f fd.body
          { store := s,
            env := penv ++ fd.locals.map fun (x, t) => (x, t.default),
            trades := [] } with
      | error e => rw [he] at h; cases h
      | ok x =>
        rw [he] at h
        rw [execStmt_mono P he hle]
        exact h

/-- The entry environment of `gen_process_order`. -/
def orderEnv (r : CRequest) : List (Ident × Val) :=
  [("id", .u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
   ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price),
   ("qty", .u64 r.qty), ("dup", .order none), ("r", .code 0)]

def orderSt (s : S) (r : CRequest) : St S := { store := s, env := orderEnv r, trades := [] }

-- ============================================================================
-- The coupling invariant
-- ============================================================================

/-- `capacity + 1` fits `uint64_t`: the standing hypothesis. -/
def CapOk (S : Type) [EngineDb S] : Prop := capacity (S := S) + 1 < 2 ^ 64

/-- **The coupling invariant.** The store's view is well formed and satisfies
    the client invariant (so its decoded book satisfies every §13
    invariant); every live row is in the book (no leaked or dangling rows);
    the pool counts are the book's sizes; the book fits the capacity. -/
structure Inv (s : S) : Prop where
  wf : (view s).WF
  client : ClientInv (view s)
  orders_resting : ∀ h, (view s).orderLive h ↔ (view s).queued h
  levels_resting : ∀ l, (view s).levelLive l ↔ (l ∈ (view s).tree .bids ∨ l ∈ (view s).tree .asks)
  count_eq : count s = restingCount (view s)
  levels_eq : levelsUsed s = ((view s).tree .bids ++ (view s).tree .asks).length
  count_le : count s ≤ capacity (S := S)

/-- The spec side of one step, from a store. -/
def specStep (s : S) (req : Req) : ResultCode × ProcessResult :=
  processB (capacity (S := S)) (absBook (view s)) req

/-- **One step refines `processB`.** Some fuel runs the matcher to a result
    code, trades and store that `processB` agrees with on `Obs`, and `Inv`
    holds again.  The fuel is existential because the theorem establishes that
    the interpreter terminates without exposing a fixed evaluation budget as
    part of the matcher interface; `runEntry_fuel_stable` shows that any larger
    budget produces the same successful result. -/
def Refines (s : S) (req : Req) : Prop :=
  ∃ f s' ts, runEntry program f (entryOf req) (argsOf req) s =
      .ok (.code (codeOf (specStep s req).1), s', ts) ∧
    ts = (specStep s req).2.trades.map tradeObs ∧
    bookView (absBook (view s')) = bookView (specStep s req).2.book ∧
    Inv s'

-- ============================================================================
-- Evaluation tactic
-- ============================================================================

/-- Evaluate a matcher expression in a concrete environment. -/
macro "meval" : tactic => `(tactic|
  simp (config := {decide := true}) [List.lookup, evalExpr, lookupVar, evalBin, asBool, asU64,
    not', and', or', eqc, nec, b2, v, c, u, orderSt, orderEnv, Except.bind, bind, Functor.map,
    Except.map, beq_eq_false_iff_ne, OT_LIMIT, OT_MARKET, OT_IOC, OT_POST_ONLY, SIDE_BUY,
    SIDE_SELL, STP_NONE, STP_CANCEL_NEW, STP_CANCEL_OLD, STP_CANCEL_BOTH, STP_DECREMENT])

-- ============================================================================
-- The entry function
-- ============================================================================

theorem lookup_process_order :
    lookupFun program "gen_process_order" = .ok processOrderFun := by
  simp (config := {decide := true}) [lookupFun, program, List.find?, minFun, sideFun,
    processOrderFun, cancelOrderFun]

theorem lookup_cancel_order :
    lookupFun program "gen_cancel_order" = .ok cancelOrderFun := by
  simp (config := {decide := true}) [lookupFun, program, List.find?, minFun, sideFun,
    processOrderFun, cancelOrderFun]

theorem bind_order_params (r : CRequest) :
    bindParams processOrderFun.params (argsOf (.order r)) =
      .ok [("id", .u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
           ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price),
           ("qty", .u64 r.qty)] := by
  simp [bindParams, processOrderFun, argsOf, Val.ty, Functor.map, Except.map]

theorem order_entry_env (r : CRequest) :
    [("id", Val.u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
     ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price),
     ("qty", .u64 r.qty)] ++ processOrderFun.locals.map (fun (x, t) => (x, t.default)) =
      orderEnv r := by
  simp [processOrderFun, orderEnv, Ty.default]

/-- From a run of the entry body to a `runEntry` result. -/
theorem order_run {s : S} {r : CRequest} {st₁ : St S} {k : UInt8}
    (h : Eval program processOrderFun.body (orderSt s r) (st₁, .ret (.code k))) :
    ∃ f, runEntry program f "gen_process_order" (argsOf (.order r)) s =
      .ok (.code k, st₁.store, st₁.trades) := by
  refine runEntry_of_eval lookup_process_order (bind_order_params r) ?_ rfl
  rw [order_entry_env]; exact h

-- ============================================================================
-- The request-only checks
-- ============================================================================

/-- The checks `gen_process_order` makes before touching the store, in its
    order. -/
def staticCode (cap : Nat) (r : CRequest) : Option ResultCode :=
  if ¬(r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3) then
    some .rejectedUnsupported
  else if ¬(r.side = 0 ∨ r.side = 1) then some .rejectedInvalid
  else if ¬(r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4) then
    some .rejectedInvalid
  else if r.qty = 0 then some .rejectedInvalid
  else if r.orderType ≠ 1 ∧ r.price = 0 then some .rejectedInvalid
  else if qmax cap < r.qty.toNat then some .rejectedInvalid
  else none

private theorem u8_lit (t : UInt8) (k : UInt8) : t = k ↔ t.toNat = k.toNat := by
  rw [← UInt8.toNat_inj]

theorem decodeOrderType_none_iff (t : UInt8) :
    decodeOrderType t = none ↔ ¬(t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) := by
  simp only [u8_lit t]
  unfold decodeOrderType
  split <;> simp_all

theorem decodeSide_none_iff (t : UInt8) : decodeSide t = none ↔ ¬(t = 0 ∨ t = 1) := by
  simp only [u8_lit t]
  unfold decodeSide
  split <;> simp_all

theorem decodeStpMode_none_iff (t : UInt8) :
    decodeStpMode t = none ↔ ¬(t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) := by
  simp only [u8_lit t]
  unfold decodeStpMode
  split <;> simp_all

theorem decodeOrderType_market_iff {t : UInt8} {ot : COrderType} (h : decodeOrderType t = some ot) :
    ot = .market ↔ t = 1 := by
  simp only [u8_lit t]
  unfold decodeOrderType at h
  split at h <;> simp_all <;> (try subst h) <;> simp_all

/-- `toSpec` fails exactly on the request-only invalid cases, once the order
    type is supported. -/
theorem toSpec_none_of_supported {r : CRequest} {ot : COrderType}
    (hot : decodeOrderType r.orderType = some ot) :
    r.toSpec = none ↔
      (¬(r.side = 0 ∨ r.side = 1) ∨
       ¬(r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4) ∨
       r.qty = 0 ∨ (r.orderType ≠ 1 ∧ r.price = 0)) := by
  have hm := decodeOrderType_market_iff hot
  unfold CRequest.toSpec
  rw [hot]
  cases hs : decodeSide r.side with
  | none =>
    have := (decodeSide_none_iff _).mp hs
    simp [this]
  | some sd =>
    have hs' : r.side = 0 ∨ r.side = 1 := by
      by_cases hc : r.side = 0 ∨ r.side = 1
      · exact hc
      · rw [(decodeSide_none_iff _).mpr hc] at hs; cases hs
    cases hp : decodeStpMode r.stpMode with
    | none =>
      have := (decodeStpMode_none_iff _).mp hp
      simp [this]
    | some md =>
      have hp' : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4 := by
        by_cases hc : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4
        · exact hc
        · rw [(decodeStpMode_none_iff _).mpr hc] at hp; cases hp
      simp only [hs', hp', not_true_eq_false, false_or]
      by_cases hq : r.qty = 0
      · simp [hq]
      · by_cases hpr : ot ≠ .market ∧ r.price = 0
        · have : r.orderType ≠ 1 ∧ r.price = 0 := ⟨fun e => hpr.1 (hm.mpr e), hpr.2⟩
          simp [hq, hpr, this]
        · have : ¬(r.orderType ≠ 1 ∧ r.price = 0) := fun h => hpr ⟨fun e => h.1 (hm.mp e), h.2⟩
          simp only [hq, if_false, hpr]
          simp [this]

theorem staticCode_supported_invalid {cap : Nat} {r : CRequest} {c : ResultCode}
    (h1 : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3)
    (h : staticCode cap r = some c) : c = .rejectedInvalid := by
  unfold staticCode at h
  simp only [h1, not_true_eq_false, if_false] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    (try split at h) <;> first | exact (Option.some.inj h).symm | cases h

/-- **The spec agrees with the request-only checks.** -/
theorem processB_static {cap : Nat} {b : BookState} {r : CRequest} {c : ResultCode}
    (h : staticCode cap r = some c) : processB cap b (.order r) = rejectWith c b := by
  by_cases h1 : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3
  · cases hot : decodeOrderType r.orderType with
    | none => exact absurd h1 ((decodeOrderType_none_iff _).mp hot)
    | some ot =>
      have hc := staticCode_supported_invalid h1 h
      subst hc
      unfold processB
      simp only [hot]
      cases hts : r.toSpec with
      | none => rfl
      | some o =>
        have key := toSpec_none_of_supported hot
        have hall := (not_congr key).mp (by simp [hts])
        have hs : r.side = 0 ∨ r.side = 1 := by
          by_cases hx : r.side = 0 ∨ r.side = 1
          · exact hx
          · exact absurd (Or.inl hx) hall
        have hp : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4 := by
          by_cases hx : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4
          · exact hx
          · exact absurd (Or.inr (Or.inl hx)) hall
        have hq : r.qty ≠ 0 := fun hx => hall (Or.inr (Or.inr (Or.inl hx)))
        have hpr : ¬(r.orderType ≠ 1 ∧ r.price = 0) := fun hx => hall (Or.inr (Or.inr (Or.inr hx)))
        unfold staticCode at h
        simp only [h1, hs, hp, hq, hpr, not_true_eq_false, if_false] at h
        by_cases hqm : qmax cap < r.qty.toNat
        · simp [hqm]
        · simp [hqm] at h
  · have hot := (decodeOrderType_none_iff _).mpr h1
    unfold staticCode at h
    simp only [h1, not_false_eq_true, if_true, Option.some.injEq] at h
    subst h
    unfold processB
    simp [hot]

-- ============================================================================
-- The request-only checks, program side
-- ============================================================================

theorem Eval.when_false {P : Program} {c : Expr} {s : Stmt} {st : St S}
    (hc : evalExpr st c = .ok (.bool false)) : Eval P (whenS c s) st (st, .normal) :=
  Eval.ite_false hc (Eval.skip P st)

theorem Eval.when_true {P : Program} {c : Expr} {s : Stmt} {st : St S} {r}
    (hc : evalExpr st c = .ok (.bool true)) (hs : Eval P s st r) : Eval P (whenS c s) st r :=
  Eval.ite_true hc hs

theorem Eval.retcode {P : Program} {st : St S} (rc : ResultCode) :
    Eval P (MatcherProgram.retc rc) st (st, .ret (.code (codeOf rc))) := Eval.ret rfl

theorem ev_check1 (s : S) (r : CRequest) :
    evalExpr (orderSt s r) (not' (or' (or' (eqc "otype" OT_LIMIT) (eqc "otype" OT_MARKET))
                 (or' (eqc "otype" OT_IOC) (eqc "otype" OT_POST_ONLY)))) =
      .ok (.bool (decide ¬(r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3))) := by
  by_cases h0 : r.orderType = 0 <;> by_cases h1 : r.orderType = 1 <;>
    by_cases h2 : r.orderType = 2 <;> by_cases h3 : r.orderType = 3 <;> meval <;> simp_all

theorem ev_check2 (s : S) (r : CRequest) :
    evalExpr (orderSt s r) (not' (or' (eqc "side" SIDE_BUY) (eqc "side" SIDE_SELL))) =
      .ok (.bool (decide ¬(r.side = 0 ∨ r.side = 1))) := by
  by_cases h0 : r.side = 0 <;> by_cases h1 : r.side = 1 <;> meval <;> simp_all

theorem ev_check3 (s : S) (r : CRequest) :
    evalExpr (orderSt s r) (not' (or' (or' (eqc "stp" STP_NONE) (eqc "stp" STP_CANCEL_NEW))
                     (or' (or' (eqc "stp" STP_CANCEL_OLD) (eqc "stp" STP_CANCEL_BOTH))
                          (eqc "stp" STP_DECREMENT)))) =
      .ok (.bool (decide ¬(r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨
        r.stpMode = 4))) := by
  by_cases h0 : r.stpMode = 0 <;> by_cases h1 : r.stpMode = 1 <;> by_cases h2 : r.stpMode = 2 <;>
    by_cases h3 : r.stpMode = 3 <;> by_cases h4 : r.stpMode = 4 <;> meval <;> simp_all

theorem ev_check4 (s : S) (r : CRequest) :
    evalExpr (orderSt s r) (b2 .eq (v "qty") (u 0)) = .ok (.bool (decide (r.qty = 0))) := by
  by_cases h : r.qty = 0 <;> meval <;> simp_all

theorem ev_check5 (s : S) (r : CRequest) :
    evalExpr (orderSt s r) (and' (nec "otype" OT_MARKET) (b2 .eq (v "price") (u 0))) =
      .ok (.bool (decide (r.orderType ≠ 1 ∧ r.price = 0))) := by
  by_cases h0 : r.orderType = 1 <;> by_cases h1 : r.price = 0 <;> meval <;> simp_all

private theorem cap_mod (hcap : CapOk S) :
    capacity (S := S) % 18446744073709551616 + 1 < 18446744073709551616 := by
  unfold CapOk at hcap
  rw [Nat.mod_eq_of_lt (by omega)]; exact hcap

private theorem capU_toNat (hcap : CapOk S) :
    (UInt64.ofNat (capacity (S := S)) + 1).toNat = capacity (S := S) + 1 := by
  unfold CapOk at hcap
  have h1 : (UInt64.ofNat (capacity (S := S))).toNat = capacity (S := S) := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_add, h1, UInt64.toNat_one]
  exact Nat.mod_eq_of_lt hcap

private theorem capU_ne (hcap : CapOk S) : UInt64.ofNat (capacity (S := S)) + 1 ≠ 0 := by
  intro h
  have := congrArg UInt64.toNat h
  rw [capU_toNat hcap] at this
  simp at this

theorem ev_qmax (st : St S) (hcap : CapOk S) :
    evalExpr st qmaxE = .ok (.u64 (U64_MAX / (UInt64.ofNat (capacity (S := S)) + 1))) := by
  have hc : capacity (S := S) < 2 ^ 64 := by unfold CapOk at hcap; omega
  simp [qmaxE, evalExpr, evalBin, addU, divU, b2, u, hc, cap_mod hcap, capU_ne hcap, bind,
    Except.bind, Functor.map, Except.map, Nat.toUInt64]

theorem qmax_toNat (hcap : CapOk S) :
    (U64_MAX / (UInt64.ofNat (capacity (S := S)) + 1)).toNat = qmax (capacity (S := S)) := by
  rw [UInt64.toNat_div, capU_toNat hcap]
  rfl

theorem ev_check6 (s : S) (r : CRequest) (hcap : CapOk S) :
    evalExpr (orderSt s r) (b2 .lt qmaxE (v "qty")) =
      .ok (.bool (decide (qmax (capacity (S := S)) < r.qty.toNat))) := by
  have e := ev_qmax (orderSt s r) hcap
  show evalExpr (orderSt s r) (.bin .lt qmaxE (.var "qty")) = _
  simp only [evalExpr, e, bind, Except.bind]
  simp (config := {decide := true}) [lookupVar, orderSt, orderEnv, List.lookup, evalBin,
    UInt64.lt_iff_toNat_lt, qmax_toNat hcap]

theorem Eval.when_pass {P : Program} {c : Expr} {x : Stmt} {st : St S} {p : Prop} [Decidable p]
    (hc : evalExpr st c = .ok (.bool (decide p))) (hp : ¬ p) : Eval P (whenS c x) st (st, .normal) :=
  Eval.when_false (by rw [hc]; simp [hp])

theorem Eval.when_fire {P : Program} {c : Expr} {st : St S} {p : Prop} [Decidable p]
    (hc : evalExpr st c = .ok (.bool (decide p))) (hp : p) (rc : ResultCode) :
    Eval P (whenS c (MatcherProgram.retc rc)) st (st, .ret (.code (codeOf rc))) :=
  Eval.when_true (by rw [hc]; simp [hp]) (Eval.retcode rc)

/-- **The request-only checks, program side.** The first six statements of
    `gen_process_order` return `staticCode`'s code, or fall through with the
    state unchanged. -/
theorem prefix_run (hcap : CapOk S) (s : S) (r : CRequest) :
    (∀ c, staticCode (capacity (S := S)) r = some c →
      Eval program (Stmt.block processOrderStmts) (orderSt s r)
        (orderSt s r, .ret (.code (codeOf c)))) ∧
    (staticCode (capacity (S := S)) r = none → ∀ res,
      Eval program (Stmt.block (processOrderStmts.drop 6)) (orderSt s r) res →
      Eval program (Stmt.block processOrderStmts) (orderSt s r) res) := by
  have e1 := ev_check1 s r
  have e2 := ev_check2 s r
  have e3 := ev_check3 s r
  have e4 := ev_check4 s r
  have e5 := ev_check5 s r
  have e6 := ev_check6 s r hcap
  have p1 := fun h => Eval.when_pass (P := program) (x := MatcherProgram.retc .rejectedUnsupported) e1 h
  have p2 := fun h => Eval.when_pass (P := program) (x := MatcherProgram.retc .rejectedInvalid) e2 h
  have p3 := fun h => Eval.when_pass (P := program) (x := MatcherProgram.retc .rejectedInvalid) e3 h
  have p4 := fun h => Eval.when_pass (P := program) (x := MatcherProgram.retc .rejectedInvalid) e4 h
  have p5 := fun h => Eval.when_pass (P := program) (x := MatcherProgram.retc .rejectedInvalid) e5 h
  have p6 := fun h => Eval.when_pass (P := program) (x := MatcherProgram.retc .rejectedInvalid) e6 h
  simp only [processOrderStmts, List.drop]
  refine ⟨fun c hc => ?_, fun hn res hres => ?_⟩
  · unfold staticCode at hc
    by_cases h1 : ¬(r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3)
    · rw [if_pos h1, Option.some.injEq] at hc; subst hc
      exact Eval.block_cons_ret (Eval.when_fire e1 h1 _)
    rw [if_neg h1] at hc
    by_cases h2 : ¬(r.side = 0 ∨ r.side = 1)
    · rw [if_pos h2, Option.some.injEq] at hc; subst hc
      exact Eval.block_cons_normal (p1 h1) (Eval.block_cons_ret (Eval.when_fire e2 h2 _)) (by simp)
    rw [if_neg h2] at hc
    by_cases h3 : ¬(r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4)
    · rw [if_pos h3, Option.some.injEq] at hc; subst hc
      exact Eval.block_cons_normal (p1 h1) (Eval.block_cons_normal (p2 h2)
        (Eval.block_cons_ret (Eval.when_fire e3 h3 _)) (by simp)) (by simp)
    rw [if_neg h3] at hc
    by_cases h4 : r.qty = 0
    · rw [if_pos h4, Option.some.injEq] at hc; subst hc
      exact Eval.block_cons_normal (p1 h1) (Eval.block_cons_normal (p2 h2)
        (Eval.block_cons_normal (p3 h3) (Eval.block_cons_ret (Eval.when_fire e4 h4 _))
        (by simp)) (by simp)) (by simp)
    rw [if_neg h4] at hc
    by_cases h5 : r.orderType ≠ 1 ∧ r.price = 0
    · rw [if_pos h5, Option.some.injEq] at hc; subst hc
      exact Eval.block_cons_normal (p1 h1) (Eval.block_cons_normal (p2 h2)
        (Eval.block_cons_normal (p3 h3) (Eval.block_cons_normal (p4 h4)
        (Eval.block_cons_ret (Eval.when_fire e5 h5 _)) (by simp)) (by simp)) (by simp)) (by simp)
    rw [if_neg h5] at hc
    by_cases h6 : qmax (capacity (S := S)) < r.qty.toNat
    · rw [if_pos h6, Option.some.injEq] at hc; subst hc
      exact Eval.block_cons_normal (p1 h1) (Eval.block_cons_normal (p2 h2)
        (Eval.block_cons_normal (p3 h3) (Eval.block_cons_normal (p4 h4)
        (Eval.block_cons_normal (p5 h5) (Eval.block_cons_ret (Eval.when_fire e6 h6 _))
        (by simp)) (by simp)) (by simp)) (by simp)) (by simp)
    rw [if_neg h6] at hc; cases hc
  · unfold staticCode at hn
    have h1 : ¬¬(r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3) := by
      intro h; simp [h] at hn
    rw [if_neg h1] at hn
    have h2 : ¬¬(r.side = 0 ∨ r.side = 1) := by intro h; simp [h] at hn
    rw [if_neg h2] at hn
    have h3 : ¬¬(r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4) := by
      intro h; simp [h] at hn
    rw [if_neg h3] at hn
    have h4 : ¬(r.qty = 0) := by intro h; simp [h] at hn
    rw [if_neg h4] at hn
    have h5 : ¬(r.orderType ≠ 1 ∧ r.price = 0) := by intro h; simp [h] at hn
    rw [if_neg h5] at hn
    have h6 : ¬(qmax (capacity (S := S)) < r.qty.toNat) := by intro h; simp [h] at hn
    exact Eval.block_cons_normal (p1 h1) (Eval.block_cons_normal (p2 h2)
      (Eval.block_cons_normal (p3 h3) (Eval.block_cons_normal (p4 h4)
      (Eval.block_cons_normal (p5 h5) (Eval.block_cons_normal (p6 h6) hres
      (by simp)) (by simp)) (by simp)) (by simp)) (by simp)) (by simp)

-- ============================================================================
-- The decoded book: ids and size
-- ============================================================================

theorem mem_insLevel_iff {t : Tree} {x y : PriceLevel} {ys : List PriceLevel} :
    y ∈ insLevel t x ys ↔ y = x ∨ y ∈ ys := mem_insLevel

theorem sortLevels_perm (t : Tree) : ∀ (xs : List PriceLevel), (sortLevels t xs).Perm xs
  | [] => List.Perm.refl _
  | x :: xs => by
    simp only [sortLevels]
    have ih := sortLevels_perm t xs
    have hins : ∀ (ys : List PriceLevel), (insLevel t x ys).Perm (x :: ys) := by
      intro ys
      induction ys with
      | nil => exact List.Perm.refl _
      | cons y ys ihy =>
        simp only [insLevel]
        split
        · exact List.Perm.refl _
        · exact (ihy.cons y).trans (List.Perm.swap x y ys)
    exact (hins _).trans (ih.cons x)

theorem absQueue_length (db : Db) (t : Tree) :
    ∀ (i : Nat) (hs : List OrderH), (absQueue db t i hs).length = hs.length
  | _, [] => rfl
  | i, _ :: hs => by simp [absQueue, absQueue_length db t (i + 1) hs]

theorem absQueue_ids (db : Db) (t : Tree) :
    ∀ (i : Nat) (hs : List OrderH), (absQueue db t i hs).map Order.id =
      hs.map fun h => ((db.orders h).getD OrderRow.dflt).id.toNat
  | _, [] => rfl
  | i, _ :: hs => by simp [absQueue, restingOrder, absQueue_ids db t (i + 1) hs]

/-- The orders on one side of the decoded book, as a list up to order. -/
theorem absSide_orders_perm (db : Db) (t : Tree) :
    ((absSide db t).flatMap PriceLevel.orders).Perm
      (((db.tree t).map (absLevel db t)).flatMap PriceLevel.orders) :=
  (sortLevels_perm t _).flatMap_right _

theorem side_length (db : Db) (t : Tree) :
    ((absSide db t).flatMap PriceLevel.orders).length =
      ((db.tree t).map fun l => (db.queue l).length).sum := by
  rw [(absSide_orders_perm db t).length_eq, List.length_flatMap]
  simp [absLevel, absQueue_length, Function.comp_def]

/-- **(B)** The decoded book holds exactly the store's resting orders. -/
theorem bookSize_absBook (db : Db) : bookSize (absBook db) = restingCount db := by
  unfold bookSize allBookOrders restingCount
  rw [List.length_append]
  have hb := side_length db .bids
  have ha := side_length db .asks
  simp only [absBook] at hb ha ⊢
  rw [hb, ha, List.map_append, List.sum_append_nat]
  simp

/-- The ids on the decoded book are the ids of the queued rows. -/
theorem idOnBook_absBook {db : Db} (_hc : ClientInv db) (n : Nat) :
    idOnBook (absBook db) n = true ↔
      ∃ t, ∃ l ∈ db.tree t, ∃ h ∈ db.queue l, ((db.orders h).getD OrderRow.dflt).id.toNat = n := by
  have side : ∀ t, (∃ o ∈ (absSide db t).flatMap PriceLevel.orders, o.id = n) ↔
      ∃ l ∈ db.tree t, ∃ h ∈ db.queue l, ((db.orders h).getD OrderRow.dflt).id.toNat = n := by
    intro t
    have hp := absSide_orders_perm db t
    constructor
    · rintro ⟨o, ho, rfl⟩
      obtain ⟨lv, hlv, ho⟩ := List.mem_flatMap.mp (hp.mem_iff.mp ho)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hlv
      have hmem := List.mem_map_of_mem (f := Order.id) ho
      simp only [absLevel] at hmem
      rw [absQueue_ids] at hmem
      obtain ⟨h, hh, e⟩ := List.mem_map.mp hmem
      exact ⟨l, hl, h, hh, e⟩
    · rintro ⟨l, hl, h, hh, e⟩
      have : ((db.orders h).getD OrderRow.dflt).id.toNat ∈
          (absQueue db t 0 (db.queue l)).map Order.id := by
        rw [absQueue_ids]; exact List.mem_map_of_mem hh
      obtain ⟨o, ho, eo⟩ := List.mem_map.mp this
      refine ⟨o, hp.mem_iff.mpr (List.mem_flatMap.mpr ⟨absLevel db t l, List.mem_map_of_mem hl, ho⟩),
        eo.trans e⟩
  unfold idOnBook allBookOrders absBook
  simp only [List.any_append, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
  rw [side .bids, side .asks]
  constructor
  · rintro (⟨l, hl, h, hh, e⟩ | ⟨l, hl, h, hh, e⟩)
    · exact ⟨.bids, l, hl, h, hh, e⟩
    · exact ⟨.asks, l, hl, h, hh, e⟩
  · rintro ⟨t, l, hl, h, hh, e⟩
    cases t
    · exact Or.inl ⟨l, hl, h, hh, e⟩
    · exact Or.inr ⟨l, hl, h, hh, e⟩

-- ============================================================================
-- The store checks: duplicate id and capacity
-- ============================================================================

/-- **(A)** Under `Inv`, the hash finds an id exactly when the decoded book
    holds an order with that id. -/
theorem hashFind_isSome_iff {s : S} (hI : Inv s) (id : UInt64) :
    (hashFind s id).isSome = true ↔ idOnBook (absBook (view s)) id.toNat = true := by
  have hlaw := hashFind_law s id hI.wf
  rw [idOnBook_absBook hI.client]
  have rowid : ∀ h, (view s).orderLive h →
      (view s).orderId h = (((view s).orders h).getD OrderRow.dflt).id := by
    intro h hl
    cases ho : (view s).orders h with
    | none => simp [Db.orderLive, ho] at hl
    | some row => simp [Db.orderId, ho]
  cases hf : hashFind s id with
  | some h =>
    rw [hf] at hlaw
    obtain ⟨hh, hid⟩ := hlaw
    simp only [Option.isSome_some, true_iff]
    obtain ⟨l, hl⟩ := (hI.client.hash_iff_queued h).mp hh
    have hlive := (hI.wf.queue_live l h hl).1
    rcases hI.client.queue_in_tree l h hl with ht | ht
    · exact ⟨.bids, l, ht, h, hl, by rw [← rowid h hlive, hid]⟩
    · exact ⟨.asks, l, ht, h, hl, by rw [← rowid h hlive, hid]⟩
  | none =>
    rw [hf] at hlaw
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro t l _ h hh e
    have hhash := (hI.client.hash_iff_queued h).mpr ⟨l, hh⟩
    have hlive := (hI.wf.queue_live l h hh).1
    apply hlaw h hhash
    rw [rowid h hlive]
    exact UInt64.toNat_inj.mp e

theorem requestMayRest_iff {r : CRequest} :
    requestMayRest r = true ↔ (r.orderType = 0 ∨ r.orderType = 3) := by
  have e : ∀ k : UInt8, r.orderType = k ↔ r.orderType.toNat = k.toNat := fun k => by
    rw [← UInt8.toNat_inj]
  rw [e 0, e 3]
  unfold requestMayRest decodeOrderType
  generalize r.orderType.toNat = n
  rcases n with _ | _ | _ | _ | n <;> simp

/-- The spec after the request-only checks pass. -/
theorem processB_after_static {cap : Nat} {b : BookState} {r : CRequest}
    (hn : staticCode cap r = none) :
    ∃ o, r.toSpec = some o ∧ o.id = r.id.toNat ∧
      processB cap b (.order r) =
        if idOnBook b o.id then rejectWith .rejectedDuplicate b
        else if requestMayRest r && cap ≤ bookSize b then rejectWith .rejectedCapacity b
        else (postOnlyCode o b, processWithId b o) := by
  unfold staticCode at hn
  have h1 : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3 := by
    by_cases h : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3
    · exact h
    · rw [if_pos h] at hn; cases hn
  rw [if_neg (fun h => h h1)] at hn
  have h2 : r.side = 0 ∨ r.side = 1 := by
    by_cases h : r.side = 0 ∨ r.side = 1
    · exact h
    · rw [if_pos h] at hn; cases hn
  rw [if_neg (fun h => h h2)] at hn
  have h3 : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4 := by
    by_cases h : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4
    · exact h
    · rw [if_pos h] at hn; cases hn
  rw [if_neg (fun h => h h3)] at hn
  have h4 : r.qty ≠ 0 := fun h => by rw [if_pos h] at hn; cases hn
  rw [if_neg h4] at hn
  have h5 : ¬(r.orderType ≠ 1 ∧ r.price = 0) := fun h => by rw [if_pos h] at hn; cases hn
  rw [if_neg h5] at hn
  have h6 : ¬(qmax cap < r.qty.toNat) := fun h => by rw [if_pos h] at hn; cases hn
  cases hot : decodeOrderType r.orderType with
  | none => exact absurd h1 ((decodeOrderType_none_iff _).mp hot)
  | some ot =>
    cases hts : r.toSpec with
    | none =>
      rcases (toSpec_none_of_supported hot).mp hts with h | h | h | h
      · exact absurd h2 h
      · exact absurd h3 h
      · exact absurd h h4
      · exact absurd h h5
    | some o =>
      have hid : o.id = r.id.toNat := by
        unfold CRequest.toSpec at hts
        split at hts
        · split at hts
          · cases hts
          · split at hts
            · cases hts
            · cases hts; rfl
        · cases hts
      refine ⟨o, rfl, hid, ?_⟩
      unfold processB
      simp only [hot, hts, h6, if_false]

-- ============================================================================
-- Statements 7–9 of gen_process_order
-- ============================================================================

/-- The environment after `dup := hashFind id`. -/
def dupEnv (r : CRequest) (x : Option OrderH) : List (Ident × Val) :=
  [("id", .u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
   ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price),
   ("qty", .u64 r.qty), ("dup", .order x), ("r", .code 0)]

def dupSt (s : S) (r : CRequest) : St S :=
  { store := s, env := dupEnv r (hashFind s r.id), trades := [] }

theorem eval_dup (s : S) (r : CRequest) :
    Eval program (call1 "dup" .hashFind [v "id"]) (orderSt s r) (dupSt s r, .normal) := by
  have h := Eval.ext (P := program) (dst := some "dup") (op := .hashFind) (args := [v "id"])
    (st := orderSt s r) (vals := [.u64 r.id]) (s' := s) (res := some (.order (hashFind s r.id)))
    (env := dupEnv r (hashFind s r.id))
    (by simp (config := {decide := true}) [v, evalExpr, lookupVar, orderSt, orderEnv, List.lookup,
      List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
    (by simp [runExt, asU64, orderSt, bind, Except.bind])
    (by simp (config := {decide := true}) [bindResult, setVar, orderSt, orderEnv, dupEnv,
      List.lookup, Val.ty])
  exact h

theorem ev_dupcheck (s : S) (r : CRequest) :
    evalExpr (dupSt s r) (not' (.isNullO (v "dup"))) =
      .ok (.bool (decide ((hashFind s r.id).isSome = true))) := by
  cases hx : hashFind s r.id <;>
    simp (config := {decide := true}) [dupSt, dupEnv, not', v, evalExpr, lookupVar, List.lookup,
      asBool, bind, Except.bind, hx]

theorem ev_capcheck (s : S) (r : CRequest) (hcap : CapOk S) (hcount : count s ≤ capacity (S := S)) :
    evalExpr (dupSt s r) (and' (or' (eqc "otype" OT_LIMIT) (eqc "otype" OT_POST_ONLY))
        (b2 .le .capacity .count)) =
      .ok (.bool (decide ((r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ count s))) := by
  have hc : capacity (S := S) < 2 ^ 64 := by unfold CapOk at hcap; omega
  have hn : count s < 2 ^ 64 := by omega
  by_cases h0 : r.orderType = 0 <;> by_cases h3 : r.orderType = 3 <;>
    simp (config := {decide := true}) [dupSt, dupEnv, and', or', eqc, b2, v, c, evalExpr, lookupVar,
      List.lookup, evalBin, asBool, bind, Except.bind, Functor.map, Except.map, hc, hn, h0, h3,
      OT_LIMIT, OT_POST_ONLY, UInt64.le_iff_toNat_le, Nat.toUInt64,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hn] <;> simp_all

-- ============================================================================
-- The four entry rejections refine processB
-- ============================================================================

/-- A rejection at entry: the store is unchanged and no trade is reported. -/
theorem refines_of_reject {s : S} {req : Req} {c : ResultCode} (hI : Inv s)
    (hrun : ∃ f, runEntry program f (entryOf req) (argsOf req) s = .ok (.code (codeOf c), s, []))
    (hspec : specStep s req = rejectWith c (absBook (view s))) : Refines s req := by
  obtain ⟨f, hf⟩ := hrun
  refine ⟨f, s, [], ?_, ?_, ?_, hI⟩
  · rw [hspec]; exact hf
  · rw [hspec]; rfl
  · rw [hspec]; rfl

theorem refines_static {s : S} {r : CRequest} {c : ResultCode} (hI : Inv s) (hcap : CapOk S)
    (hc : staticCode (capacity (S := S)) r = some c) : Refines s (.order r) := by
  refine refines_of_reject hI ?_ (processB_static hc)
  exact order_run ((prefix_run hcap s r).1 c hc)

theorem refines_duplicate {s : S} {r : CRequest} (hI : Inv s) (hcap : CapOk S)
    (hn : staticCode (capacity (S := S)) r = none) (hd : (hashFind s r.id).isSome = true) :
    Refines s (.order r) := by
  obtain ⟨o, _, hid, hspec⟩ := processB_after_static (b := absBook (view s)) hn
  have hbook : idOnBook (absBook (view s)) o.id = true := by
    rw [hid]; exact (hashFind_isSome_iff hI r.id).mp hd
  refine refines_of_reject hI ?_ (by unfold specStep; rw [hspec, if_pos hbook])
  have hbody : Eval program (Stmt.block (processOrderStmts.drop 6)) (orderSt s r)
      (dupSt s r, .ret (.code (codeOf .rejectedDuplicate))) := by
    simp only [processOrderStmts, List.drop]
    exact Eval.block_cons_normal (eval_dup s r)
      (Eval.block_cons_ret (Eval.when_fire (ev_dupcheck s r) hd _)) (by simp)
  exact order_run ((prefix_run hcap s r).2 hn _ hbody)

theorem refines_capacity {s : S} {r : CRequest} (hI : Inv s) (hcap : CapOk S)
    (hn : staticCode (capacity (S := S)) r = none) (hd : ¬(hashFind s r.id).isSome = true)
    (hfull : (r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ count s) :
    Refines s (.order r) := by
  obtain ⟨o, _, hid, hspec⟩ := processB_after_static (b := absBook (view s)) hn
  have hbook : ¬ idOnBook (absBook (view s)) o.id = true := by
    rw [hid]; exact fun h => hd ((hashFind_isSome_iff hI r.id).mpr h)
  have hmay : (requestMayRest r && decide (capacity (S := S) ≤ bookSize (absBook (view s)))) = true := by
    rw [bookSize_absBook, ← hI.count_eq]
    simp [requestMayRest_iff.mpr hfull.1, hfull.2]
  refine refines_of_reject hI ?_ (by unfold specStep; rw [hspec, if_neg hbook, if_pos hmay])
  have hbody : Eval program (Stmt.block (processOrderStmts.drop 6)) (orderSt s r)
      (dupSt s r, .ret (.code (codeOf .rejectedCapacity))) := by
    simp only [processOrderStmts, List.drop]
    exact Eval.block_cons_normal (eval_dup s r)
      (Eval.block_cons_normal (Eval.when_pass (ev_dupcheck s r) hd)
        (Eval.block_cons_ret (Eval.when_fire (ev_capcheck s r hcap hI.count_le) hfull _))
        (by simp)) (by simp)
  exact order_run ((prefix_run hcap s r).2 hn _ hbody)

-- ============================================================================
-- Cancel
-- ============================================================================

theorem findSome_side_none {levels : List PriceLevel} {sd : Side} {n : OrderId} :
    (levels.findSome? fun level => level.orders.findSome? fun order =>
        if order.id == n then some (sd, order) else none) = none ↔
      ∀ l ∈ levels, ∀ o ∈ l.orders, o.id ≠ n := by
  constructor
  · intro h l hl o ho e
    have h1 := List.findSome?_eq_none_iff.mp h l hl
    have h2 := List.findSome?_eq_none_iff.mp h1 o ho
    simp [e] at h2
  · intro h
    apply List.findSome?_eq_none_iff.mpr
    intro l hl
    apply List.findSome?_eq_none_iff.mpr
    intro o ho
    simp [h l hl o ho]

theorem findOrderOnBook_none_iff (b : BookState) (n : OrderId) :
    findOrderOnBook b n = none ↔
      (∀ l ∈ b.bids, ∀ o ∈ l.orders, o.id ≠ n) ∧ (∀ l ∈ b.asks, ∀ o ∈ l.orders, o.id ≠ n) := by
  unfold findOrderOnBook
  simp only
  cases hb : (b.bids.findSome? fun level => level.orders.findSome? fun order =>
      if order.id == n then some (Side.buy, order) else none) with
  | some r =>
    simp only [reduceCtorEq, false_iff]
    intro ⟨hb', _⟩
    rw [findSome_side_none.mpr hb'] at hb; cases hb
  | none =>
    simp only
    exact ⟨fun ha => ⟨findSome_side_none.mp hb, findSome_side_none.mp ha⟩,
      fun ⟨_, ha⟩ => findSome_side_none.mpr ha⟩

theorem idOnBook_false_iff (b : BookState) (n : OrderId) :
    idOnBook b n = false ↔
      (∀ l ∈ b.bids, ∀ o ∈ l.orders, o.id ≠ n) ∧ (∀ l ∈ b.asks, ∀ o ∈ l.orders, o.id ≠ n) := by
  unfold idOnBook allBookOrders
  rw [List.any_eq_false]
  constructor
  · intro h
    refine ⟨fun l hl o ho e => ?_, fun l hl o ho e => ?_⟩
    · exact h o (List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, hl, ho⟩)) (by simp [e])
    · exact h o (List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, hl, ho⟩)) (by simp [e])
  · intro ⟨hb, ha⟩ o ho e
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨l, hl, ho⟩ := List.mem_flatMap.mp ho
      exact hb l hl o ho (by simpa using e)
    · obtain ⟨l, hl, ho⟩ := List.mem_flatMap.mp ho
      exact ha l hl o ho (by simpa using e)

/-- `cancelOrder` finds nothing exactly when no order on the book has the id. -/
theorem cancelOrder_none_iff (b : BookState) (n : OrderId) :
    cancelOrder b n = none ↔ idOnBook b n = false := by
  rw [idOnBook_false_iff, ← findOrderOnBook_none_iff]
  unfold cancelOrder
  cases findOrderOnBook b n with
  | none => simp
  | some p =>
    obtain ⟨sd, o⟩ := p
    cases sd <;> simp

/-- The entry environment of `gen_cancel_order`. -/
def cancelEnv (id : UInt64) (x : Option OrderH) : List (Ident × Val) :=
  [("id", .u64 id), ("ord", .order x), ("lvl", .level none), ("side", .code 0)]

theorem cancel_run {s : S} {id : UInt64} {st₁ : St S} {k : UInt8}
    (h : Eval program (Stmt.block cancelOrderStmts)
      { store := s, env := cancelEnv id none, trades := [] } (st₁, .ret (.code k))) :
    ∃ f, runEntry program f "gen_cancel_order" (argsOf (.cancel id)) s =
      .ok (.code k, st₁.store, st₁.trades) := by
  refine runEntry_of_eval lookup_cancel_order
    (penv := [("id", .u64 id)]) (by simp [bindParams, cancelOrderFun, argsOf, Val.ty,
      Functor.map, Except.map]) ?_ rfl
  have : [("id", Val.u64 id)] ++ cancelOrderFun.locals.map (fun (x, t) => (x, t.default)) =
      cancelEnv id none := by simp [cancelOrderFun, cancelEnv, Ty.default]
  rw [this]; exact h

theorem eval_cancel_find (s : S) (id : UInt64) :
    Eval program (call1 "ord" .hashFind [v "id"])
      ({ store := s, env := cancelEnv id none, trades := [] } : St S)
      ({ store := s, env := cancelEnv id (hashFind s id), trades := [] }, .normal) :=
  Eval.ext (by simp (config := {decide := true}) [v, evalExpr, lookupVar, cancelEnv, List.lookup,
      List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
    (runExt_hashFind id)
    (by simp (config := {decide := true}) [bindResult, setVar, cancelEnv, List.lookup, Val.ty])

theorem refines_cancel_unknown {s : S} {id : UInt64} (hI : Inv s)
    (hn : hashFind s id = none) : Refines s (.cancel id) := by
  have hnot : idOnBook (absBook (view s)) id.toNat = false := by
    cases hb : idOnBook (absBook (view s)) id.toNat
    · rfl
    · have := (hashFind_isSome_iff hI id).mpr hb
      rw [hn] at this; cases this
  refine refines_of_reject hI ?_ (by
    unfold specStep processB
    simp only
    rw [(cancelOrder_none_iff _ _).mpr hnot])
  show ∃ f, runEntry program f "gen_cancel_order" (argsOf (.cancel id)) s = _
  refine cancel_run (st₁ := { store := s, env := cancelEnv id (hashFind s id), trades := [] }) ?_
  simp only [cancelOrderStmts]
  refine Eval.block_cons_normal (eval_cancel_find s id)
    (Eval.block_cons_ret (Eval.when_true ?_ (Eval.retcode _))) (by simp)
  simp (config := {decide := true}) [hn, cancelEnv, evalExpr, v, lookupVar, List.lookup, bind,
    Except.bind]

end MatcherRefines

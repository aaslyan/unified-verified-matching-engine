import Matcher.StoreStep

/-!
# Phase 4: the side function, statement by statement

`sideFun isBuy` (`gen_process_buy` / `gen_process_sell`) split into named
pieces (`sideFun_body`, by `rfl`), its local environment as a record `Loc`,
and one evaluation lemma per statement of the matching loop. The lemmas state
exactly which contract preconditions each statement needs; the loop proofs
(`Inner.lean`, `Outer.lean`) discharge them from the loop invariant.
-/

namespace MatcherLoop

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore

-- ============================================================================
-- The pieces of sideFun
-- ============================================================================

def contraT (isBuy : Bool) : Tree := if isBuy then .asks else .bids
def ownT (isBuy : Bool) : Tree := if isBuy then .bids else .asks

def crossesE (isBuy : Bool) (bp : Expr) : Expr :=
  if isBuy then b2 .le bp (v "price") else b2 .le (v "price") bp

def stpCond : Expr :=
  and' (and' (b2 .ne (v "account") (u 0)) (b2 .eq (v "account") (.getO (v "passive") .account)))
    (nec "stp" STP_NONE)

def cancelOldBlock : Stmt := Stmt.block [
  .assign "victim" (v "passive"),
  call1 "passive" .qNext [v "passive"],
  removeResting "best" "victim",
  whenS (eqc "stp" STP_CANCEL_BOTH) (.assign "rem" (u 0))]

def decStmts : List Stmt := [
  .call (some "fill") "gen_min_u64" [v "rem", .getO (v "passive") .remaining],
  .assign "rem" (b2 .sub (v "rem") (v "fill")),
  .assign "prem" (b2 .sub (.getO (v "passive") .remaining) (v "fill")),
  call0 (.setO .remaining) [v "passive", v "prem"],
  call1 "nextp" .qNext [v "passive"],
  whenS (b2 .eq (v "prem") (u 0)) (removeResting "best" "passive"),
  .assign "passive" (v "nextp")]

def fillStmts : List Stmt := [
  .call (some "fill") "gen_min_u64" [v "rem", .getO (v "passive") .remaining],
  .assign "rem" (b2 .sub (v "rem") (v "fill")),
  .assign "prem" (b2 .sub (.getO (v "passive") .remaining) (v "fill")),
  call0 (.setO .remaining) [v "passive", v "prem"],
  .emit (.getO (v "passive") .id) (v "id") (.getL (v "best") .price) (v "fill"),
  call1 "nextp" .qNext [v "passive"],
  whenS (b2 .eq (v "prem") (u 0)) (removeResting "best" "passive"),
  .assign "passive" (v "nextp")]

def innerBody : Stmt :=
  .ite stpCond
    (.ite (eqc "stp" STP_CANCEL_NEW) (.assign "rem" (u 0))
      (.ite (or' (eqc "stp" STP_CANCEL_OLD) (eqc "stp" STP_CANCEL_BOTH)) cancelOldBlock
        (Stmt.block decStmts)))
    (Stmt.block fillStmts)

def innerCond : Expr := and' (not' (.isNullO (v "passive"))) (b2 .lt (u 0) (v "rem"))

def freeStmt (isBuy : Bool) : Stmt :=
  whenS (b2 .eq (.getL (v "best") .count) (u 0)) (Stmt.block [
    call0 (.tRemove (contraT isBuy)) [v "best"],
    call0 .levelFree [v "best"]])

def crossCond (isBuy : Bool) : Expr :=
  and' (nec "otype" OT_MARKET) (not' (crossesE isBuy (.getL (v "best") .price)))

def matchBlock (isBuy : Bool) : Stmt := Stmt.block [
  call1 "passive" .qFirst [v "best"],
  .loop (.capPlus 1) innerCond innerBody,
  freeStmt isBuy]

def outerBody (isBuy : Bool) : Stmt := Stmt.block [
  call1 "best" (.tBest (contraT isBuy)) [],
  .ite (.isNullL (v "best")) (.assign "stop" (.blit true))
    (.ite (crossCond isBuy) (.assign "stop" (.blit true)) (matchBlock isBuy))]

def outerCond : Expr := and' (b2 .lt (u 0) (v "rem")) (not' (v "stop"))

def outerLoop (isBuy : Bool) : Stmt := .loop (.capPlus 1) outerCond (outerBody isBuy)

def poStmt (isBuy : Bool) : Stmt :=
  whenS (eqc "otype" OT_POST_ONLY) (Stmt.block [
    call1 "best" (.tBest (contraT isBuy)) [],
    whenS (and' (not' (.isNullL (v "best"))) (crossesE isBuy (.getL (v "best") .price)))
      (retc .rejectedPostOnly)])

def restCond : Expr :=
  and' (b2 .lt (u 0) (v "rem")) (and' (nec "otype" OT_IOC) (nec "otype" OT_MARKET))

def newLevelStmt (isBuy : Bool) : Stmt :=
  whenS (.isNullL (v "lvl")) (Stmt.block [
    call1 "lvl" .levelAlloc [],
    whenS (.isNullL (v "lvl")) (Stmt.block [
      call0 .orderFree [v "ord"],
      retc .rejectedCapacity]),
    call0 (.setL .price) [v "lvl", v "price"],
    call0 (.tInsert (ownT isBuy)) [v "lvl"],
    .assign "isnew" (.blit true)])

def hashFailStmt (isBuy : Bool) : Stmt :=
  whenS (not' (v "ok")) (Stmt.block [
    call0 .qRemove [v "lvl", v "ord"],
    whenS (and' (v "isnew") (b2 .eq (.getL (v "lvl") .count) (u 0))) (Stmt.block [
      call0 (.tRemove (ownT isBuy)) [v "lvl"],
      call0 .levelFree [v "lvl"]]),
    call0 .orderFree [v "ord"],
    retc .rejectedDuplicate])

def restStmts (isBuy : Bool) : List Stmt := [
  call1 "ord" .orderAlloc [],
  whenS (.isNullO (v "ord")) (retc .rejectedCapacity),
  call0 (.setO .id) [v "ord", v "id"],
  call0 (.setO .account) [v "ord", v "account"],
  call0 (.setO .side) [v "ord", v "side"],
  call0 (.setO .stpMode) [v "ord", v "stp"],
  call0 (.setO .price) [v "ord", v "price"],
  call0 (.setO .qty) [v "ord", v "qty"],
  call0 (.setO .remaining) [v "ord", v "rem"],
  call1 "lvl" (.tFind (ownT isBuy)) [v "price"],
  newLevelStmt isBuy,
  call0 .qInsertTail [v "lvl", v "ord"],
  call1 "ok" .hashInsert [v "ord"],
  hashFailStmt isBuy]

def restStmt (isBuy : Bool) : Stmt := whenS restCond (Stmt.block (restStmts isBuy))

theorem sideFun_body (isBuy : Bool) :
    (sideFun isBuy).body = Stmt.block [poStmt isBuy, .assign "rem" (v "qty"), outerLoop isBuy,
      restStmt isBuy, retc .accepted] := by
  cases isBuy <;> rfl

-- ============================================================================
-- The local environment
-- ============================================================================

structure Loc where
  rem : UInt64 := 0
  stop : Bool := false
  best : Option LevelH := none
  passive : Option OrderH := none
  nextp : Option OrderH := none
  victim : Option OrderH := none
  fill : UInt64 := 0
  prem : UInt64 := 0
  ord : Option OrderH := none
  lvl : Option LevelH := none
  isnew : Bool := false
  ok : Bool := false

def sEnv (r : CRequest) (L : Loc) : List (Ident × Val) :=
  [("id", .u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
   ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price),
   ("qty", .u64 r.qty), ("rem", .u64 L.rem), ("stop", .bool L.stop), ("best", .level L.best),
   ("passive", .order L.passive), ("nextp", .order L.nextp), ("victim", .order L.victim),
   ("fill", .u64 L.fill), ("prem", .u64 L.prem), ("ord", .order L.ord), ("lvl", .level L.lvl),
   ("isnew", .bool L.isnew), ("ok", .bool L.ok)]

variable {S : Type} [EngineDb S]

def mkSt (s : S) (r : CRequest) (L : Loc) (ts : List TradeObs) : St S :=
  { store := s, env := sEnv r L, trades := ts }

/-- Evaluate in a side-function environment. -/
syntax "lsimp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| lsimp) => `(tactic|
      simp (config := {decide := true}) [mkSt, sEnv, evalExpr, lookupVar, List.lookup, evalBin,
        asBool, asU64, bind, Except.bind, Functor.map, Except.map, pure, Except.pure, List.mapM,
        List.mapM.loop, and', or', not', eqc, nec, b2, v, u, c, liveOrder, liveLevel, viewOf,
        OT_LIMIT, OT_MARKET, OT_IOC, OT_POST_ONLY, STP_NONE, STP_CANCEL_NEW, STP_CANCEL_OLD,
        STP_CANCEL_BOTH, STP_DECREMENT, bindResult, setVar, Val.ty])
  | `(tactic| lsimp [$xs,*]) => `(tactic|
      simp (config := {decide := true}) [mkSt, sEnv, evalExpr, lookupVar, List.lookup, evalBin,
        asBool, asU64, bind, Except.bind, Functor.map, Except.map, pure, Except.pure, List.mapM,
        List.mapM.loop, and', or', not', eqc, nec, b2, v, u, c, liveOrder, liveLevel, viewOf,
        OT_LIMIT, OT_MARKET, OT_IOC, OT_POST_ONLY, STP_NONE, STP_CANCEL_NEW, STP_CANCEL_OLD,
        STP_CANCEL_BOTH, STP_DECREMENT, bindResult, setVar, Val.ty, $xs,*])

section Set

variable (r : CRequest) (L : Loc)

theorem set_rem (x : UInt64) : setVar (sEnv r L) "rem" (.u64 x) = .ok (sEnv r { L with rem := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_stop (x : Bool) : setVar (sEnv r L) "stop" (.bool x) = .ok (sEnv r { L with stop := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_best (x : Option LevelH) :
    setVar (sEnv r L) "best" (.level x) = .ok (sEnv r { L with best := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_passive (x : Option OrderH) :
    setVar (sEnv r L) "passive" (.order x) = .ok (sEnv r { L with passive := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_nextp (x : Option OrderH) :
    setVar (sEnv r L) "nextp" (.order x) = .ok (sEnv r { L with nextp := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_victim (x : Option OrderH) :
    setVar (sEnv r L) "victim" (.order x) = .ok (sEnv r { L with victim := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_fill (x : UInt64) : setVar (sEnv r L) "fill" (.u64 x) = .ok (sEnv r { L with fill := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_prem (x : UInt64) : setVar (sEnv r L) "prem" (.u64 x) = .ok (sEnv r { L with prem := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_ord (x : Option OrderH) :
    setVar (sEnv r L) "ord" (.order x) = .ok (sEnv r { L with ord := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_lvl (x : Option LevelH) :
    setVar (sEnv r L) "lvl" (.level x) = .ok (sEnv r { L with lvl := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_isnew (x : Bool) : setVar (sEnv r L) "isnew" (.bool x) = .ok (sEnv r { L with isnew := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]
theorem set_ok (x : Bool) : setVar (sEnv r L) "ok" (.bool x) = .ok (sEnv r { L with ok := x }) := by
  simp (config := {decide := true}) [setVar, sEnv, List.lookup, Val.ty]

end Set

-- ============================================================================
-- Generic statement rules in a side-function state
-- ============================================================================

theorem ev_ext {P : Program} {dst : Option Ident} {op : Ext} {args : List Expr} {s s' : S}
    {r : CRequest} {L L' : Loc} {ts : List TradeObs} {vals : List Val} {res : Option Val}
    (hv : args.mapM (evalExpr (mkSt s r L ts)) = .ok vals)
    (hr : runExt (mkSt s r L ts) op vals = .ok (s', res))
    (hb : bindResult (sEnv r L) dst res = .ok (sEnv r L')) :
    Eval P (.ext dst op args) (mkSt s r L ts) (mkSt s' r L' ts, .normal) :=
  Eval.ext hv hr hb

theorem ev_assign {P : Program} {x : Ident} {e : Expr} {s : S} {r : CRequest} {L L' : Loc}
    {ts : List TradeObs} {val : Val}
    (he : evalExpr (mkSt s r L ts) e = .ok val) (hs : setVar (sEnv r L) x val = .ok (sEnv r L')) :
    Eval P (.assign x e) (mkSt s r L ts) (mkSt s r L' ts, .normal) :=
  Eval.assign he hs

-- ============================================================================
-- The statements of the matching loop
-- ============================================================================

section Stmts

variable {P : Program} {s : S} {r : CRequest} {L : Loc} {ts : List TradeObs}

open EngineDb

theorem ev_tBest (t : Tree) :
    Eval P (call1 "best" (.tBest t) []) (mkSt s r L ts)
      (mkSt s r { L with best := tBest s t } ts, .normal) :=
  ev_ext (vals := []) (by lsimp) (runExt_tBest t) (set_best r L _)

theorem ev_stop : Eval P (.assign "stop" (.blit true)) (mkSt s r L ts)
    (mkSt s r { L with stop := true } ts, .normal) :=
  ev_assign (by lsimp) (set_stop r L true)

theorem ev_rem0 : Eval P (.assign "rem" (u 0)) (mkSt s r L ts)
    (mkSt s r { L with rem := 0 } ts, .normal) :=
  ev_assign (by lsimp) (set_rem r L 0)

theorem ev_qFirst {l : LevelH} (hb : L.best = some l) (hl : liveL (view s) l = true) :
    Eval P (call1 "passive" .qFirst [v "best"]) (mkSt s r L ts)
      (mkSt s r { L with passive := qFirst s l } ts, .normal) :=
  ev_ext (vals := [.level (some l)]) (by lsimp [hb]) (runExt_qFirst hl) (set_passive r L _)

theorem ev_victim {h : OrderH} (hp : L.passive = some h) :
    Eval P (.assign "victim" (v "passive")) (mkSt s r L ts)
      (mkSt s r { L with victim := some h } ts, .normal) :=
  ev_assign (by lsimp [hp]) (set_victim r L _)

theorem ev_qNextP {h : OrderH} (hp : L.passive = some h) (hl : liveO (view s) h = true)
    (hq : queuedB (view s) h = true) :
    Eval P (call1 "passive" .qNext [v "passive"]) (mkSt s r L ts)
      (mkSt s r { L with passive := qNext s h } ts, .normal) :=
  ev_ext (vals := [.order (some h)]) (by lsimp [hp]) (runExt_qNext hl hq) (set_passive r L _)

theorem ev_qNextN {h : OrderH} (hp : L.passive = some h) (hl : liveO (view s) h = true)
    (hq : queuedB (view s) h = true) :
    Eval P (call1 "nextp" .qNext [v "passive"]) (mkSt s r L ts)
      (mkSt s r { L with nextp := qNext s h } ts, .normal) :=
  ev_ext (vals := [.order (some h)]) (by lsimp [hp]) (runExt_qNext hl hq) (set_nextp r L _)

theorem ev_passiveNext : Eval P (.assign "passive" (v "nextp")) (mkSt s r L ts)
    (mkSt s r { L with passive := L.nextp } ts, .normal) :=
  ev_assign (by lsimp) (set_passive r L _)

/-- The store after unlinking and freeing order `h` of level `l`. -/
def dropS (s : S) (l : LevelH) (h : OrderH) : S := orderFree (hashRemove (qRemove s l h) h) h

theorem dropS_facts {s : S} {l : LevelH} {h : OrderH} (hw : (view s).WF)
    (hh : h ∈ (view s).queue l) (hhash : h ∈ (view s).hash) :
    view (dropS s l h) = dropDb (view s) l h ∧ (view (dropS s l h)).WF ∧
      count (dropS s l h) + 1 = count s ∧ levelsUsed (dropS s l h) = levelsUsed s ∧
      liveO (view (qRemove s l h)) h = true ∧ inHashB (view (qRemove s l h)) h = true ∧
      liveO (view (hashRemove (qRemove s l h) h)) h = true ∧
      queuedB (view (hashRemove (qRemove s l h) h)) h = false ∧
      inHashB (view (hashRemove (qRemove s l h) h)) h = false := by
  have hlive : (view s).orderLive h := (hw.queue_live l h hh).1
  have hv1 : view (qRemove s l h) = { view s with queue := upd (view s).queue l (((view s).queue l).erase h) } :=
    qRemove_law s l h hw hh
  have hw1 : (view (qRemove s l h)).WF := qRemove_preserves_WF hw hv1
  have hhash1 : h ∈ (view (qRemove s l h)).hash := by rw [hv1]; exact hhash
  have hv2 : view (hashRemove (qRemove s l h) h) =
      { view (qRemove s l h) with hash := (view (qRemove s l h)).hash.erase h } :=
    hashRemove_law _ h hw1 hhash1
  have hw2 : (view (hashRemove (qRemove s l h) h)).WF := hashRemove_preserves_WF hw1 hv2
  have hnq2 : ¬ (view (hashRemove (qRemove s l h) h)).queued h := by
    rintro ⟨x, hx⟩
    rw [hv2, hv1] at hx
    by_cases hxl : x = l
    · subst hxl
      simp only [upd_same] at hx
      exact (hw.queue_nodup x).not_mem_erase hx
    · simp only [upd_other _ _ hxl] at hx
      exact hxl (hw.queue_unique _ _ _ hx hh)
  have hnh2 : h ∉ (view (hashRemove (qRemove s l h) h)).hash := by
    rw [hv2]; exact hw1.hash_nodup.not_mem_erase
  have hlive2 : (view (hashRemove (qRemove s l h) h)).orderLive h := by rw [hv2, hv1]; exact hlive
  have hpre3 : orderFree.pre (view (hashRemove (qRemove s l h) h)) h := ⟨hlive2, hnq2, hnh2⟩
  have hv3 : view (dropS s l h) = { view (hashRemove (qRemove s l h) h) with
      orders := upd (view (hashRemove (qRemove s l h) h)).orders h none,
      oLive := (view (hashRemove (qRemove s l h) h)).oLive.erase h } :=
    orderFree_law _ h hw2 hpre3
  refine ⟨?_, orderFree_preserves_WF hw2 hpre3 hv3, ?_, ?_, ?_, ?_, hlive2, queuedB_false_of hnq2,
    by simpa [inHashB] using hnh2⟩
  · rw [hv3, hv2, hv1]; rfl
  · have a := count_qRemove s l h
    have b := count_hashRemove (qRemove s l h) h
    have c := count_orderFree _ h hw2 hpre3
    unfold dropS; omega
  · unfold dropS; rw [levelsUsed_orderFree, levelsUsed_hashRemove, levelsUsed_qRemove]
  · show ((view (qRemove s l h)).orders h).isSome = true; rw [hv1]; exact hlive
  · exact List.contains_iff_mem.mpr hhash1

/-- `removeResting "best" x` with `best = l`, `x = h`, `h` queued at `l`. -/
theorem ev_remove {x : Ident} {l : LevelH} {h : OrderH} (hb : L.best = some l)
    (hx : ∀ s' : S, evalExpr (mkSt s' r L ts) (v x) = .ok (.order (some h)))
    (hw : (view s).WF) (hh : h ∈ (view s).queue l) (hhash : h ∈ (view s).hash)
    (hl : liveL (view s) l = true) :
    Eval P (removeResting "best" x) (mkSt s r L ts) (mkSt (dropS s l h) r L ts, .normal) := by
  obtain ⟨_, _, _, _, hl1, hin1, hl2, hq2, hn2⟩ := dropS_facts hw hh hhash
  have hlo : liveO (view s) h = true := (hw.queue_live l h hh).1
  have hvb : ∀ s' : S, evalExpr (mkSt s' r L ts) (v "best") = .ok (.level (some l)) := by
    intro s'; lsimp [hb]
  have hvx := hx
  have a1 : Eval P (call0 .qRemove [v "best", v x]) (mkSt s r L ts)
      (mkSt (qRemove s l h) r L ts, .normal) :=
    ev_ext (vals := [.level (some l), .order (some h)])
      (by simp [List.mapM, List.mapM.loop, hvb, hvx, bind, Except.bind, pure, Except.pure])
      (runExt_qRemove hl hlo (List.contains_iff_mem.mpr hh)) rfl
  have a2 : Eval P (call0 .hashRemove [v x]) (mkSt (qRemove s l h) r L ts)
      (mkSt (hashRemove (qRemove s l h) h) r L ts, .normal) :=
    ev_ext (vals := [.order (some h)])
      (by simp [List.mapM, List.mapM.loop, hvx, bind, Except.bind, pure, Except.pure])
      (runExt_hashRemove hl1 hin1) rfl
  have a3 : Eval P (call0 .orderFree [v x]) (mkSt (hashRemove (qRemove s l h) h) r L ts)
      (mkSt (dropS s l h) r L ts, .normal) :=
    ev_ext (vals := [.order (some h)])
      (by simp [List.mapM, List.mapM.loop, hvx, bind, Except.bind, pure, Except.pure])
      (runExt_orderFree hl2 hq2 hn2) rfl
  exact Eval.block_cons_normal a1 (Eval.block_cons_normal a2 a3 (by simp)) (by simp)

/-- `gen_min_u64`. -/
def umin (a b : UInt64) : UInt64 := if a < b then a else b

theorem umin_toNat (a b : UInt64) : (umin a b).toNat = min a.toNat b.toNat := by
  unfold umin
  split
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega

theorem umin_le_left (a b : UInt64) : (umin a b).toNat ≤ a.toNat := by rw [umin_toNat]; omega
theorem umin_le_right (a b : UInt64) : (umin a b).toNat ≤ b.toNat := by rw [umin_toNat]; omega

theorem lookup_min : lookupFun program "gen_min_u64" = .ok minFun := by
  simp (config := {decide := true}) [lookupFun, program, minFun]

theorem ev_min {h : OrderH} {row : OrderRow} (hp : L.passive = some h) (hlo : liveO (view s) h = true)
    (hr : readOrder s h = some row) :
    Eval program (.call (some "fill") "gen_min_u64" [v "rem", .getO (v "passive") .remaining])
      (mkSt s r L ts) (mkSt s r { L with fill := umin L.rem row.remaining } ts, .normal) := by
  have hbody : Eval program minFun.body { store := s, env := [("a", .u64 L.rem), ("b", .u64 row.remaining)] ++ minFun.locals.map (fun (x, t) => (x, t.default)), trades := ts } ({ store := s, env := [("a", .u64 L.rem), ("b", .u64 row.remaining)] ++ minFun.locals.map (fun (x, t) => (x, t.default)), trades := ts }, .ret (.u64 (umin L.rem row.remaining))) := by
    unfold umin
    by_cases hlt : L.rem < row.remaining
    · refine Eval.ite_true ?_ (Eval.ret ?_)
      · simp [minFun, evalExpr, b2, v, lookupVar, List.lookup, evalBin, hlt, bind, Except.bind]
      · simp [minFun, evalExpr, v, lookupVar, List.lookup, hlt]
    · refine Eval.ite_false ?_ (Eval.ret ?_)
      · simp [minFun, evalExpr, b2, v, lookupVar, List.lookup, evalBin, hlt, bind, Except.bind]
      · simp [minFun, evalExpr, v, lookupVar, List.lookup, hlt]
  exact Eval.call (st := mkSt s r L ts) (dst := some "fill") (fd := minFun)
    (vals := [.u64 L.rem, .u64 row.remaining])
    (penv := [("a", .u64 L.rem), ("b", .u64 row.remaining)])
    (v := .u64 (umin L.rem row.remaining)) (env := sEnv r { L with fill := umin L.rem row.remaining })
    lookup_min (by lsimp [hp, hlo, hr, getOField])
    (by simp [bindParams, minFun, Val.ty, Functor.map, Except.map]) hbody rfl
    (by simp only [bindResult]; exact set_fill r L _)

theorem ev_subRem (hf : L.fill ≤ L.rem) :
    Eval P (.assign "rem" (b2 .sub (v "rem") (v "fill"))) (mkSt s r L ts)
      (mkSt s r { L with rem := L.rem - L.fill } ts, .normal) :=
  ev_assign (by
    have : L.fill.toNat ≤ L.rem.toNat := UInt64.le_iff_toNat_le.mp hf
    lsimp [subU, this]) (set_rem r L _)

theorem ev_prem {h : OrderH} {row : OrderRow} (hp : L.passive = some h) (hlo : liveO (view s) h = true)
    (hr : readOrder s h = some row) (hf : L.fill ≤ row.remaining) :
    Eval P (.assign "prem" (b2 .sub (.getO (v "passive") .remaining) (v "fill"))) (mkSt s r L ts)
      (mkSt s r { L with prem := row.remaining - L.fill } ts, .normal) :=
  ev_assign (by
    have : L.fill.toNat ≤ row.remaining.toNat := UInt64.le_iff_toNat_le.mp hf
    lsimp [subU, this, hp, hlo, hr, getOField]) (set_prem r L _)

theorem ev_setRem {h : OrderH} {row : OrderRow} (hp : L.passive = some h)
    (hlo : liveO (view s) h = true) (hr : readOrder s h = some row) :
    Eval P (call0 (.setO .remaining) [v "passive", v "prem"]) (mkSt s r L ts)
      (mkSt (writeOrder s h { row with remaining := L.prem }) r L ts, .normal) :=
  ev_ext (vals := [.order (some h), .u64 L.prem]) (by lsimp [hp])
    (runExt_setO hlo hr (by simp) (by simp [setOField])) rfl

theorem boundVal_trade (hcap : CapOk S) :
    boundVal (S := S) program.tradeCap = .ok (capacity (S := S) + 1) := by
  unfold CapOk at hcap
  simp [boundVal, program, hcap]

theorem ev_emit {h : OrderH} {row : OrderRow} {l : LevelH} {lrow : LevelRow} (hcap : CapOk S)
    (hp : L.passive = some h) (hlo : liveO (view s) h = true) (hr : readOrder s h = some row)
    (hb : L.best = some l) (hl : liveL (view s) l = true) (hrl : readLevel s l = some lrow)
    (hlen : ts.length < capacity (S := S) + 1) :
    Eval program (.emit (.getO (v "passive") .id) (v "id") (.getL (v "best") .price) (v "fill"))
      (mkSt s r L ts)
      (mkSt s r L (ts ++ [toNatTrade row.id r.id lrow.price L.fill]), .normal) :=
  Eval.emit (by lsimp [hp, hlo, hr, getOField]) (by lsimp) (by lsimp [hb, hl, hrl]) (by lsimp)
    (boundVal_trade hcap) hlen

theorem ev_premWhen_zero {l : LevelH} {h : OrderH} (hz : L.prem = 0) (hb : L.best = some l)
    (hp : L.passive = some h) (hw : (view s).WF) (hh : h ∈ (view s).queue l)
    (hhash : h ∈ (view s).hash) (hl : liveL (view s) l = true) :
    Eval P (whenS (b2 .eq (v "prem") (u 0)) (removeResting "best" "passive")) (mkSt s r L ts)
      (mkSt (dropS s l h) r L ts, .normal) :=
  Eval.when_true (by lsimp [hz]) (ev_remove hb (fun _ => by lsimp [hp]) hw hh hhash hl)

theorem ev_premWhen_pos (hz : L.prem ≠ 0) :
    Eval P (whenS (b2 .eq (v "prem") (u 0)) (removeResting "best" "passive")) (mkSt s r L ts)
      (mkSt s r L ts, .normal) :=
  Eval.when_false (by lsimp [hz])

-- Conditions

theorem ev_stpCond {h : OrderH} {row : OrderRow} (hp : L.passive = some h)
    (hlo : liveO (view s) h = true) (hr : readOrder s h = some row) :
    evalExpr (mkSt s r L ts) stpCond =
      .ok (.bool (decide (r.account ≠ 0 ∧ r.account = row.account ∧ r.stpMode ≠ 0))) := by
  by_cases h1 : r.account = 0
  · simp only [stpCond]; lsimp [h1]
  · by_cases h2 : r.account = row.account
    · have h1' : ¬ row.account = 0 := h2 ▸ h1
      by_cases h3 : r.stpMode = 0 <;>
        (simp only [stpCond]; lsimp [h1, h1', h2, h3, hp, hlo, hr, getOField])
    · by_cases h3 : r.stpMode = 0 <;>
        (simp only [stpCond]; lsimp [h1, h2, h3, hp, hlo, hr, getOField])

theorem ev_stp_eq (k : UInt8) :
    evalExpr (mkSt s r L ts) (eqc "stp" k) = .ok (.bool (decide (r.stpMode = k))) := by
  by_cases h : r.stpMode = k <;> lsimp [h]

theorem ev_oldBoth :
    evalExpr (mkSt s r L ts) (or' (eqc "stp" STP_CANCEL_OLD) (eqc "stp" STP_CANCEL_BOTH)) =
      .ok (.bool (decide (r.stpMode = 2 ∨ r.stpMode = 3))) := by
  by_cases h2 : r.stpMode = 2
  · lsimp [h2]
  · by_cases h3 : r.stpMode = 3 <;> lsimp [h2, h3]

theorem ev_innerCond :
    evalExpr (mkSt s r L ts) innerCond = .ok (.bool (L.passive.isSome && decide (0 < L.rem))) := by
  cases hp : L.passive <;> by_cases h : 0 < L.rem <;> (simp only [innerCond]; lsimp [hp, h])

theorem ev_outerCond :
    evalExpr (mkSt s r L ts) outerCond = .ok (.bool (decide (0 < L.rem) && !L.stop)) := by
  cases hs : L.stop <;> by_cases h : 0 < L.rem <;> (simp only [outerCond]; lsimp [hs, h])

theorem ev_bestNull : evalExpr (mkSt s r L ts) (.isNullL (v "best")) = .ok (.bool L.best.isNone) := by
  lsimp

/-- The crossing test of the matcher, on a level price and the request price. -/
def crossB (isBuy : Bool) (bp p : UInt64) : Prop := if isBuy then bp ≤ p else p ≤ bp

instance (isBuy : Bool) (bp p : UInt64) : Decidable (crossB isBuy bp p) := by
  unfold crossB; cases isBuy <;> infer_instance

theorem ev_crossCond (isBuy : Bool) {l : LevelH} {lrow : LevelRow} (hb : L.best = some l)
    (hl : liveL (view s) l = true) (hrl : readLevel s l = some lrow) :
    evalExpr (mkSt s r L ts) (crossCond isBuy) =
      .ok (.bool (decide (r.orderType ≠ 1 ∧ ¬ crossB isBuy lrow.price r.price))) := by
  by_cases hm : r.orderType = 1
  · simp only [crossCond]; lsimp [hm]
  · cases isBuy
    · by_cases hc : r.price ≤ lrow.price <;>
        (simp only [crossCond, crossesE]; lsimp [hm, hb, hl, hrl, hc, crossB])
    · by_cases hc : lrow.price ≤ r.price <;>
        (simp only [crossCond, crossesE]; lsimp [hm, hb, hl, hrl, hc, crossB])

theorem ev_countZero {l : LevelH} (hb : L.best = some l) (hl : liveL (view s) l = true)
    (hn : levelCount s l < 2 ^ 64) :
    evalExpr (mkSt s r L ts) (b2 .eq (.getL (v "best") .count) (u 0)) =
      .ok (.bool (decide (levelCount s l = 0))) := by
  by_cases hz : levelCount s l = 0
  · lsimp [hb, hl, hz, hn]
  · have : ¬ (levelCount s l).toUInt64 = 0 := by
      intro e
      have := congrArg UInt64.toNat e
      rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn] at this
      exact hz this
    lsimp [hb, hl, hz, hn, this]

end Stmts

end MatcherLoop

import Matcher.Lang

/-!
# A program logic for the matcher language

`execStmt` takes a fuel argument that bounds nesting and call depth. For
proofs, fuel is noise: `execStmt_mono` shows a run that succeeds with some
fuel succeeds identically with more, so `Eval P s st r` ("some fuel runs `s`
from `st` to `r`") composes without bookkeeping. The rules below give one
lemma per statement form; a loop is unrolled with `LoopRun`.
-/

namespace Matcher

open EngineDbApi

variable {S : Type} [EngineDb S]

/-- The step function the loop folds with, for a given body semantics `g`. -/
def loopStep (c : Expr) (g : St S → Except Err (St S × Outcome))
    (acc : Except Err (St S × Outcome × Bool)) : Except Err (St S × Outcome × Bool) :=
  match acc with
  | .ok (st', .normal, false) =>
    match evalExpr st' c with
    | .ok (.bool true) =>
      match g st' with
      | .ok (st'', o) => .ok (st'', o, false)
      | .error e => .error e
    | .ok (.bool false) => .ok (st', .normal, true)
    | .ok _ => .error .type
    | .error e => .error e
  | other => other

theorem foldl_loopStep_error (c : Expr) (g : St S → Except Err (St S × Outcome)) (e : Err) :
    ∀ (l : List Nat), l.foldl (fun acc _ => loopStep c g acc) (.error e) = .error e
  | [] => rfl
  | _ :: l => foldl_loopStep_error c g e l

/-- If `g₁` succeeds only where `g₂` gives the same result, a fold that
    succeeds with `g₁` gives the same result with `g₂`. -/
theorem foldl_loopStep_mono (c : Expr) (g₁ g₂ : St S → Except Err (St S × Outcome))
    (hg : ∀ st r, g₁ st = .ok r → g₂ st = .ok r) :
    ∀ (l : List Nat) (acc : Except Err (St S × Outcome × Bool)) x,
      l.foldl (fun acc _ => loopStep c g₁ acc) acc = .ok x →
      l.foldl (fun acc _ => loopStep c g₂ acc) acc = .ok x
  | [], _, _, h => h
  | _ :: l, acc, x, h => by
    simp only [List.foldl] at h ⊢
    have hstep : loopStep c g₁ acc = loopStep c g₂ acc ∨
        ∃ e, loopStep c g₁ acc = .error e := by
      unfold loopStep
      split
      · split
        · rename_i st' _ _
          cases hg1 : g₁ st' with
          | error e => exact Or.inr ⟨e, rfl⟩
          | ok r => rw [hg _ _ hg1]; exact Or.inl rfl
        · exact Or.inl rfl
        · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
    rcases hstep with he | ⟨e, he⟩
    · rw [← he]; exact foldl_loopStep_mono c g₁ g₂ hg l _ x h
    · rw [he, foldl_loopStep_error] at h; cases h

theorem execStmt_loop_eq (P : Program) (f : Nat) (bnd : Bound) (c : Expr) (body : Stmt)
    (st : St S) :
    execStmt P (f + 1) (.loop bnd c body) st =
      (do
        let n ← boundVal (S := S) bnd
        match (List.range n).foldl (fun acc _ => loopStep c (execStmt P f body) acc)
            (.ok (st, .normal, false)) with
        | .error e => .error e
        | .ok (st', .ret v, _) => .ok (st', .ret v)
        | .ok (st', .normal, true) => .ok (st', .normal)
        | .ok (st', .normal, false) =>
          match evalExpr st' c with
          | .ok (.bool false) => .ok (st', .normal)
          | .ok (.bool true) => .error .bound
          | .ok _ => .error .type
          | .error e => .error e) := rfl

theorem exec_seq (P : Program) (f : Nat) (a b : Stmt) (st : St S) :
    execStmt P (f + 1) (.seq a b) st =
      (execStmt P f a st).bind (fun p => match p.2 with
        | .ret v => .ok (p.1, .ret v)
        | .normal => execStmt P f b p.1) := rfl

theorem exec_ite (P : Program) (f : Nat) (c : Expr) (a b : Stmt) (st : St S) :
    execStmt P (f + 1) (.ite c a b) st =
      (evalExpr st c).bind (fun vc => (asBool vc).bind (fun cb =>
        if cb then execStmt P f a st else execStmt P f b st)) := rfl

theorem exec_call (P : Program) (f : Nat) (dst : Option Ident) (fname : Ident)
    (args : List Expr) (st : St S) :
    execStmt P (f + 1) (.call dst fname args) st =
      (lookupFun P fname).bind (fun fd =>
      (args.mapM (evalExpr st)).bind (fun vals =>
      (bindParams fd.params vals).bind (fun penv =>
      (execStmt P f fd.body
          { st with env := penv ++ fd.locals.map fun (x, t) => (x, t.default) }).bind
        (fun p => match p.2 with
          | .normal => .error .noReturn
          | .ret v =>
            if v.ty = fd.ret then
              (bindResult st.env dst (some v)).bind (fun env => .ok ({ p.1 with env := env }, .normal))
            else .error .type)))) := rfl

/-- **Fuel monotonicity**, one step. -/
theorem execStmt_succ (P : Program) :
    ∀ (f : Nat) (s : Stmt) (st : St S) r,
      execStmt P f s st = .ok r → execStmt P (f + 1) s st = .ok r := by
  intro f
  induction f with
  | zero => intro s st r h; simp [execStmt] at h
  | succ f ih =>
    intro s st r h
    cases s with
    | skip => exact h
    | seq a b =>
      rw [exec_seq] at h ⊢
      cases ha : execStmt P f a st with
      | error e => rw [ha] at h; cases h
      | ok p =>
        rw [ha] at h
        rw [ih a st p ha]
        obtain ⟨st1, o⟩ := p
        cases o with
        | ret v => exact h
        | normal => exact ih b st1 r h
    | assign x e => exact h
    | ite c a b =>
      rw [exec_ite] at h ⊢
      cases hc : evalExpr st c with
      | error e => rw [hc] at h; cases h
      | ok vc =>
        rw [hc] at h
        simp only [Except.bind] at h ⊢
        cases hb : asBool vc with
        | error e => rw [hb] at h; cases h
        | ok bb =>
          rw [hb] at h
          simp only at h ⊢
          cases bb
          · exact ih b st r h
          · exact ih a st r h
    | loop bnd c body =>
      rw [execStmt_loop_eq] at h ⊢
      cases hn : boundVal (S := S) bnd with
      | error e => rw [hn] at h; cases h
      | ok n =>
        rw [hn] at h
        simp only [bind, Except.bind] at h ⊢
        cases hfold : (List.range n).foldl
            (fun acc _ => loopStep c (execStmt P f body) acc) (.ok (st, .normal, false)) with
        | error e => rw [hfold] at h; cases h
        | ok x =>
          rw [hfold] at h
          rw [foldl_loopStep_mono c _ _ (ih body) _ _ x hfold]
          exact h
    | ext dst op args => exact h
    | call dst fname args =>
      rw [exec_call] at h ⊢
      cases hf : lookupFun P fname with
      | error e => rw [hf] at h; cases h
      | ok fd =>
        rw [hf] at h
        simp only [Except.bind] at h ⊢
        cases hv : args.mapM (evalExpr st) with
        | error e => rw [hv] at h; cases h
        | ok vals =>
          rw [hv] at h
          simp only at h ⊢
          cases hp : bindParams fd.params vals with
          | error e => rw [hp] at h; cases h
          | ok penv =>
            rw [hp] at h
            simp only at h ⊢
            cases hb : execStmt P f fd.body
                { st with env := penv ++ fd.locals.map fun (x, t) => (x, t.default) } with
            | error e => rw [hb] at h; cases h
            | ok p =>
              rw [hb] at h
              rw [ih _ _ p hb]
              exact h
    | emit m t p q => exact h
    | ret e => exact h

theorem execStmt_mono (P : Program) {f f' : Nat} {s : Stmt} {st : St S} {r}
    (h : execStmt P f s st = .ok r) (hle : f ≤ f') : execStmt P f' s st = .ok r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact execStmt_succ P _ s st r ih

-- ============================================================================
-- Eval: a run with some fuel
-- ============================================================================

/-- Some fuel runs `s` from `st` to `r`. By `execStmt_mono`, every larger fuel
    does too, and `Eval` is deterministic. -/
def Eval (P : Program) (s : Stmt) (st : St S) (r : St S × Outcome) : Prop :=
  ∃ f, execStmt P f s st = .ok r

theorem Eval.det {P : Program} {s : Stmt} {st : St S} {r₁ r₂}
    (h₁ : Eval P s st r₁) (h₂ : Eval P s st r₂) : r₁ = r₂ := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  have := execStmt_mono P h₁ (Nat.le_max_left f₁ f₂)
  rw [execStmt_mono P h₂ (Nat.le_max_right f₁ f₂)] at this
  cases this; rfl

theorem Eval.skip (P : Program) (st : St S) : Eval P .skip st (st, .normal) := ⟨1, rfl⟩

theorem Eval.seq_normal {P : Program} {a b : Stmt} {st st₁ : St S} {r}
    (ha : Eval P a st (st₁, .normal)) (hb : Eval P b st₁ r) : Eval P (.seq a b) st r := by
  obtain ⟨f₁, h₁⟩ := ha
  obtain ⟨f₂, h₂⟩ := hb
  refine ⟨max f₁ f₂ + 1, ?_⟩
  rw [exec_seq, execStmt_mono P h₁ (Nat.le_max_left f₁ f₂)]
  exact execStmt_mono P h₂ (Nat.le_max_right f₁ f₂)

theorem Eval.seq_ret {P : Program} {a b : Stmt} {st st₁ : St S} {v : Val}
    (ha : Eval P a st (st₁, .ret v)) : Eval P (.seq a b) st (st₁, .ret v) := by
  obtain ⟨f₁, h₁⟩ := ha
  refine ⟨f₁ + 1, ?_⟩
  rw [exec_seq, h₁]; rfl

theorem Eval.assign {P : Program} {x : Ident} {e : Expr} {st : St S} {v : Val} {env}
    (he : evalExpr st e = .ok v) (hs : setVar st.env x v = .ok env) :
    Eval P (.assign x e) st ({ st with env := env }, .normal) :=
  ⟨1, by simp only [execStmt, he, hs, bind, Except.bind]⟩

theorem Eval.ite_true {P : Program} {c : Expr} {a b : Stmt} {st : St S} {r}
    (hc : evalExpr st c = .ok (.bool true)) (ha : Eval P a st r) : Eval P (.ite c a b) st r := by
  obtain ⟨f, h⟩ := ha
  exact ⟨f + 1, by rw [exec_ite, hc]; exact h⟩

theorem Eval.ite_false {P : Program} {c : Expr} {a b : Stmt} {st : St S} {r}
    (hc : evalExpr st c = .ok (.bool false)) (hb : Eval P b st r) : Eval P (.ite c a b) st r := by
  obtain ⟨f, h⟩ := hb
  exact ⟨f + 1, by rw [exec_ite, hc]; exact h⟩

theorem Eval.ret {P : Program} {e : Expr} {st : St S} {v : Val}
    (he : evalExpr st e = .ok v) : Eval P (.ret e) st (st, .ret v) :=
  ⟨1, by simp only [execStmt, he, bind, Except.bind]⟩

theorem Eval.ext {P : Program} {dst : Option Ident} {op : Ext} {args : List Expr}
    {st : St S} {vals : List Val} {s' : S} {res : Option Val} {env}
    (hv : args.mapM (evalExpr st) = .ok vals) (hr : runExt st op vals = .ok (s', res))
    (hb : bindResult st.env dst res = .ok env) :
    Eval P (.ext dst op args) st ({ st with store := s', env := env }, .normal) :=
  ⟨1, by simp only [execStmt, hv, hr, hb, bind, Except.bind]⟩

theorem Eval.emit {P : Program} {m t p q : Expr} {st : St S} {vm vt vp vq : UInt64} {cap : Nat}
    (hm : evalExpr st m = .ok (.u64 vm)) (ht : evalExpr st t = .ok (.u64 vt))
    (hp : evalExpr st p = .ok (.u64 vp)) (hq : evalExpr st q = .ok (.u64 vq))
    (hcap : boundVal (S := S) P.tradeCap = .ok cap) (hlen : st.trades.length < cap) :
    Eval P (.emit m t p q) st
      ({ st with trades := st.trades ++ [toNatTrade vm vt vp vq] }, .normal) :=
  ⟨1, by simp only [execStmt, hm, ht, hp, hq, asU64, hcap, hlen, bind, Except.bind, if_true]⟩

theorem Eval.call {P : Program} {dst : Option Ident} {fname : Ident} {args : List Expr}
    {st : St S} {fd : FunDef} {vals : List Val} {penv : List (Ident × Val)} {st₁ : St S}
    {v : Val} {env}
    (hf : lookupFun P fname = .ok fd) (hv : args.mapM (evalExpr st) = .ok vals)
    (hp : bindParams fd.params vals = .ok penv)
    (hbody : Eval P fd.body
      { st with env := penv ++ fd.locals.map fun (x, t) => (x, t.default) } (st₁, .ret v))
    (hty : v.ty = fd.ret) (hb : bindResult st.env dst (some v) = .ok env) :
    Eval P (.call dst fname args) st ({ st₁ with env := env }, .normal) := by
  obtain ⟨f, h⟩ := hbody
  exact ⟨f + 1, by rw [exec_call, hf]; simp only [Except.bind, hv, hp, h, hty, hb, if_true]⟩

theorem Eval.block_cons_normal {P : Program} {a : Stmt} {rest : List Stmt} {st st₁ : St S} {r}
    (ha : Eval P a st (st₁, .normal)) (hr : Eval P (Stmt.block rest) st₁ r) (hne : rest ≠ []) :
    Eval P (Stmt.block (a :: rest)) st r := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons b bs => exact Eval.seq_normal ha hr

theorem Eval.block_cons_ret {P : Program} {a : Stmt} {rest : List Stmt} {st st₁ : St S} {v : Val}
    (ha : Eval P a st (st₁, .ret v)) : Eval P (Stmt.block (a :: rest)) st (st₁, .ret v) := by
  cases rest with
  | nil => exact ha
  | cons b bs => exact Eval.seq_ret ha

-- ============================================================================
-- Loops
-- ============================================================================

/-- Running a loop body up to `k` more times from `st`, ending in `r`. -/
inductive LoopRun (P : Program) (c : Expr) (body : Stmt) : Nat → St S → St S × Outcome → Prop
  /-- The condition is false: the loop ends. -/
  | stop {k : Nat} {st : St S} :
      evalExpr st c = .ok (.bool false) → LoopRun P c body k st (st, .normal)
  /-- The condition holds, the body completes, and the loop continues. -/
  | step {k : Nat} {st st₁ : St S} {r} :
      evalExpr st c = .ok (.bool true) → Eval P body st (st₁, .normal) →
      LoopRun P c body k st₁ r → LoopRun P c body (k + 1) st r
  /-- The condition holds and the body returns. -/
  | ret {k : Nat} {st st₁ : St S} {v : Val} :
      evalExpr st c = .ok (.bool true) → Eval P body st (st₁, .ret v) →
      LoopRun P c body (k + 1) st (st₁, .ret v)

/-- What the loop does after its fold. -/
def loopFinish (c : Expr) : Except Err (St S × Outcome × Bool) → Except Err (St S × Outcome)
  | .error e => .error e
  | .ok (st', .ret v, _) => .ok (st', .ret v)
  | .ok (st', .normal, true) => .ok (st', .normal)
  | .ok (st', .normal, false) =>
    match evalExpr st' c with
    | .ok (.bool false) => .ok (st', .normal)
    | .ok (.bool true) => .error .bound
    | .ok _ => .error .type
    | .error e => .error e

theorem execStmt_loop_finish (P : Program) (f : Nat) (bnd : Bound) (c : Expr) (body : Stmt)
    (st : St S) :
    execStmt P (f + 1) (.loop bnd c body) st =
      (boundVal (S := S) bnd).bind (fun n => loopFinish c
        ((List.range n).foldl (fun acc _ => loopStep c (execStmt P f body) acc)
          (.ok (st, .normal, false)))) := by
  rw [execStmt_loop_eq]
  cases boundVal (S := S) bnd with
  | error e => rfl
  | ok n =>
    simp only [bind, Except.bind]
    unfold loopFinish
    rfl

theorem foldl_loopStep_done (c : Expr) (g : St S → Except Err (St S × Outcome))
    (x : St S) (o : Outcome) : ∀ (l : List Nat),
    l.foldl (fun acc _ => loopStep c g acc) (.ok (x, o, true)) = .ok (x, o, true)
  | [] => rfl
  | _ :: l => by
    simp only [List.foldl]
    have : loopStep c g (.ok (x, o, true)) = .ok (x, o, true) := by
      unfold loopStep; cases o <;> rfl
    rw [this]; exact foldl_loopStep_done c g x o l

theorem foldl_loopStep_ret (c : Expr) (g : St S → Except Err (St S × Outcome))
    (x : St S) (v : Val) (b : Bool) : ∀ (l : List Nat),
    l.foldl (fun acc _ => loopStep c g acc) (.ok (x, .ret v, b)) = .ok (x, .ret v, b)
  | [] => rfl
  | _ :: l => by
    simp only [List.foldl]
    have : loopStep c g (.ok (x, .ret v, b)) = .ok (x, .ret v, b) := by
      unfold loopStep; rfl
    rw [this]; exact foldl_loopStep_ret c g x v b l

theorem loopRun_core {P : Program} {c : Expr} {body : Stmt} :
    ∀ {k : Nat} {st : St S} {r}, LoopRun P c body k st r →
      ∃ f, ∀ f', f ≤ f' → ∀ l : List Nat, l.length = k →
        loopFinish c (l.foldl (fun acc _ => loopStep c (execStmt P f' body) acc)
          (.ok (st, .normal, false))) = .ok r := by
  intro k st r h
  induction h with
  | @stop k st₀ hc =>
    refine ⟨0, fun f' _ l _ => ?_⟩
    cases l with
    | nil => simp only [List.foldl, loopFinish, hc]
    | cons a l' =>
      simp only [List.foldl]
      have : loopStep c (execStmt P f' body) (.ok (st₀, .normal, false)) = .ok (st₀, .normal, true) := by
        simp only [loopStep, hc]
      rw [this, foldl_loopStep_done]; rfl
  | @step k st₀ st₁ r₀ hc hb _ ih =>
    obtain ⟨fb, hfb⟩ := hb
    obtain ⟨fi, hfi⟩ := ih
    refine ⟨max fb fi, fun f' hf' l hl => ?_⟩
    cases l with
    | nil => cases hl
    | cons a l' =>
      simp only [List.foldl]
      have e := execStmt_mono P hfb (Nat.le_trans (Nat.le_max_left fb fi) hf')
      have : loopStep c (execStmt P f' body) (.ok (st₀, .normal, false)) = .ok (st₁, .normal, false) := by
        simp only [loopStep, hc, e]
      rw [this]
      exact hfi f' (Nat.le_trans (Nat.le_max_right fb fi) hf') l' (by simpa using hl)
  | @ret k st₀ st₁ v hc hb =>
    obtain ⟨fb, hfb⟩ := hb
    refine ⟨fb, fun f' hf' l hl => ?_⟩
    cases l with
    | nil => cases hl
    | cons a l' =>
      simp only [List.foldl]
      have e := execStmt_mono P hfb hf'
      have : loopStep c (execStmt P f' body) (.ok (st₀, .normal, false)) = .ok (st₁, .ret v, false) := by
        simp only [loopStep, hc, e]
      rw [this, foldl_loopStep_ret]; rfl

/-- **The loop rule.** A loop whose bound evaluates to `n` and whose body runs
    as `LoopRun` with budget `n` runs to the same result. -/
theorem Eval.loop {P : Program} {bnd : Bound} {c : Expr} {body : Stmt} {st : St S} {n : Nat} {r}
    (hn : boundVal (S := S) bnd = .ok n) (h : LoopRun P c body n st r) :
    Eval P (.loop bnd c body) st r := by
  obtain ⟨f, hf⟩ := loopRun_core h
  refine ⟨f + 1, ?_⟩
  rw [execStmt_loop_finish, hn]
  exact hf f (Nat.le_refl f) (List.range n) List.length_range

/-- More budget never hurts a loop run. -/
theorem LoopRun.mono {P : Program} {c : Expr} {body : Stmt} :
    ∀ {k : Nat} {st : St S} {r}, LoopRun P c body k st r → ∀ {k'}, k ≤ k' →
      LoopRun P c body k' st r := by
  intro k st r h
  induction h with
  | stop hc => intro k' _; exact .stop hc
  | step hc hb _ ih =>
    intro k' hk
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    exact .step hc hb (ih (by omega))
  | ret hc hb =>
    intro k' hk
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    exact .ret hc hb

/-- An entry run: from `Eval` of the entry body to `runEntry`. -/
theorem runEntry_of_eval {P : Program} {fname : Ident} {args : List Val} {s : S}
    {fd : FunDef} {penv : List (Ident × Val)} {st₁ : St S} {v : Val}
    (hf : lookupFun P fname = .ok fd) (hp : bindParams fd.params args = .ok penv)
    (hb : Eval P fd.body
      { store := s, env := penv ++ fd.locals.map fun (x, t) => (x, t.default), trades := [] }
      (st₁, .ret v))
    (hty : v.ty = fd.ret) :
    ∃ f, runEntry P f fname args s = .ok (v, st₁.store, st₁.trades) := by
  obtain ⟨f, h⟩ := hb
  exact ⟨f, by simp only [runEntry, hf, hp, h, hty, bind, Except.bind, if_true]⟩

-- ============================================================================
-- Extern operations: one lemma each, given the checked precondition
-- ============================================================================

section Ext

variable {st : St S}

theorem liveOrder_some {h : OrderH} (hl : liveO (viewOf st) h = true) :
    liveOrder st (.order (some h)) = .ok h := by simp [liveOrder, hl]

theorem liveLevel_some {l : LevelH} (hl : liveL (viewOf st) l = true) :
    liveLevel st (.level (some l)) = .ok l := by simp [liveLevel, hl]

theorem runExt_hashFind (id : UInt64) :
    runExt st .hashFind [.u64 id] = .ok (st.store, some (.order (EngineDb.hashFind st.store id))) := by
  simp [runExt, asU64, bind, Except.bind]

theorem runExt_owner {h : OrderH} (hl : liveO (viewOf st) h = true) :
    runExt st .owner [.order (some h)] = .ok (st.store, some (.level (EngineDb.owner st.store h))) := by
  simp [runExt, liveOrder_some hl, bind, Except.bind]

theorem runExt_qFirst {l : LevelH} (hl : liveL (viewOf st) l = true) :
    runExt st .qFirst [.level (some l)] = .ok (st.store, some (.order (EngineDb.qFirst st.store l))) := by
  simp [runExt, liveLevel_some hl, bind, Except.bind]

theorem runExt_qNext {h : OrderH} (hl : liveO (viewOf st) h = true)
    (hq : queuedB (viewOf st) h = true) :
    runExt st .qNext [.order (some h)] = .ok (st.store, some (.order (EngineDb.qNext st.store h))) := by
  simp [runExt, liveOrder_some hl, hq, bind, Except.bind]

theorem runExt_tBest (t : Tree) :
    runExt st (.tBest t) [] = .ok (st.store, some (.level (EngineDb.tBest st.store t))) := rfl

theorem runExt_tFind (t : Tree) (p : UInt64) :
    runExt st (.tFind t) [.u64 p] = .ok (st.store, some (.level (EngineDb.tFind st.store t p))) := by
  simp [runExt, asU64, bind, Except.bind]

theorem runExt_qRemove {l : LevelH} {h : OrderH} (hl : liveL (viewOf st) l = true)
    (hh : liveO (viewOf st) h = true) (hq : ((viewOf st).queue l).contains h = true) :
    runExt st .qRemove [.level (some l), .order (some h)] =
      .ok (EngineDb.qRemove st.store l h, none) := by
  have hm : h ∈ (viewOf st).queue l := List.contains_iff_mem.mp hq
  simp [runExt, liveLevel_some hl, liveOrder_some hh, hm, bind, Except.bind]

theorem runExt_hashRemove {h : OrderH} (hh : liveO (viewOf st) h = true)
    (hin : inHashB (viewOf st) h = true) :
    runExt st .hashRemove [.order (some h)] = .ok (EngineDb.hashRemove st.store h, none) := by
  simp [runExt, liveOrder_some hh, hin, bind, Except.bind]

theorem runExt_orderFree {h : OrderH} (hh : liveO (viewOf st) h = true)
    (hq : queuedB (viewOf st) h = false) (hin : inHashB (viewOf st) h = false) :
    runExt st .orderFree [.order (some h)] = .ok (EngineDb.orderFree st.store h, none) := by
  simp [runExt, liveOrder_some hh, hq, hin, bind, Except.bind]

theorem runExt_tRemove {t : Tree} {l : LevelH} (hl : liveL (viewOf st) l = true)
    (hin : inTreeB (viewOf st) t l = true) :
    runExt st (.tRemove t) [.level (some l)] = .ok (EngineDb.tRemove st.store t l, none) := by
  simp [runExt, liveLevel_some hl, hin, bind, Except.bind]

theorem runExt_levelFree {l : LevelH} (hl : liveL (viewOf st) l = true)
    (hin : inAnyTreeB (viewOf st) l = false) (he : ((viewOf st).queue l).isEmpty = true) :
    runExt st .levelFree [.level (some l)] = .ok (EngineDb.levelFree st.store l, none) := by
  simp [runExt, liveLevel_some hl, hin, he, bind, Except.bind]

theorem runExt_orderAlloc :
    runExt st .orderAlloc [] =
      .ok ((EngineDb.orderAlloc st.store).2, some (.order (EngineDb.orderAlloc st.store).1)) := rfl

theorem runExt_levelAlloc :
    runExt st .levelAlloc [] =
      .ok ((EngineDb.levelAlloc st.store).2, some (.level (EngineDb.levelAlloc st.store).1)) := rfl

theorem runExt_qInsertTail {l : LevelH} {h : OrderH} (hl : liveL (viewOf st) l = true)
    (hh : liveO (viewOf st) h = true) (hq : queuedB (viewOf st) h = false) :
    runExt st .qInsertTail [.level (some l), .order (some h)] =
      .ok (EngineDb.qInsertTail st.store l h, none) := by
  simp [runExt, liveLevel_some hl, liveOrder_some hh, hq, bind, Except.bind]

theorem runExt_hashInsert {h : OrderH} (hh : liveO (viewOf st) h = true)
    (hin : inHashB (viewOf st) h = false) :
    runExt st .hashInsert [.order (some h)] =
      .ok ((EngineDb.hashInsert st.store h).2, some (.bool (EngineDb.hashInsert st.store h).1)) := by
  simp [runExt, liveOrder_some hh, hin, bind, Except.bind]

theorem runExt_tInsert {t : Tree} {l : LevelH} (hl : liveL (viewOf st) l = true)
    (hin : inAnyTreeB (viewOf st) l = false) (hp : priceFreshB (viewOf st) t l = true) :
    runExt st (.tInsert t) [.level (some l)] = .ok (EngineDb.tInsert st.store t l, none) := by
  simp [runExt, liveLevel_some hl, hin, hp, bind, Except.bind]

theorem runExt_setL_price {l : LevelH} {row : LevelRow} (p : UInt64)
    (hl : liveL (viewOf st) l = true) (hr : EngineDb.readLevel st.store l = some row)
    (hin : inAnyTreeB (viewOf st) l = false) :
    runExt st (.setL .price) [.level (some l), .u64 p] =
      .ok (EngineDb.writeLevel st.store l { row with price := p }, none) := by
  simp [runExt, liveLevel_some hl, asU64, hr, hin, bind, Except.bind]

theorem runExt_setO {f : OField} {h : OrderH} {row row' : OrderRow} {vv : Val}
    (hh : liveO (viewOf st) h = true) (hr : EngineDb.readOrder st.store h = some row)
    (hkey : (f = .id && inHashB (viewOf st) h) = false) (hset : setOField row f vv = .ok row') :
    runExt st (.setO f) [.order (some h), vv] = .ok (EngineDb.writeOrder st.store h row', none) := by
  simp [runExt, liveOrder_some hh, hr, hkey, hset, bind, Except.bind]

end Ext

end Matcher

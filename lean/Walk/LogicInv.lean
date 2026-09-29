import Matcher.Logic

/-!
# A3 infrastructure: inversion rules for the program logic

`main`'s `Logic.lean` gives one rule per statement form for runs that
succeed. To state that the program traps exactly where the walk does
(`none`), A3 needs the converse direction for three forms: a successful loop
is a `LoopRun` of its budget (so a loop whose test still holds when the
budget is spent has no successful run); a successful `seq` runs its first
statement; a successful `emit` had room in the trade buffer.

Counted as infrastructure in A4: facts about the language, not about the
matcher or the spec.
-/

namespace Matcher

open EngineDbApi

variable {S : Type} [EngineDb S]

theorem loopStep_cases (c : Expr) (g : St S → Except Err (St S × Outcome)) (st : St S) :
    (∃ e, loopStep c g (.ok (st, .normal, false)) = .error e) ∨
    (evalExpr st c = .ok (.bool false) ∧ loopStep c g (.ok (st, .normal, false)) = .ok (st, .normal, true)) ∨
    (∃ st₁ o, evalExpr st c = .ok (.bool true) ∧ g st = .ok (st₁, o) ∧
      loopStep c g (.ok (st, .normal, false)) = .ok (st₁, o, false)) := by
  simp only [loopStep]
  split
  · rename_i hc
    split
    · rename_i st₁ o hb; exact Or.inr (Or.inr ⟨st₁, o, hc, hb, rfl⟩)
    · exact Or.inl ⟨_, rfl⟩
  · rename_i hc; exact Or.inr (Or.inl ⟨hc, rfl⟩)
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

theorem loopRun_of_fold {P : Program} {c : Expr} {body : Stmt} {f : Nat} {r : St S × Outcome} :
    ∀ (l : List Nat) (st : St S),
      loopFinish c (l.foldl (fun acc _ => loopStep c (execStmt P f body) acc)
        (.ok (st, .normal, false))) = .ok r →
      LoopRun P c body l.length st r
  | [], st, h => by
    simp only [List.foldl, loopFinish] at h
    split at h
    · rename_i hc; cases h; exact .stop hc
    all_goals cases h
  | _ :: l, st, h => by
    simp only [List.foldl] at h
    rcases loopStep_cases c (execStmt P f body) st with ⟨e, he⟩ | ⟨hc, he⟩ | ⟨st₁, o, hc, hb, he⟩
    · rw [he, foldl_loopStep_error] at h; cases h
    · rw [he, foldl_loopStep_done] at h
      simp only [loopFinish] at h
      cases h
      exact .stop hc
    · rw [he] at h
      cases o with
      | normal => exact .step hc ⟨f, hb⟩ (loopRun_of_fold l st₁ h)
      | ret v =>
        rw [foldl_loopStep_ret] at h
        simp only [loopFinish] at h
        cases h
        exact .ret hc ⟨f, hb⟩

/-- **A successful loop is a `LoopRun` of its budget.** -/
theorem loopRun_of_eval {P : Program} {bnd : Bound} {c : Expr} {body : Stmt} {st : St S}
    {n : Nat} {r : St S × Outcome} (hn : boundVal (S := S) bnd = .ok n)
    (h : Eval P (.loop bnd c body) st r) : LoopRun P c body n st r := by
  obtain ⟨f, hf⟩ := h
  cases f with
  | zero => simp [execStmt] at hf
  | succ f =>
    rw [execStmt_loop_finish, hn] at hf
    have := loopRun_of_fold (List.range n) st hf
    simpa using this

theorem Eval.seq_inv {P : Program} {a b : Stmt} {st : St S} {r : St S × Outcome}
    (h : Eval P (.seq a b) st r) :
    (∃ st₁, Eval P a st (st₁, .normal) ∧ Eval P b st₁ r) ∨ (∃ v, Eval P a st (r.1, .ret v) ∧ r.2 = .ret v) := by
  obtain ⟨f, hf⟩ := h
  cases f with
  | zero => simp [execStmt] at hf
  | succ f =>
    rw [exec_seq] at hf
    cases ha : execStmt P f a st with
    | error e => rw [ha] at hf; cases hf
    | ok p =>
      rw [ha] at hf
      obtain ⟨st₁, o⟩ := p
      cases o with
      | normal => exact Or.inl ⟨st₁, ⟨f, ha⟩, ⟨f, hf⟩⟩
      | ret v => cases hf; exact Or.inr ⟨v, ⟨f, ha⟩, rfl⟩

theorem Eval.ite_inv {P : Program} {c : Expr} {a b : Stmt} {st : St S} {r : St S × Outcome}
    (h : Eval P (.ite c a b) st r) :
    (evalExpr st c = .ok (.bool true) ∧ Eval P a st r) ∨
      (evalExpr st c = .ok (.bool false) ∧ Eval P b st r) := by
  obtain ⟨f, hf⟩ := h
  cases f with
  | zero => simp [execStmt] at hf
  | succ f =>
    rw [exec_ite] at hf
    cases hc : evalExpr st c with
    | error e => rw [hc] at hf; cases hf
    | ok vc =>
      rw [hc] at hf
      cases vc with
      | bool bb =>
        cases bb
        · exact Or.inr ⟨rfl, ⟨f, hf⟩⟩
        · exact Or.inl ⟨rfl, ⟨f, hf⟩⟩
      | _ => cases hf

/-- A successful `emit` had room in the trade buffer. -/
theorem Eval.emit_inv {P : Program} {m t p q : Expr} {st : St S} {r : St S × Outcome}
    (h : Eval P (.emit m t p q) st r) :
    ∃ cap, boundVal (S := S) P.tradeCap = .ok cap ∧ st.trades.length < cap := by
  obtain ⟨f, hf⟩ := h
  cases f with
  | zero => simp [execStmt] at hf
  | succ f =>
    simp only [execStmt, bind, Except.bind] at hf
    split at hf
    · cases hf
    · split at hf
      · cases hf
      · split at hf
        · cases hf
        · split at hf
          · cases hf
          · split at hf
            · cases hf
            · split at hf
              · cases hf
              · split at hf
                · cases hf
                · split at hf
                  · cases hf
                  · split at hf
                    · cases hf
                    · rename_i cap hcap
                      split at hf
                      · rename_i hlen; exact ⟨cap, hcap, hlen⟩
                      · cases hf

end Matcher

import Amcc.Interface
import Amcc.Schema
import Amcc.Dmmeta
import Amcc.Spec.Algebra
import Amcc.CSubset.Syntax
import Amcc.CSubset.Value
import Amcc.CSubset.Eval
import Amcc.CSubset.Calls
import Amcc.Templates.Pool
import Amcc.Templates.Llist
import Amcc.Templates.Thash
import Amcc.Templates.ThashRefine
import Amcc.Templates.MiniDb
import Bridge.MatchingEngineBridge
import Bridge.RelationalMemory
import Bridge.OrderExecution

/-!
# Forward Simulation Bridge: C AST Operational Semantics to Abstract Book Transitions

This module formalizes the forward simulation relation between:
1. Concrete C Operational Semantics (`execStmt`, `Mem`, `Store`) executing generated AMCC C ASTs (`genC d`)
2. Abstract Limit Order Book State Transitions (`abstract_insert`, `abstract_match_step`)

## Current Progress & Status
- **`Llist` Refinement**: Completed in AMCC (`Llist.TailListInv`, `insert_success`, FIFO stepping).
- **`Pool` / `Inlary` Refinement**: Completed in AMCC (`Pool.PoolInv`, `alloc_correct`, `RowFresh`).
- **`Thash` Refinement**: Completed in AMCC (`Thash.RepInv`, `lookup_soundness`, `insert_success`, `keys_unique`).
- **Multi-Template Generator**: Completed in AMCC (`MiniDb.genC` synthesizing 3-reftype programs).
- **`MiniDb` Forward Simulation**: Discharged with 0 sorry (`mini_insert_forward_sim_of_gen`).
- **Remaining Bridge Obligations**: Integrating the price level binary search tree (`Atree`) and multi-table footprint framing.
-/

namespace VerifiedCMatchingEngine

open Interface
open Amcc.Spec
open CSubset

/-- Simulation Relation: A concrete C memory state `m` simulates an abstract `BookState`
    if `alpha_concrete` decodes `m` to `book` and satisfies well-formed memory invariants. -/
def SimRel (m : Mem) (bids_root asks_root : Option Path) (book : BookState) : Prop :=
  alpha_concrete m bids_root asks_root = some book ∧
  AmccMemoryContract m bids_root asks_root book

/-- C statement representing order insertion into the matching engine database -/
def insertStmt (req : OrderRequest) : Stmt :=
  Stmt.call none "EngineDb_insert" [
    Expr.lit (Lit.u64 req.id),
    Expr.lit (Lit.u64 req.account),
    Expr.lit (Lit.u64 req.price),
    Expr.lit (Lit.u64 req.qty),
    Expr.lit (Lit.u8 (if req.side == Side.buy then 0 else 1))
  ]

/-- C statement representing matching execution against a passive order -/
def matchStmt (req : OrderRequest) (passive : Order) : Stmt :=
  Stmt.call none "EngineDb_match_step" [
    Expr.lit (Lit.u64 req.id),
    Expr.lit (Lit.u64 passive.id)
  ]

/-- Under `DbRepInv3`, the MiniDb queue decodes: `absDb3` succeeds once the
    decode fuel covers the queue length. -/
theorem mini_queue_absDb3_decodes
    (cap nb fuel : Nat) (m : Mem)
    {free_rest live_qs queue_es : List Path} {chains : List (List Path)}
    (I : Templates.MiniDb.DbRepInv3 m cap nb (nb - 1) free_rest live_qs queue_es chains)
    (hfuel : fuel ≥ queue_es.length + 1) :
    ∃ q, Templates.MiniDb.absDb3 m fuel = some q := by
  open Templates Templates.MiniDb in
  have h_abs_m : absDb3 m fuel = queue_es.mapM (readOrder3 m) := by
    simp only [absDb3]
    have hlen_le : queue_es.length ≤ fuel - 1 := by omega
    have hreach := Llist.reaches_headOf_implies_elems m queueNm queue_es I.queue.chain
      (fuel - 1) hlen_le
    have hfuel_sub : fuel - 1 + 1 = fuel := by omega
    rw [hfuel_sub] at hreach
    have hhd_eq := Llist.head_eq_headOf m queueNm queue_es I.queue.head
    rw [← hhd_eq] at hreach
    rw [hreach]
    rfl
  open Templates Templates.MiniDb in
  obtain ⟨ords, hords⟩ : ∃ ords, queue_es.mapM (readOrder3 m) = some ords :=
    mapM_isSome_iff_exists (readOrder3 m) queue_es I.orders
  exact ⟨ords, by rw [h_abs_m, hords]⟩

/-- **MiniDb queue insertion forward simulation.**

    Scope: this is AMCC's three-reftype MiniDb (Pool + Llist + Thash) holding
    `(UInt32 × UInt64)` pairs, not the matching engine's `Order`/`BookState`
    insertion. It re-exports `Templates.MiniDb.mini_insert_forward_sim3_of_gen`:
    running the C insertion AST generated from `miniDb3` preserves `DbRepInv3`,
    and the decoded queue `q` becomes `q ++ [v]`. The pre-state is shown to
    decode (`mini_queue_absDb3_decodes`), so the refinement cannot hold
    vacuously through a failed decode.

    (The composite `insert_forward_sim` it was meant to feed is retired; see below.)
    Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`. -/
theorem mini_queue_insert_forward_sim
    (cap nb fuel : Nat) (m : Mem) (v : UInt32 × UInt64)
    {free_rest live_qs queue_es : List Path}
    {chains : List (List Path)}
    {p : Program} (hp : Templates.MiniDb.genC (Templates.MiniDb.miniDb3 cap nb) = some p)
    (I : Templates.MiniDb.DbRepInv3 m cap nb (nb - 1) free_rest live_qs queue_es chains)
    (hfree : free_rest ≠ [])
    (h_fresh : ∀ q', (v.1, q') ∉ Templates.Thash.elems m "id" chains)
    (hb : (v.1 &&& UInt32.ofNat (nb - 1)).toNat < nb)
    (hfits : (chains[(v.1 &&& UInt32.ofNat (nb - 1)).toNat]'(by rw [I.thash.nb_len]; exact hb)).length < cap)
    (hfuel : fuel ≥ queue_es.length + cap + 5) :
    ∃ q m' free' live' es' chains',
      Templates.MiniDb.absDb3 m fuel = some q
      ∧ execStmt p fuel (Templates.MiniDb.insertStmt3 v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
      ∧ Templates.MiniDb.DbRepInv3 m' cap nb (nb - 1) free' live' es' chains'
      ∧ Templates.MiniDb.absDb3 m' fuel = some (q ++ [v]) := by
  obtain ⟨q, hq⟩ := mini_queue_absDb3_decodes cap nb fuel m I (by omega)
  obtain ⟨m', free', live', es', chains', hexec, I', habs⟩ :=
    Templates.MiniDb.mini_insert_forward_sim3_of_gen cap nb fuel m v hp I hfree h_fresh hb hfits hfuel
  rw [hq, Option.getD_some] at habs
  exact ⟨q, m', free', live', es', chains', hq, hexec, I', habs⟩

#print axioms mini_queue_absDb3_decodes
#print axioms mini_queue_insert_forward_sim

-- Retired (plan v2 §4): `insert_forward_sim` and `match_step_forward_sim`, which
-- were `sorry`, are replaced by `MatcherAccept.matcher_refines` and
-- `MatcherRun.matcher_run_refines` (lean/Matcher). See git history before Phase 5.


end VerifiedCMatchingEngine

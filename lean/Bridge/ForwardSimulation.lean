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

/-- **Provably Discharged Single-Queue C Insertion Forward Simulation**:
    Directly bridges AMCC's multi-template C code generator (Pool + Llist + Thash)
    to concrete C statement execution under `execStmt`, proving that executing
    the synthesized C insertion AST preserves low-level representation invariants `DbRepInv3`
    and refines the decoded FIFO order queue `absDb3` with zero axioms and 0 sorry. -/
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
    ∃ m' free' live' es' chains',
      execStmt p fuel (Templates.MiniDb.insertStmt3 v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
      ∧ Templates.MiniDb.DbRepInv3 m' cap nb (nb - 1) free' live' es' chains'
      ∧ Templates.MiniDb.absDb3 m' fuel = some ((Templates.MiniDb.absDb3 m fuel).getD [] ++ [v]) := by
  exact Templates.MiniDb.mini_insert_forward_sim3_of_gen cap nb fuel m v hp I hfree h_fresh hb hfits hfuel

#print axioms mini_queue_insert_forward_sim

/-- Master Forward Simulation Theorem for Order Insertion:
    Executing the generated C matching engine insertion pipeline on a well-formed memory state `m`
    under call/loop budget `fuel` produces a deterministic post-state `st'` whose persisted memory `st'.toMem`
    satisfies `WfMem` and decodes via `alpha_concrete` to `abstract_insert emptyBook req.toOrder`.

    NOTE: Blocked on composite Atree level tree synthesis and multi-table footprint framing.
    Marked with an honest `sorry` documenting the compiler simulation obligations. -/
theorem insert_forward_sim
    (d : Dmmeta.Db) (p : Program) (hp : Templates.MiniDb.genC d = some p)
    (m : Mem) (req : OrderRequest) (fuel : Nat)
    (bids_root asks_root : Option Path)
    (h_empty : alpha_concrete m bids_root asks_root = some emptyBook)
    (h_wf : WfMem m bids_root asks_root)
    (h_wf_req : WfOrder req)
    (h_fuel : fuel ≥ execFuelBound emptyBook req.side) :
    ∃ (st' : Store),
      execStmt p fuel (insertStmt req) (m.toStore ∅) = .ok (st', Outcome.normal) ∧
      WfMem st'.toMem bids_root asks_root ∧
      alpha_concrete st'.toMem bids_root asks_root = some (abstract_insert emptyBook req.toOrder) := by
  sorry

/-- Forward Simulation for Match Step Execution:
    Executing the generated C match step on a well-formed memory state `m`
    produces a new memory state `st'.toMem` that preserves `SimRel` with
    `abstract_match_step book req.toOrder passive req.stp_mode`. -/
theorem match_step_forward_sim
    (d : Dmmeta.Db) (p : Program) (hp : Templates.MiniDb.genC d = some p)
    (m : Mem) (req : OrderRequest) (passive : Order) (fuel : Nat)
    (bids_root asks_root : Option Path)
    (book : BookState)
    (h_sim : SimRel m bids_root asks_root book)
    (h_wf_req : WfOrder req)
    (h_fuel : fuel ≥ execFuelBound book req.side) :
    ∃ (st' : Store),
      execStmt p fuel (matchStmt req passive) (m.toStore ∅) = .ok (st', Outcome.normal) ∧
      SimRel st'.toMem bids_root asks_root (abstract_match_step book req.toOrder passive req.stp_mode) := by
  sorry

#print axioms insert_forward_sim
#print axioms match_step_forward_sim

end VerifiedCMatchingEngine

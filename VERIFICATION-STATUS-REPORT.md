# Verification Status and Audit Analysis Report

**Repository**: `unified-verified-matching-engine`  
**Date**: September 2026  
**Author**: Ara Aslyan (`ara.aslyan@gmail.com`)  

---

## 1. Executive Summary

This report documents the findings from the comprehensive verification audit of the unified matching engine repository, analyzes the root causes of previously identified gaps, and details the authentic technical status of the codebase.

The repository brings together two distinct developments:
1. **The Full Domain Specification (`MatchingEngine`)**: 7,000+ lines of Lean 4 verifying a rich limit order book with 16-field orders, stop-order cascades, Time-in-Force policies (Day, GTC, GTD, IOC, FOK), minimum execution quantities, and TLA+ model checking.
2. **The Relational Schema-to-C Synthesis Pipeline (`Amcc` / `VerifiedCMatchingEngine`)**: A compiler that synthesizes intrusive C data structures (`Tpool`, `Atree`, `Llist`, `Thash`) from declarative relational schemas, verifying template-level operational semantics under a formalized C big-step evaluator (`execStmt`, `callFun`).

---

## 2. Audit Findings & Critical Analysis

### 2.1 The Refinement Bridge Gap
- **Audit Finding**: The top-level theorem in `lean/Bridge/EndToEndTheorem.lean` (`c_matching_engine_end_to_end_sound`) does not execute the emitted C program `execStmt (genC S)`.
- **Analysis**:
  - The theorem evaluates hand-written Lean step functions (`abstract_insert`, `abstract_match_step`, `abstract_cancel`) over abstract `BookState`.
  - In previous revisions, tautological hypotheses (such as `h_noncross_sell : Uncrossed (abstract_insert ... req.toOrder)`) were introduced, mirroring the conclusion conjunct verbatim.
  - While AMCC verifies operational contracts for individual C primitives (`c_first_spec_decodes`, `c_next_spec_decodes`, `Llist.first_correct`, `Llist.insert_correct`, `ArrayTableInsert.insert_correct`), the synthesis of the entire multi-level matching loop into a single verified C AST executed under `execStmt` remains an open bridge step.

### 2.2 Memory Well-Formedness & Invariant Derivation
- **Audit Finding**: `wf_mem_implies_AllInv` historically acted as a structural record repackaging rather than deriving book invariants from memory pointer graphs.
- **Analysis**:
  - `AmccMemoryContract` assumed high-level relational properties (tree sortedness, unique IDs, uncrossed levels) as contract fields.
  - The proof of `wf_mem_implies_AllInv` projected these fields directly into `AllInv` without traversing the raw memory graph (`bids_wf`, `asks_wf`, `llist_wf`).
  - True end-to-end memory derivation requires proving that `WfMem m` (raw heap block validity, acyclicity, well-typedness) inductively guarantees `AmccMemoryContract`.

### 2.3 Structural FIFO vs. Phantom Timestamps
- **Audit Finding**: The C schema (`matching_engine.ssim`) and C header (`matching_engine_gen.h`) contain 5 business fields (`id`, `account_id`, `price`, `remaining_qty`, `side`) and lack a `timestamp` field.
- **Analysis**:
  - In intrusive C order book implementations, arrival FIFO priority is structurally enforced by list order within each price level (orders are appended to tail `orders ++ [o]` and consumed from head `orders.head`).
  - Representing FIFO via an explicit timestamp tag in the abstract model created a mismatch with the generated C code. The model must treat FIFO as structural list queueing.

### 2.4 Self-Trade Prevention (STP) Policies
- **Audit Finding**: The static predicate `NoSelfTrades` verified account separation on resting orders but did not differentiate among the four active execution behaviors (`cancel_new`, `cancel_old`, `cancel_both`, `decrement_and_continue`).
- **Analysis**:
  - STP is an operational transition policy, not merely a static book invariant.
  - A comprehensive specification requires relational step contracts (`StepRel`) parameterized by the active `STPMode`.

### 2.5 Memory Allocation and Hot-Path Reality
- **Audit Finding**: Unqualified claims of "0 dynamic allocations" are contradicted by process heap profiling (DHAT/Valgrind).
- **Analysis**:
  - The generated C engine uses `calloc`/`realloc` during process initialization to preallocate memory chunks (~627 MB for order pools, level pools, and hash buckets).
  - Steady-state dynamic allocation is 0 bytes on the hot matching path (pool exhaustion returns `NULL` rather than triggering dynamic growth). Claims must clearly distinguish preallocation from the timed matching loop.

### 2.6 Empirical Benchmarking Methodology
- **Audit Finding**: Benchmark timings showed large variance across runs (49 ns to 69 ns) and arithmetic discrepancies in per-class breakdowns.
- **Analysis**:
  - Measurements without core pinning, cache warmup, and statistical aggregation (median-of-N, variance/CI) reflect machine state rather than intrinsic engine latency.
  - The per-class profiling table must strictly close arithmetically with the headline end-to-end average.

---

## 3. What Is Mechanized vs. What Remains Ongoing Work

| Component | Status | Mechanized Proof Evidence |
|:---|:---:|:---|
| **Domain Model (`MatchingEngine`)** | **PROVED** | 7,024 lines of Lean 4 (`TheoremsFull.lean`): uncrossed book preservation, volume conservation, monotonic clocks, stop-order activation, TIF rules. |
| **AMCC Schema Compiler (`Amcc`)** | **PROVED** | Big-step operational semantics (`CSubset/Eval.lean`), well-formedness checker (`CSubset/Wf.lean`), template correctness for `ArrayTable`, `Llist`, `Tpool`. |
| **Template C Operational Contracts** | **PROVED** | `c_first_spec_decodes`, `c_next_spec_decodes` in `RelationalMemory.lean` linking `callFun` on C ASTs to decoded order list heads. |
| **Abstract Order Invariant Preservation** | **PROVED** | `matching_engine_execution_sound` in `OrderExecution.lean` for abstract insertions and match steps. |
| **Composed Full-Loop C Forward Simulation** | **OPEN** | Composing the entire matching loop AST under `execStmt (genC S)` into a single forward simulation theorem $m \xrightarrow{\mathtt{execStmt}} m'$ with $\alpha(m') = \mathtt{step}(\alpha(m), \mathtt{req})$. |

---

## 4. Technical Roadmap & Milestones

1. **Purge Tautologies**: Revert all tautological hypotheses in `EndToEndTheorem.lean`.
2. **Minimal Executed C Theorem**: Formulate and prove single-order insertion through `execStmt (genC S)` on an initial memory state, proving `WfMem m'` and $\alpha(m') = \mathtt{abstract\_insert}(\alpha(m), \mathtt{req})$ without circular hypotheses.
3. **Formal Memory Graph Derivation**: Connect raw memory reachability (`WfTree`, `WfLevelList`) to `AmccMemoryContract`.
4. **Benchmarking Rigor**: Implement a benchmark runner with hardware core pinning, warmup cycles, median-of-N reporting, and reconciled per-operation profiling.

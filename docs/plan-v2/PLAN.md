Verification Plan v2 — matcher logic
Date 2026-09-27. Supersedes the method and step sections of v1 (main tab). v1 stays as the record of the divergence report, the three C bugs fixed, and the contract work already done.
How to use: paste this tab into Claude Code once, then say "execute Phase N". Claude Code runs that phase, pushes, and writes STATUS-v2.md. Bring the STATUS back to this chat for review before the next phase.
1. Goal
Obtain the strongest machine-checked evidence that the C matching logic is correct, without proving anything about memory management. Memory sits behind AMCC plus a logical contract (EngineDb). The matcher is verified against the contract; the contract is discharged later, on AMCC's side, from its container lemmas. Composition target in one sentence: if malloc and the compiler do not fail us, the matching engine does not fail us.
Not goals for this loop:
• Pool or allocator correctness — a standalone AMCC result (given malloc succeeds, blocks are distinct, in-bounds, recycled), on its own schedule.
• C-to-assembly — gcc and clang are trusted; CompCert is at most an extra test compiler.
• Data-layer representation (pointer vs index, tree vs ladder, preallocation) — matters only when the contract is discharged; decided then.
2. The theorem
Informally: for any store that behaves per the EngineDb contract, running the generated matcher program under the CSubset semantics on a request (a) never reaches an error state, (b) yields the same result code and trade sequence as the Lean spec, and (c) leaves a store that decodes to the spec's book — iterated over any request sequence from the initial state.
Shape (names fixed in Phase 4):
theorem matcher_refines {S} [EngineDb S] : ∀ s req, Inv s → ∃ s' r, execStmt matcherProgram (s, req) = .ok (s', r) ∧ obs r s' = obsSpec (processB (capacity S) (decode s) req) ∧ Inv s'
• Inv is the coupling invariant: decode s satisfies the spec's §13 invariants, every handle the matcher holds is valid, and count s equals the book size.
• execStmt returns an error on any contract violation, invalid handle, arithmetic overflow, or exhausted loop bound, so (a) and (b) are one conjunct proved by one induction — not a separate safety theorem.
• processB cap is a thin wrapper around the existing process (§4). process and its 6,250-line proof base are not edited; each §13 invariant transfers to processB by a short lemma.
• The store is a parameter (EngineDb S: operations plus laws). The matcher fragment has no arrays and no pointers, and capacity is deterministic (§4), so the statement is a plain equality — no quantification over oracle behaviours.
Corollary from the existing spec theorems: every reachable state of the generated matcher satisfies the state invariants (uncrossed, sorted, FIFO, no ghosts, no resting market orders) and every step obeys the STP and post-only rules.
3. Trust boundary
Assumed in this loop, not proved:
1. The C data layer satisfies the EngineDb contract. Evidence: the laws are executed as tests against it (Phase 5); discharged from AMCC container lemmas later (Phase 6).
2. CSubset semantics agrees with the C that gcc and clang implement, on the memory-free fragment. Evidence: Phase 5 differential testing.
3. The printer emits the tree the proof is about. Evidence: independent reparse (Phase 5).
4. gcc and clang compile correctly.
5. Single-threaded execution; engine pointer non-NULL (D10).
Everything above the line is logic and is proved: handle validity, the capacity branch, loop bounds, 64-bit totals.
4. Decisions frozen for v2
• Capacity. The contract exposes capacity (a store parameter) and count. Law: insert succeeds iff count < capacity; otherwise it returns full and leaves the store unchanged. The matcher does one pre-check at entry: if the request may rest (anything process can leave in the book — limit orders that are not IOC/FOK, post-only, stops when triggered) and the store is full, reject with RejectedCapacity before any trade. Pessimistic by design: an order that would have filled completely is also rejected when full. processB applies the identical rule from book.size and cap. No reservation, no unwinding. If amend/replace is in scope, its rule is settled in Phase 1 ⚑.
• Allocation failure is the only allocator fact the matcher sees: insert returns a handle or full. The matcher branches on it; the safety conjunct fails otherwise.
• Handle validity. The contract states, per operation, which handles remain valid (remove h invalidates h and nothing else; insert returns a fresh valid handle; find returns a valid handle or none). Using an invalid handle is an execStmt error. This is where the CancelOrder use-after-free class is caught by the proof.
• Duplicate ids (replaces D1). The matcher looks the incoming id up first; if present, reject with the store unchanged. processB does the same.
• Quantity bounds (replaces D8). Validate 0 < qty ≤ Qmax at entry, with Qmax fixed so that capacity · Qmax < 2^64. Per-level totals are then bounded by a lemma, not an assumption.
• Observables Obs: result code (including the new rejection reasons), the trade list in execution order with (maker id, taker id, price, qty) per trade, and the decoded book. No sequence numbers or timestamps unless process already returns them (Phase 0 records this).
• Request universe: in scope = request types implemented in both process and the handwritten C (Phase 0 matrix). Types on one side only are excluded from the generated matcher and listed for decision.
• STP: the spec follows C (account-0 sentinel). Phase 0 records whether two account-0 orders may trade. No change in this loop.
• Trade buffer: static, at most capacity + 1 trades per request (each trade but the last fully consumes a resting order; triggered stops are separate requests). No caller-owned buffer.
• Retired: c_matching_engine_end_to_end_sound (circular) is deleted. insert_forward_sim and match_step_forward_sim (sorry) are replaced by the Phase 4 statements, not kept. The printer round-trip proof is off the path.
5. Phases — one per Claude Code session
Each phase ends with: lake build clean; grep -rn sorry over the phase's deliverable files empty; a commit; STATUS-v2.md updated (§6); push; stop. A decision point marked ⚑ that the repo cannot settle: stop there and report, do not guess. Paths below are suggestions — keep the repo's existing layout where one exists.
Phase 0 — Inventory and freeze (no proofs)
Deliverable: docs/plan-v2/INVENTORY.md.
1. Request-type matrix. For each of: new limit, market, cancel, amend/replace, IOC, FOK, post-only, stop, iceberg, anything else found — does process support it (which constructor), does c/src/matching_engine.c support it, is it in scope by the §4 rule. ⚑ for any spec-only type.
2. The exact return type of process: result constructors, trade record fields, any counters or timestamps. Propose the Obs record from it.
3. State of EngineDbApi.lean, EngineDbApiLaws.lean, EngineDbAbs.lean: operations, laws, whether the abstract model already proves the laws; gaps against §4 (capacity, count, validity, full).
4. State of CSubset: syntax, execStmt, printer, its memory model, and which constructs the 414 lines of handwritten matcher logic need beyond it (extern calls, opaque handle type, payload get/set, forN, arithmetic and bit primitives).
5. sorry inventory over the whole Lake project, one line each: keep / replaced in Phase N / delete.
6. The STP account-0 semantics as the spec has it.
Acceptance: INVENTORY.md committed; no code changes.
Phase 1 — Contract
Deliverables: the three EngineDb files updated; Spec/ProcessB.lean new.
1. Extend the API with capacity, count, insert returning a handle or full, a validity predicate, and per-operation validity laws; keep the existing find/remove/FIFO/totals laws.
2. Prove every law for the abstract model in EngineDbAbs.lean — the satisfiability witness, without which the theorem is vacuous.
3. Define processB cap over process implementing §4: duplicate-id rejection, qty validation, capacity pre-check, RejectedCapacity. Do not edit process.
4. Transfer lemmas: each §13 invariant for processB, by cases on the wrapper falling through to the existing theorem.
5. Define Obs, obs, obsSpec.
Acceptance: no sorry in the five files; #print axioms on the transfer lemmas shows only standard axioms.
Phase 2 — CSubset memory-free fragment
Deliverables: CSubset syntax, semantics and printer extended; c/gen/engine_db.h; docs/plan-v2/FRAGMENT.md.
1. Add to the AST: opaque handle values; extern calls to the EngineDb operations, whose semantics is the EngineDb S instance; payload get/set through handles; forN as the only loop; fixed-width arithmetic with overflow as an error; the primitives Phase 0 listed. No arrays, no pointers, no address-of in this fragment.
2. Make the semantics parametric in the store: execStmt takes S with an EngineDb S instance.
3. Printer: extern calls print as calls to the data-layer C functions declared in engine_db.h (the contract's C face); the handle type prints as an opaque typedef. Write engine_db.h.
4. FRAGMENT.md: every construct, its C printing, its semantics.
Acceptance: lake build; a small program in the fragment prints and compiles under gcc -std=c11 -Wall -Wextra -Werror and under clang with the same flags.
Phase 3 — Port the matcher
Deliverables: Matcher/Program.lean (the AST); c/gen/matcher.c (printed); build glue.
1. Transcribe the in-scope logic from c/src/matching_engine.c into the fragment, request by request, with the §4 changes: entry pre-check, duplicate-id lookup, qty validation, the full branch. Every loop is forN with a bound derived from capacity. Static trade buffer.
2. Link the printed matcher against the existing handwritten data layer through engine_db.h; an adapter is allowed if thin and listed in STATUS.
3. Run the existing C tests against generated matcher + handwritten data layer. Failures caused by §4 behaviour differing from the handwritten engine (capacity, duplicate id) are expected: list them ⚑, do not change the matcher to match old behaviour.
Acceptance: c/gen/matcher.c compiles under both compilers with -Werror; test tally in STATUS.
Phase 4 — Prove it
Deliverable: Matcher/Refines.lean. Several sessions; report per lemma group.
1. State Inv.
2. Per-request lemmas of the §2 shape, in this order: rejection branches (store unchanged), cancel, then the matching loop by induction on the forN bound using the FIFO and sorted laws.
3. Assemble matcher_refines and the trace corollary: fold over a request list from the initial store, which must decode to the empty book (the init obligation).
4. Delete the retired artefacts (§4).
Acceptance: no sorry in the file; #print axioms matcher_refines recorded in STATUS.
Phase 5 — Evidence below the line
Deliverables: tests/contract/, tests/differential/, tests/semantics/, docs/plan-v2/EVIDENCE.md.
1. Contract tests: each EngineDb law run as a property test against the handwritten C data layer — insert then find, remove then invalid, FIFO order, totals, full exactly at capacity. The statement tested is the statement the theorem assumes.
2. Differential test: generated matcher + C data layer against the Lean spec executed as the oracle (lake exe or an exported reference), random request streams including full-store and duplicate-id cases; the handwritten engine as a third voice. Compare Obs only. If the executable spec is slow, shorten streams and raise their number; record throughput.
3. Semantics test: random programs in the memory-free fragment run under execStmt and under gcc -O0, gcc -O2 and clang; compare only runs that end without error; report the filtered fraction. A Cerberus or CompCert interpreter is an optional third oracle.
4. Printer: reparse c/gen/matcher.c independently (pycparser or clang -ast-dump) and diff against the Lean AST; no round-trip proof.
Acceptance: all suites green; counts and seeds in EVIDENCE.md.
Phase 6 — Discharge the contract (AMCC side, separate loop)
Not started here; recorded so the composition is explicit. Prove the EngineDb laws for the AMCC-generated data layer from AMCC's container lemmas, plus the standalone pool theorem; instantiate S with the generated store; matcher_refines then holds for the whole generated engine, modulo compilers. Design choices that make this cheap (index links, direct-indexed ladder, preallocation) go into AMCC's GOALS.md/PLAN.md as a route change, not into this plan.
6. STATUS-v2.md — written after every phase
• Phase, date, commit hashes, files added or changed.
• Theorems proved, one line each; #print axioms for the headline theorem.
• sorry count per file (0 in deliverables; anything else with a reason).
• Tests: suites run, pass/fail counts, seeds.
• Decisions settled from the repo; ⚑ decisions needing Ara.
• Deviations from this plan and why.
• Next phase and its first task.
7. Claim wording
• After Phase 4: the generated C matching logic, under CSubset semantics, refines the verified Lean specification for every storage layer satisfying the EngineDb contract; the contract is satisfiable, and its laws are tested against the shipped C data layer.
• After Phase 6: additionally, the AMCC-generated data layer satisfies the contract — so the generated engine refines the specification assuming a correct C compiler and a malloc that honours its contract.
• On the open comment in v1: the qualified claim is the target. CompCert is not on the path (Coq-side proofs, no Lean bridge); at most a third test compiler in Phase 5.
8. Rules for Claude Code
• Never edit process or an existing §13 proof; wrap.
• No arrays or pointers in the matcher fragment. If the port seems to need one, the operation belongs in the contract: stop and report ⚑.
• No sorry in deliverable files at phase end; no axiom declarations without ⚑.
• No changes to handwritten C beyond thin adapters listed in STATUS.
• One phase per session; push; stop.
9. Open for Ara (not blocking Phases 0–1)
• Is 14M orders/s a requirement for the generated engine, or is the handwritten engine the performance baseline only? Affects Phase 6 choices, nothing in the proof.
• Do the TLA+ model and the April paper get re-synced after the spec adopted C's STP rule?
• Atree = AVL, and typed-field vs byte-level memory in CSubset — both Phase 6 questions now; moot for the matcher fragment.

---
Decisions after Phase 0 (2026-09-27), recorded in docs/plan-v2/INVENTORY.md:
• Decision 1: spec-only request types (FOK, DAY, stops, market-to-limit, iceberg, minimum quantity, amend) stay out of the generated matcher. Exclusion is a rejection at entry (RejectedUnsupported, store unchanged), not an input assumption; the theorem quantifies over all requests. Amend/replace is out, so its capacity rule is closed.
• Decision 2: Phase 2 builds a separate memory-free language in this repository instead of extending CSubset. "CSubset semantics" for the matcher (§2, §3, §7) means this language's semantics. Linking it to CSubset is a Phase 6 obligation.
• §7 claim wording, supported requests: the claim covers LIMIT (GTC), MARKET (IOC), IOC limit, POST_ONLY and cancel, with STP modes NONE, CANCEL_NEW, CANCEL_OLD, CANCEL_BOTH and DECREMENT; every other request is rejected unchanged, and that rejection is itself covered by the theorem.
Decisions during Phase 2 (2026-09-27), recorded in docs/plan-v2/STATUS-v2.md and FRAGMENT.md:
• Integer rule: the matcher language has one integer type, 64-bit unsigned (id, price, qty, count, capacity, trade quantities). Side, order type, STP mode and result code are enumerations (type `code`, equality only). engine_db.h uses uint64_t for every numeric field; narrower data-layer fields are widened, not range-checked. Overflow stays an error in the semantics and is discharged in Phase 4 from the Phase 1 bounds.
• Level totals are out of the contract: no in-scope matcher path reads one. A data layer that keeps totals maintains them privately, including on ME_order_set_remaining.
• count and levelsUsed are class operations with their own laws (init 0; alloc +1; free −1; every other operation unchanged; alloc fails iff at capacity).
• Post-only is decided in one place: processB takes the book and trades from process, and postOnlyCode reports the rejection process made (postOnly_reject_agrees).
• Phase 4 obligation: level-pool sizing needs "no empty level in the store" and levels ≤ orders in Inv; the Phase 3 matcher frees a level when its last order leaves.

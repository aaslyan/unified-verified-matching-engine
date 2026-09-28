# Phase 5 — Evidence below the line

Plan v2 §3 lists what the refinement theorem (`matcher_refines`,
`matcher_run_refines`) does not prove and trusts instead:

1. the C data layer satisfies the EngineDb contract;
2. the matcher language's semantics agrees with what gcc and clang compile;
3. the printer emits the tree the proof is about;
4. the compilers are correct;
5. execution is single-threaded.

Phase 5 tests items 1–3 and, through item 2, exercises item 4. Every suite is
green. The whole set runs with `tests/run_all.sh`.

**Environment.** gcc 13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04.1), clang 19.1.1
(Ubuntu 1ubuntu1~24.04.2), Lean v4.26.0, Python 3.12.3, pycparser 3.00, Linux
7.0.0 x86_64. Recorded on 2026-09-28.

## 1. Contract tests (`tests/contract/`)

**What is tested.** The EngineDb laws are checked against the data layer as
linked under the matcher. That is the adapter `c/gen/engine_db_adapter.c` over
the handwritten data layer `c/src/matching_engine_gen.c`, called through
`c/gen/engine_db.h`.

**Method.** `contract_test.c` keeps a model of the Lean `Db` view: orders,
levels, queues, hash, trees and live sets. It drives the store with random
operations whose contract preconditions hold in the model, and applies each
operation's Lean postcondition to the model. After every operation it checks
everything observable through `engine_db.h` against the model. Each law has
its own check, and the check's comment quotes the Lean statement it tests.

**Laws checked.** Each check below is labelled with its Lean name.
- Allocation:
  - `orderAlloc_law` and `levelAlloc_law`: allocation fails exactly when the pool is at capacity;
  - `orderAlloc_full` and `levelAlloc_full`: a failed allocation leaves the store unchanged;
  - `orderAlloc_valid`: allocation returns a handle that was not live.
- `orderFree_law` / `orderFree_valid` and `levelFree_law` / `levelFree_valid`.
- `readOrder_law` / `writeOrder_law` and `readLevel_law` / `writeLevel_law`.
- `levelCount_law`.
- `owner_law` / `owner_valid`.
- Hash:
  - `hashFind_law` / `hashFind_valid` / `hashFind_unique`;
  - `hashInsert_law` / `hash_find_after_insert` / `hash_insert_refused`;
  - `hashRemove_law` / `hash_find_after_remove`.
- Queues, which carry the FIFO order:
  - `qInsertTail_law` / `queue_after_insertTail` / `first_stable_under_insertTail`;
  - `qRemove_law` / `first_after_remove_head`;
  - `qFirst_law` / `qFirst_valid`;
  - `qNext_law` / `qNext_valid`.
- Trees:
  - `tFind_law` / `tFind_valid` / `tFind_unique`;
  - `tInsert_law` / `tree_find_after_insert`;
  - `tRemove_law` / `tree_find_after_remove`;
  - `tBest_law` / `tBest_valid` / `tBest_unique`.
- The count and levelsUsed laws for every operation.
- `init_view` / `init_count` / `init_levelsUsed`.
- Handles stay valid after a remaining-quantity write (reduce).
- Level totals equal the sum of remaining quantities. This is private to the data layer, which maintains it.
- Read purity (FRAGMENT.md, "Evaluation order"). Bursts of random reads are interleaved everywhere, and the full observation before and after each burst must be identical.

**Handle validity.** Using a freed handle is undefined in C, so the test never
does it. What it does check is that the store never hands out an invalid handle:
- every lookup (hash find, tree find, tree best, queue first and next, owner) returns a handle live in the model;
- every allocation returns a handle that was not live.

**Run.** `tests/contract/run.sh 1 50 3000`:
- seeds 1–50, 3,000 operations each;
- capacities 0, 1, 2, 5, 16 and 64;
- gcc -O2 and clang -O2.

That is 12 configurations × 150,000 operations = 1.8 million operations. **All laws hold in every configuration.** Check counts per law are printed by the run; at capacity 5 with 20 seeds they range from about 180 (reduce) to 2.2 million (`tFind`).

**Sensitivity.** Three mutants of the adapter are caught within the first 300 operations of seed 1:

| Mutant | Law that fails |
|---|---|
| Order allocation succeeds one row past capacity | `orderAlloc_law` |
| Hash insert replaces a duplicate id instead of refusing it | `hashInsert_law` |
| The remaining-quantity write no longer updates the level total | totals |

## 2. Differential test (`tests/differential/`)

**Three voices.** For each seed, `gen_stream.py` produces a random request
stream, which runs through three engines:
- the **oracle**: the executable spec `processB` (`lean/Matcher/Oracle.lean`, built as `spec_oracle`);
- the **generated matcher** (`c/gen/matcher.c`) with the adapter and the handwritten data layer, calling `gen_process_order` / `gen_cancel_order` for their result codes;
- the **handwritten engine** (`c/src/matching_engine.c`), as a third voice.

**What is compared.** Only `Obs`, after every request: the result code, the
trades (maker, taker, price, qty), and the book view (for each level, best
first: price, then for each order id, remaining, qty, account and STP policy).
The view has no post-only flag, and dropping it is safe: a resting order's
post-only flag is never read again on the path (`postOnly` is read only on the
incoming order, by `process` and `postOnlyCode`, and in a trade's
`aggPostOnly`, which `tradeObs` drops).
The oracle and the generated matcher must agree exactly on every step. The
handwritten engine returns only a bool, so its comparison maps
accepted/cancelled to true. It is compared up to its first divergence, which
is classified per seed by the oracle's result code at that step.

**Streams** contain:
- duplicate ids;
- cancels of resting, removed and never-used ids;
- an unsupported order type and an invalid STP mode;
- price 0, quantity 0, and quantities above Qmax for the capacity;
- at small capacities, a store that fills, so capacity rejections occur and post-only orders arrive at a full store.

| Capacity | Profile | Steps | Oracle = generated | Oracle throughput | Handwritten engine, first divergence per seed |
|---|---|---|---|---|---|
| 2 | full | 100 seeds × 300 = 30,000 | **all 30,000 steps** | 46,607 req/s | capacity 89, qty > Qmax 11 |
| 8 | full | 30,000 | **all** | 37,875 req/s | qty > Qmax 60, capacity 40 |
| 64 | full | 30,000 | **all** | 23,891 req/s | qty > Qmax 99, identical 1 |
| 1,000,000 | full | 30,000 | **all** | 32,704 req/s | qty > Qmax 99, identical 1 |
| 8 | noqmax | 30,000 | **all** | 56,395 req/s | capacity 99, identical 1 |
| 1,000,000 | noqmax | 30,000 | **all** | 53,904 req/s | **identical 100** |

That is 180,000 steps, and the oracle and the generated matcher agree on all
of them. Throughput is wall-clock for the compiled `spec_oracle`, including
process start. Seeds 1–100 at every row.

**Coverage.** The oracle's result codes over the four `full` rows:

| Capacity | Accepted | Cancelled | Unsupported | Invalid | Duplicate | Capacity | Post-only | Unknown id | Post-only at a full store |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 9,166 | 357 | 1,212 | 3,748 | 129 | 10,140 | 153 | 5,095 | 3,774 |
| 8 | 13,983 | 808 | 1,212 | 3,748 | 298 | 4,335 | 972 | 4,644 | 1,610 |
| 64 | 17,629 | 1,145 | 1,212 | 3,748 | 427 | 0 | 1,532 | 4,307 | 0 |
| 1,000,000 | 17,629 | 1,145 | 1,212 | 3,748 | 427 | 0 | 1,532 | 4,307 | 0 |

**Divergence classes of the handwritten engine.** Both are expected, and are
recorded rather than failing the run. They are the two §4 rules the handwritten
engine does not have:
- `capacity`: at a full store, a LIMIT or a non-crossing POST_ONLY order is rejected by the generated matcher before any trade, while the handwritten engine rests it.
- `qty > Qmax`: the v2 quantity bound; the handwritten engine accepts any quantity.

Over the 6 configurations × 100 seeds (600 seed-runs), the first divergence
per seed falls in:

| Class | Seed-runs |
|---|---|
| `capacity` | 228 |
| `qty > Qmax` | 269 |
| none: identical on the whole stream | 103 |

No seed diverged in any other class.

**The second class is a latent overflow in the handwritten engine.** A level's
`total_qty` is a 64-bit sum of its orders' remaining quantities. Without the
Qmax bound, two resting 2^63 orders at one price make it wrap to 0, and
`MatchingEngine_CheckInvariants` still passes, since its own sum wraps too.
`tests/differential/total_overflow.c` demonstrates this; it runs as part of
`tests/differential/run.sh` and reports `level total_qty = 0 (true sum 2^64);
CheckInvariants: 1`. The generated matcher cannot reach this state: its Qmax
check (`qty ≤ Qmax = (2^64 − 1) / (capacity + 1)`) rejects any order whose quantity could
take a level total past 2^64 − 1, so both orders are rejected there.

With the over-Qmax quantities left out (profile `noqmax`) and a store that
never fills, the handwritten engine agrees with the spec on every step of all
100 streams.

## 3. Semantics test (`tests/semantics/`)

**Method.** `lean/Matcher/SemTest.lean` (built as `semtest`) generates random
programs in the matcher language. It runs each one under `execStmt`
(`runEntry` on the model store `AbsStore cap`) and prints it with
`Print.program`. Each program is then compiled with `harness.c`, the adapter
and the handwritten data layer, under gcc -O0, gcc -O2 and clang -O2, and run.

**Comparison.** The outcomes must be identical:
- `ok <value> <order count> [trades]`; or
- `trap <class>`, with the same class on both sides.

For the class, the printer's `me_trap(k)` now carries the error class `k`
(`Print.trapCode`): 1 overflow or zero divisor, 2 loop bound, 3 trade buffer,
4 missing return, 5 malformed extern. The harness defines `ME_TRAP_REPORT` to
read `k` before the abort. **Nothing is filtered.** The generator only
produces programs whose errors are of a class the C traps. A semantic error
that is not (`invalidHandle`, `contract`, `type`, …) is printed as `leanerr`
and fails the comparison.

**Program contents.**
- Expressions with several store reads (`capacity`, `count`, order fields) and pure arithmetic. Expressions contain no state-changing call, by construction.
- `&&` guarding reads through handles that may be null (short-circuit).
- Overflow-adjacent constants: 2^64−1, 2^64−2, 2^63, 2^63−1, 2^32, 2^32−1.
- Every loop-bound edge:
  - literal bounds 0–5, with iteration counts at bound − 1, at the bound, and at bound + 1 and + 2;
  - `capacity + k` bounds with counts `capacity + k`, `capacity + k + 1`, `capacity` and 0;
  - `capacity + k` overflowing, with k = 2^64 − 1 and 2^64 − 2.
- Trade emission up to and past the buffer of `capacity + 1`.
- Allocation, which can fail at capacity, followed by writes of all seven fields.
- Calls to helper functions, some of which fall off their end.

**Printer check included.** Every generated program is also reparsed by
`tests/printer/reparse.py` and compared with its syntax tree (section 4).

**Run.** `tests/semantics/run.sh <seed> 200 <cap>` for seeds 1–5 and
capacities 0, 1, 3 and 7. The generator's seed mixes in the capacity, so the
programs differ between capacities.

| Measure | Value |
|---|---|
| Distinct programs | 4,000 |
| Compiled runs (× 3 configurations) | 12,000 |
| Agree with `execStmt` | **all 12,000** (gcc -O0 4,000/4,000, gcc -O2 4,000/4,000, clang -O2 4,000/4,000) |
| Filtered | none |

| Semantic outcome | Programs | C outcome |
|---|---|---|
| ok (value, order count and trades equal) | 1,699 | same |
| trap 1: overflow or zero divisor | 1,420 | `me_trap(1)` |
| trap 3: trade buffer full | 503 | `me_trap(3)` |
| trap 2: loop bound | 225 | `me_trap(2)` |
| trap 4: missing return | 153 | `me_trap(4)` |

**Fixed during the run.** At capacity 0, the generator's "overflowing" bound
`capacity + (2^64 − 2)` did not overflow, and the Lean semantics tried to fold
over 2^64 − 2 iterations; the run was killed. The overflow edge is now taken
relative to the capacity (`k = 2^64 − capacity` and `2^64 − 1`, for capacity ≥ 1).
All numbers above are from after the fix.

### 3b. Validity-aware extension (all store-call kinds)

**Method.** `lean/Matcher/SemValid.lean` (built as `semvalid`, selected with
`GEN=semvalid tests/semantics/run.sh`) emits programs that use every kind of
store call and the null-handle test, with every handle use valid at its point
of use. The generator runs the model store `AbsStore cap` alongside the
program, and updates it with the same `EngineDb` functions `runExt` uses. It
emits a call only when the call's contract precondition holds in the model at
that point. Invalid programs are never generated, so nothing is filtered: every
emitted program is run and compared, exactly as in §3 (same harness, same
compilers, same outcome comparison, trap class included, printer reparse
included). Pure statements from §3 (arithmetic, branches, bounded loops,
trade emission, helper calls) are interleaved, so programs also trap.

**Why validity is required, and why it is permanent.** Handle reuse is
outside the contract: the laws say an allocation returns a fresh live handle,
not which one. The model store numbers a new handle one above the largest live
one, so freed numbers recur; the C data layer returns whichever pool row its
free list hands out. A program that uses a stale
handle can therefore observe the choice, so exact agreement between the model
store and the C data layer is meaningful only over valid-handle programs. The
refinement theorem is unaffected: it quantifies over every store satisfying
the laws, whatever its reuse policy, and the matcher uses only valid handles
(`Refines` requires the entry function to return `.ok`, so no
`invalidHandle` or `contract` error occurs). The
validity checks are therefore a permanent property of the generator, not a
test option: no configuration turns them off.

**Run.** `GEN=semvalid tests/semantics/run.sh <seed> 200 <cap>`, seeds 1–5,
capacities 0, 1, 3 and 7.

| Measure | Value |
|---|---|
| Distinct programs | 4,000 |
| Compiled runs (× 3 configurations) | 12,000 |
| Agree with `execStmt` | **all 12,000** (gcc -O0, gcc -O2, clang -O2: 4,000/4,000 each) |
| Printer reparse | 4,000 of 4,000 identical |
| Filtered | none |

| Semantic outcome | Programs |
|---|---|
| ok | 1,332 |
| trap 1: overflow or zero divisor | 1,721 |
| trap 3: trade buffer full | 586 |
| trap 2: loop bound | 335 |
| trap 4: missing return | 26 |

**Call-kind coverage.** All 34 kinds occur. "Emitted" counts calls in all
4,000 programs; "completed" counts calls in the 1,332 programs that ran to the
end, so every one of those was executed. `capacity` and `count` reads occur
in the interleaved pure expressions and are not counted here. At capacity 0
every allocation fails, so those programs cover only allocation, finds, bests,
null tests and guarded reads.

| Kind | Emitted | Completed |
|---|---|---|
| `order_alloc` / `order_free` | 22,757 / 3,158 | 7,055 / 1,116 |
| `level_alloc` / `level_free` | 11,305 / 1,675 | 3,501 / 591 |
| `order_set_` id / account / side / stp_mode | 1,004 / 1,072 / 1,088 / 1,088 | 389 / 360 / 400 / 373 |
| `order_set_` price / qty / remaining | 1,132 / 996 / 1,137 | 400 / 355 / 387 |
| `level_set_price` | 2,002 | 673 |
| `hash_find` / `hash_insert` / `hash_remove` | 11,401 / 696 / 281 | 3,523 / 275 / 109 |
| `queue_insert_tail` / `queue_remove` | 1,811 / 576 | 628 / 197 |
| `queue_first` / `queue_next` | 2,384 / 697 | 759 / 237 |
| `order_owner` | 3,759 | 1,323 |
| `bids_find` / `bids_insert` / `bids_remove` / `bids_best` | 5,643 / 465 / 225 / 5,637 | 1,792 / 135 / 66 / 1,701 |
| `asks_find` / `asks_insert` / `asks_remove` / `asks_best` | 5,638 / 422 / 187 / 5,736 | 1,732 / 119 / 59 / 1,745 |
| order field read / level price read / level count read | 972 / 197 / 1,212 | 336 / 65 / 416 |
| null test, order / level | 6,843 / 6,691 | 2,135 / 2,056 |
| `&&`-guarded read through a possibly-null handle | 6,522 | 1,974 |

**Second configuration: small constants (`SEMVALID_CFG=small`).** The
default configuration's pure statements carry every trap edge, so two programs
in three trap part-way, and the store-call sequence after the trap is never
executed. The `small` configuration generates longer programs (40–119
statements) whose pure statements use small constants, `+`, division by a
nonzero literal, loops within their bound and helpers that always return, so
they cannot trap. One pure statement in 48 is still drawn from the full
generator, so traps after long store sequences still occur. The store part,
the validity checks, the compilers and the exact comparison are the same.
The Lean runner's fuel (which bounds nesting, including sequence length, and
has no C counterpart) is raised from 64 to 1,024 for both configurations, so
no program runs out of it. The default configuration's outcomes are unchanged.

Run: `GEN=semvalid SEMVALID_CFG=small tests/semantics/run.sh <seed> 200 <cap>`,
seeds 1–5, capacities 0, 1, 3 and 7.

| Measure | Value |
|---|---|
| Distinct programs | 4,000 |
| Compiled runs (× 3 configurations) | 12,000 |
| Agree with `execStmt` | **all 12,000** (gcc -O0, gcc -O2, clang -O2: 4,000/4,000 each) |
| Printer reparse | 4,000 of 4,000 identical |
| Filtered | none |
| **Ran to completion** | **3,587 of 4,000 (89.7%)**: capacity 0 848/1,000, 1 900/1,000, 3 905/1,000, 7 934/1,000 |
| Other outcomes | trap 1 293, trap 3 61, trap 2 59 |
| Store calls and handle uses executed in completed programs | 205,039 (57.2 per program; default configuration: 36,982, 27.8 per program) |

Per kind, inside the 3,587 completed programs (every call executed):

| Kind | Completed | Kind | Completed |
|---|---|---|---|
| `order_alloc` | 39,466 | `order_free` | 4,642 |
| `level_alloc` | 19,715 | `level_free` | 2,773 |
| `order_set_id` | 1,624 | `order_set_account` | 1,833 |
| `order_set_side` | 1,802 | `order_set_stp_mode` | 1,761 |
| `order_set_price` | 1,753 | `order_set_qty` | 1,764 |
| `order_set_remaining` | 1,933 | `level_set_price` | 3,608 |
| `hash_find` | 19,674 | `hash_insert` | 1,537 |
| `hash_remove` | 820 | `order_owner` | 6,343 |
| `queue_insert_tail` | 3,186 | `queue_remove` | 1,241 |
| `queue_first` | 4,620 | `queue_next` | 1,769 |
| `bids_find` | 9,949 | `asks_find` | 9,861 |
| `bids_insert` | 1,070 | `asks_insert` | 1,037 |
| `bids_remove` | 649 | `asks_remove` | 600 |
| `bids_best` | 9,826 | `asks_best` | 10,002 |
| order field read | 1,977 | level price read | 612 |
| level count read | 2,186 | `&&`-guarded read | 11,710 |
| null test, order | 11,879 | null test, level | 11,817 |

The least-exercised kinds grew roughly tenfold over the default
configuration's completed programs (`asks_remove` 59 → 600, level price read
65 → 612, `bids_remove` 66 → 649).

**Mismatch found and fixed (a generator bug).** The first full run had one
mismatch: seed 3, capacity 3, program 122. `execStmt` returned
`ok 111 0 [1,19,2,0]`, and all three compilers returned `ok 5 0 [1,19,2,0]`.
The program freed `o2`, then allocated `o3`, then read through `o2`. The
model store reuses handle numbers, so `o3` got o2's old number, and the
generator's liveness check (is the variable's handle number live?) accepted
the stale `o2`, which in the model aliased o3's row. In C, `o2` is a dangling
pointer. This was a use after free that the generator believed valid, not a
semantics or compiler disagreement. Fix: on a free, every variable holding that
handle is dead until reassigned, whatever later allocations reuse. All numbers
above are from after the fix; seed 3 at capacity 3 now agrees on all 200.

## 4. Printer (`tests/printer/`)

**Method.** `reparse.py` parses the printed C with pycparser. It first runs
`gcc -E` with stub headers, and leaves `UINT64_C` unexpanded so literals stay
visible. It then maps the C back to the matcher language's tree and prints it
as an S-expression. `lean/Matcher/AstDump.lean` prints the same S-expression
form directly from the Lean AST, not through the C printer, and `run.sh`
diffs the two.

**Erased.** Exactly what the C printing identifies:
- `code` prints as `uint64_t`;
- a null test prints as `== NULL` for both handle types;
- block nesting and `skip` are flattened.

**Rejected.** Anything outside the printer's language is rejected, not skipped.

**Results.**
- `c/gen/matcher.c`: reparses to the tree of `lean/Matcher/Program.lean` (5 functions).
- Every random program of the semantics test: 4,000 of 4,000 identical; of the validity-aware extension (§3b): 4,000 + 4,000 of 4,000 + 4,000.
- Sensitivity: changing one `<=` to `<` in `matcher.c`, or one loop's trap class, is reported: a tree difference in the first case, not the printer's language in the second.

## Summary

| Suite | Scale | Result |
|---|---|---|
| Contract | 1.8M operations, 12 configurations | all laws hold |
| Differential | 180,000 steps, 6 configurations | oracle = generated on every step |
| Semantics | 4,000 programs × 3 compilers | 12,000 of 12,000 identical outcomes, trap class included; nothing filtered |
| Semantics, validity-aware (all 34 store-call kinds, null tests) | 4,000 programs × 3 compilers | 12,000 of 12,000 identical outcomes; nothing filtered |
| Semantics, validity-aware, small constants | 4,000 programs × 3 compilers | 12,000 of 12,000 identical; 89.7% run to completion |
| Printer | `matcher.c` + every semantics program | identical trees |

# Walk-spec STATUS — Phase A4 (result)

Commit: see `git log -1 -- docs/walk-spec/STATUS-W.md`   Branch: walk-spec   lake build: clean (115 jobs)   sorry count under lean/Walk: 0

## Done

- `docs/walk-spec/RESULT-W.md`:
  - §1 dependency closure and the independence claim;
  - §2 re-attribution, with rules and totals before and after;
  - §3 per-lemma tables, with the three-way split and classification;
  - §4 clause table;
  - §5 store operations by branch;
  - §6 walk-only outputs;
  - §7 recommendation.
- `docs/walk-spec/a4/`: `closure.lean` (the dependency closure, via `#eval`), `tables.py` (attribution and split), and their outputs `decls.tsv` and `tables.md`. Both reproduce from the repository root.
- Earlier status files archived: `A0-INVENTORY.md`, `A2-STATUS.md`, `A3a-STATUS.md`, `A3b-STATUS.md`.

## Figures

| | Declaration lines | With comments |
|---|---|---|
| Direct-specific | 1,480 | 1,703 |
| Walk-specific | 2,901 | 3,320 |
| — A2 | 1,319 | |
| — A3 + `WF_of_Inv` | 1,582 | |
| Shared, located in the direct files | 1,113 | 1,277 |
| Walk, extra | 871 | 1,168 |

Before re-attribution: 3,004 vs 4,216 (4,498 with `WFInv` and `LogicInv`).

## Decisions recorded (Ara, A3b)

- `refines_static`, `refines_duplicate`, `refines_capacity` and `refines_cancel` are reused and counted as shared.
- The independence claim is stated as: independent on the matching path; shared for entry rejections, cancel, and `rest_step` via `step_sim`.

## Deviations

- **The three-way split is a keyword rule applied line by line** (stated in RESULT §3), not a hand classification. It is applied identically to both routes. Its totals agree with the line-coverage attribution to within 2 lines.
- **The direct-specific bucket is "reached only from `main`'s theorem".** It contains 36 lines that do not carry the continuation; they are named in RESULT §2.

## ⚑ Questions for Ara

None.

## Next

The experiment's planned phases are complete. Open choices for Ara:
- the RESULT §7 recommendation;
- PLAN-W §6, the parametric `BookOps` with a syntactic instance;
- a `walk_oracle` executable;
- the EVIDENCE.md note for `main` about Phase 3 capacity coverage.

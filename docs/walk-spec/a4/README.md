# A4 data

From the repository root:

    lake env lean docs/walk-spec/a4/closure.lean   # writes docs/walk-spec/a4/decls.tsv
    python3 docs/walk-spec/a4/tables.py            # writes docs/walk-spec/a4/tables.md

`decls.tsv`: every declaration in `MatchingEngine.*`, `Bridge.*`, `Matcher.*`, `Walk.*` with
module, declaration range, and whether it is in the dependency closure of
`Walk.matcher_refines` / `MatcherAccept.matcher_refines`.

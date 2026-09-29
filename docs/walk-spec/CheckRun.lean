import Walk.Check

/-! Runner for `Walk.Check.runIO` (see there); not a library root.
    `WALK_CAP=6 lake env lean docs/walk-spec/CheckRun.lean`; outside `lean/Walk/` so the `Walk.+` glob does not build it. -/

#eval Walk.Check.runIO

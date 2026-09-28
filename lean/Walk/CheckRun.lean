import Walk.Check

/-! Runner for `Walk.Check.runIO` (see there); not a library root.
    `WALK_CAP=6 lake env lean lean/Walk/CheckRun.lean` -/

#eval Walk.Check.runIO

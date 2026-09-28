import Matcher.SemTest

/-! The `semtest` executable: see `Matcher.SemTest`. -/

open SemTest in
def main (args : List String) : IO UInt32 := do
  let seed := (args.getD 0 "1").toNat!.toUInt64
  let count := (args.getD 1 "100").toNat!
  let cap := (args.getD 2 "3").toNat!
  let dir := args.getD 3 "."
  let mut x := seed * 2862933555777941757 + 3037000493 + cap.toUInt64 * 0x9E3779B97F4A7C15
  let mut classes : List (String × Nat) := []
  for k in [0:count] do
    let (P, x') := (genProgram cap).run x
    x := x'
    IO.FS.writeFile s!"{dir}/prog{k}.c" (Matcher.Print.program P)
    IO.FS.writeFile s!"{dir}/prog{k}.sexp" (AstDump.dump P)
    let o := outcome cap P
    IO.FS.writeFile s!"{dir}/prog{k}.exp" (o ++ "\n")
    let cls := (o.splitOn " ").take 2 |> " ".intercalate
    let cls := if o.startsWith "ok" then "ok" else cls
    classes := if classes.any (·.1 == cls) then classes.map fun (c, n) => if c == cls then (c, n + 1) else (c, n)
      else classes ++ [(cls, 1)]
  IO.println s!"semtest: seed {seed}, {count} programs, cap {cap}; outcomes {classes}"
  return 0

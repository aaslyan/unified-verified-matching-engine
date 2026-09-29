import Lean
import Walk.Refine
open Lean

def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack := [root]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | some ci => for c in ci.getUsedConstantsAsSet.toList do
        if !visited.contains c then stack := c :: stack
    | none => pure ()
  return visited

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "<here>"

#eval show CoreM Unit from do
  let env ← getEnv
  let cw := closureOf env ``Walk.matcher_refines
  let cd := closureOf env ``MatcherAccept.matcher_refines
  let keep (m : String) := m.startsWith "MatchingEngine" || m.startsWith "Bridge" ||
    m.startsWith "Matcher" || m.startsWith "Walk"
  let mut out := ""
  for (n, _) in env.constants.toList do
    let m := modOf env n
    if !keep m then continue
    let r ← findDeclarationRanges? n
    let (a, b) := match r with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    out := out ++ s!"{n}\t{m}\t{a}\t{b}\t{cw.contains n}\t{cd.contains n}\n"
  IO.FS.writeFile "docs/walk-spec/a4/decls.tsv" out

import Matcher.Program

/-! Prints the generated matcher as C; `scripts/gen_matcher.sh` writes it to
`c/gen/matcher.c`. -/

def main : IO Unit := IO.print (Matcher.Print.program MatcherProgram.program)

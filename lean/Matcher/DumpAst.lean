import Matcher.AstDump

/-! Prints the matcher's syntax tree (`AstDump.dump`); `tests/printer/run.sh`
diffs it against the reparse of `c/gen/matcher.c`. -/

def main : IO Unit := IO.print (AstDump.dump MatcherProgram.program)

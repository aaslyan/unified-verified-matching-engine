import MatchingEngine.Order

/-!
# Matching Engine — Self-Trade Prevention (§8)

Conflict detection and all four STP policies.

The trigger follows the C engine (`c/src/matching_engine.c`, decision D2/D3 in
`docs/c-vs-spec-divergences.md`): only the incoming order opts in. `stpGroup`
is the account (`none` for account 0) and `stpPolicy` is the STP mode
(`none` for mode NONE). A conflict exists when the incoming order has a
policy and both orders carry the same group. The resting order's policy is
irrelevant; the policy applied is the incoming order's.
-/

-- §8.1 Conflict detection
def selfTradeConflict (inc rest : Order) : Bool :=
  inc.stpPolicy.isSome &&
  match inc.stpGroup, rest.stpGroup with
  | some g1, some g2 => g1 == g2
  | _, _ => false

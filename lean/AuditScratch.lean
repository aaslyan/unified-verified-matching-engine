import Bridge.EndToEndTheorem
import Amcc.Templates.ArrayTableWf

open CSubset
open VerifiedCMatchingEngine

def auditOrderA : VerifiedCMatchingEngine.Order :=
  { id := 1, account := 7, price := 100, qty := 1, side := VerifiedCMatchingEngine.Side.buy }

def auditOrderB : VerifiedCMatchingEngine.Order :=
  { id := 1, account := 8, price := 100, qty := 1, side := VerifiedCMatchingEngine.Side.buy }

def auditDupBook : VerifiedCMatchingEngine.BookState :=
  { bids := [{ price := 100, orders := [auditOrderA, auditOrderB] }], asks := [] }

def idsOfBook (b : VerifiedCMatchingEngine.BookState) : List UInt64 :=
  (VerifiedCMatchingEngine.allOrders b).map (fun o => o.id)

def hasDuplicateId : List UInt64 → Bool
  | [] => false
  | x :: xs => xs.contains x || hasDuplicateId xs

#eval idsOfBook auditDupBook
#eval hasDuplicateId (idsOfBook auditDupBook)

def auditSameAccountBid : VerifiedCMatchingEngine.Order :=
  { id := 10, account := 42, price := 90, qty := 1, side := VerifiedCMatchingEngine.Side.buy }

def auditSameAccountAsk : VerifiedCMatchingEngine.Order :=
  { id := 11, account := 42, price := 110, qty := 1, side := VerifiedCMatchingEngine.Side.sell }

def auditPolicyBlindBook : VerifiedCMatchingEngine.BookState :=
  { bids := [{ price := 90, orders := [auditSameAccountBid] }],
    asks := [{ price := 110, orders := [auditSameAccountAsk] }] }

def noSelfTradesBool (b : VerifiedCMatchingEngine.BookState) : Bool :=
  b.bids.all fun bid =>
    b.asks.all fun ask =>
      bid.orders.all fun ob =>
        ask.orders.all fun oa =>
          ob.account != oa.account || bid.price < ask.price

#eval noSelfTradesBool auditPolicyBlindBook

#eval execStmt (default : Program) 0 Stmt.skip (default : Store)

#print axioms VerifiedCMatchingEngine.c_first_spec
#print axioms VerifiedCMatchingEngine.c_first_spec_decodes
#print axioms VerifiedCMatchingEngine.c_next_spec
#print axioms VerifiedCMatchingEngine.c_next_spec_decodes
#print axioms VerifiedCMatchingEngine.EngineDb_bids_First_spec
#print axioms VerifiedCMatchingEngine.EngineDb_asks_First_spec
#print axioms VerifiedCMatchingEngine.amcc_memory_contract_implies_matcher_invariants
#print axioms VerifiedCMatchingEngine.wf_mem_implies_AllInv
#print axioms VerifiedCMatchingEngine.top_of_book_match_sound
#print axioms VerifiedCMatchingEngine.matching_engine_execution_sound
#print axioms VerifiedCMatchingEngine.c_matching_engine_end_to_end_sound
#print axioms Templates.ArrayTable.genWellFormed

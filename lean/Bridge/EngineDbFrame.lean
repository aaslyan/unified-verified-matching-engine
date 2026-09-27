import Bridge.EngineDbApiLaws

/-!
# Payload access through handles: frame laws

The matcher reads and writes row payload through handles: on an order it
writes every field when it rests a new order and `remaining` on each fill;
on a level it writes `price` when it creates one, and reads `count`. These
laws, stated over any `EngineDb S`, are what a matcher proof uses:

- get after set returns the value set;
- a set leaves every other handle's row unchanged;
- a set changes no queue, hash, tree, handle validity or pool count.

Level totals are not part of the contract (`EngineDbApi`, "Level totals").
-/

namespace EngineDbApi

variable {S : Type} [EngineDb S]

open EngineDb

theorem readOrder_writeOrder_same {s : S} {h : OrderH} {row : OrderRow}
    (hw : (view s).WF) (hpre : EngineDbApi.writeOrder.pre (view s) h row) :
    readOrder (writeOrder s h row) h = some row := by
  rw [readOrder_law, writeOrder_law s h row hw hpre]
  simp

theorem readOrder_writeOrder_other {s : S} {h x : OrderH} {row : OrderRow}
    (hw : (view s).WF) (hpre : EngineDbApi.writeOrder.pre (view s) h row) (hx : x ≠ h) :
    readOrder (writeOrder s h row) x = readOrder s x := by
  rw [readOrder_law, readOrder_law, writeOrder_law s h row hw hpre]
  simp [upd_other _ _ hx]

/-- An order write changes nothing but that one row. -/
theorem writeOrder_frame {s : S} {h : OrderH} {row : OrderRow}
    (hw : (view s).WF) (hpre : EngineDbApi.writeOrder.pre (view s) h row) :
    (view (writeOrder s h row)).queue = (view s).queue ∧
    (view (writeOrder s h row)).hash = (view s).hash ∧
    (view (writeOrder s h row)).tree = (view s).tree ∧
    (view (writeOrder s h row)).levels = (view s).levels ∧
    (∀ x, (view (writeOrder s h row)).validO x ↔ (view s).validO x) ∧
    (∀ x, (view (writeOrder s h row)).validL x ↔ (view s).validL x) ∧
    count (writeOrder s h row) = count s ∧
    levelsUsed (writeOrder s h row) = levelsUsed s := by
  have hpost := writeOrder_law s h row hw hpre
  obtain ⟨hvo, hvl⟩ := writeOrder_valid hpre hpost
  rw [hpost]
  exact ⟨rfl, rfl, rfl, rfl, fun x => by rw [← hpost]; exact hvo x,
    fun x => by rw [← hpost]; exact hvl x, count_writeOrder s h row, levelsUsed_writeOrder s h row⟩

theorem readLevel_writeLevel_same {s : S} {l : LevelH} {row : LevelRow}
    (hw : (view s).WF) (hpre : EngineDbApi.writeLevel.pre (view s) l row) :
    readLevel (writeLevel s l row) l = some row := by
  rw [readLevel_law, writeLevel_law s l row hw hpre]
  simp

theorem readLevel_writeLevel_other {s : S} {l x : LevelH} {row : LevelRow}
    (hw : (view s).WF) (hpre : EngineDbApi.writeLevel.pre (view s) l row) (hx : x ≠ l) :
    readLevel (writeLevel s l row) x = readLevel s x := by
  rw [readLevel_law, readLevel_law, writeLevel_law s l row hw hpre]
  simp [upd_other _ _ hx]

/-- A level write changes nothing but that one row. -/
theorem writeLevel_frame {s : S} {l : LevelH} {row : LevelRow}
    (hw : (view s).WF) (hpre : EngineDbApi.writeLevel.pre (view s) l row) :
    (view (writeLevel s l row)).queue = (view s).queue ∧
    (view (writeLevel s l row)).hash = (view s).hash ∧
    (view (writeLevel s l row)).tree = (view s).tree ∧
    (view (writeLevel s l row)).orders = (view s).orders ∧
    (∀ x, (view (writeLevel s l row)).validO x ↔ (view s).validO x) ∧
    (∀ x, (view (writeLevel s l row)).validL x ↔ (view s).validL x) ∧
    count (writeLevel s l row) = count s ∧
    levelsUsed (writeLevel s l row) = levelsUsed s := by
  have hpost := writeLevel_law s l row hw hpre
  obtain ⟨hvo, hvl⟩ := writeLevel_valid hpre hpost
  rw [hpost]
  exact ⟨rfl, rfl, rfl, rfl, fun x => by rw [← hpost]; exact hvo x,
    fun x => by rw [← hpost]; exact hvl x, count_writeLevel s l row, levelsUsed_writeLevel s l row⟩

/-- **The empty store.** `init` holds no row: no order or level handle is
    valid, both pool counts are 0, and no queue, hash or tree has an entry.
    Phase 4's trace corollary starts here. -/
theorem init_empty :
    (∀ h, ¬ (view (init : S)).validO h) ∧ (∀ l, ¬ (view (init : S)).validL l) ∧
    count (init : S) = 0 ∧ levelsUsed (init : S) = 0 ∧
    (view (init : S)).hash = [] ∧ (∀ t, (view (init : S)).tree t = []) ∧
    (∀ l, (view (init : S)).queue l = []) := by
  rw [init_view]
  refine ⟨fun h => by simp [Db.orderLive, Db.empty], fun l => by simp [Db.levelLive, Db.empty],
    init_count, init_levelsUsed, rfl, fun _ => rfl, fun _ => rfl⟩

end EngineDbApi

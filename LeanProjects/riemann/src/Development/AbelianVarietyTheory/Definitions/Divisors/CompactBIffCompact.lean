import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.CompactB (D : Datum p) : Prop := 2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)

theorem Datum.compactB_iff_compact (D : Datum p) : D.CompactB ↔ D.Compact := Iff.rfl

example (D : Datum p) (h : D.a = 0) : D.CompactB := D.compactB_iff_compact.2 (D.compact_of_a_eq_zero h)

example (D : Datum p) (h : D.IsSimple) : D.CompactB := D.compactB_iff_compact.2 h.compact

example (D : Datum p) (hm : D.m = 1) (hn : 2 ≤ D.n) (ha : Module.finrank ℚ D.F ≤ 2 * D.a) : ¬ D.CompactB :=
  fun h => D.not_compact_of_m_eq_one hm hn ha (D.compactB_iff_compact.1 h)

end GlobalTheory.UPel.HT

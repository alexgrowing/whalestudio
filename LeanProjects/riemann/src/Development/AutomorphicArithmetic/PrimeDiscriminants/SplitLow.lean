import Mathlib
import Formalism.LocalRingCardinality.DataParams₂

namespace UpperTheory.Host

open Formalism.BasicNotions

theorem le_floor_ez (s : Scale) {c : ℝ} (hc : 0 < c) (hce : c ≤ s.ez) (B : ℕ) (hx : (B : ℝ) ^ (5 / c) ≤ s.x) :
    B ≤ ⌊s.x ^ (s.ez / 5)⌋₊ := by
  refine Nat.le_floor ?_
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have e : (B : ℝ) = ((B : ℝ) ^ (5 / c)) ^ (c / 5) := by
    rw [← Real.rpow_mul hB, show 5 / c * (c / 5) = 1 by field_simp, Real.rpow_one]
  calc (B : ℝ) = ((B : ℝ) ^ (5 / c)) ^ (c / 5) := e
    _ ≤ s.x ^ (c / 5) := Real.rpow_le_rpow (Real.rpow_nonneg hB _) hx (by positivity)
    _ ≤ s.x ^ (s.ez / 5) := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith)

end UpperTheory.Host

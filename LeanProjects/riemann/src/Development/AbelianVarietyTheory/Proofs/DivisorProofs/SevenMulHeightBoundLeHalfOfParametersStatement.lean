import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SevenMulHeightBoundLeHalfOfParameters
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seven_mul_height_bound_le_half_of_parameters : ∀ (D T ρ PP κ b f r m k H TO Nb nW t : ℝ), 1 ≤ D → 0 < b → 1 ≤ f → 2 ≤ m → m ≤ k → r = k + m - 1 → 0 ≤ t → 0 ≤ κ → κ ≤ 4 * f * r * b → PP ^ 2 * D ^ 2 * k / m ≤ T → T ≤ TO → 4 * D + 4 ≤ T → ρ ≤ 3 * r * (f * (r * r * (2 * (T + D + 1)) / H + 2 * r * r * T * (2 / Real.sqrt b))) → TO * Nb * f ^ 2 * m ^ 2 * k * D * PP ≤ H → 2500 * r * (D + 1) ≤ TO → f * r * (r + 1) ≤ nW → (2 * f * m) ^ 4 * nW ≤ PP → PP ^ 3 * TO ^ 2 ≤ Real.sqrt b → TO * nW ≤ r + t → m * (t + 1) ≤ Nb → 7 * (D ^ 2 / T + D * ρ) * (PP * κ) ≤ b / 2 := by
  first | exact @GlobalTheory.seven_mul_height_bound_le_half | exact GlobalTheory.seven_mul_height_bound_le_half | (intros; apply GlobalTheory.seven_mul_height_bound_le_half <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpSumBounds
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_exp_mul_aChi_bounds : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) ∧ ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ C * 𝓕.B ^ 11 * min t (1 / t)) ∧ (χ ≠ 1 → (∀ t : ℝ, 1 ≤ t → ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤ C * 𝓕.B * Real.exp (-(t / 2))) ∧ ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1) := by
  first | exact @GlobalTheory.Hk.LFam.exp_sum_bounds | exact GlobalTheory.Hk.LFam.exp_sum_bounds | (intros; apply GlobalTheory.Hk.LFam.exp_sum_bounds <;> assumption)

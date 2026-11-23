import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QFormCount
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_ncard_qForm_le_sub_pi_div_sqrt_mul_le_ten_sqrt : ∀ α γ l θ₁ θ₂ x : ℝ, 1 ≤ α → 1 ≤ γ → 1 ≤ x → {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.Finite ∧ |(({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.ncard : ℕ) : ℝ) - Real.pi / Real.sqrt (α * γ) * x| ≤ 10 * Real.sqrt x := by
  first | exact @GlobalTheory.Hk.qForm_count | exact GlobalTheory.Hk.qForm_count | (intros; apply GlobalTheory.Hk.qForm_count <;> assumption)

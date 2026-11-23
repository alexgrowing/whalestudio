import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExp
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_eq_polar_sqrt : ∀ (ε c : ℝ), (ε = 1 ∨ ε = -1) → ∀ g : ℂ → ENNReal, Measurable g → g 0 = 0 → ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (2 : ENNReal)⁻¹ * g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | exact GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | (intros; apply GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp <;> assumption)

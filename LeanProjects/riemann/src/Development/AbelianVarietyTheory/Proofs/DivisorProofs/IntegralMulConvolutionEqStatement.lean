import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConvolutionEq
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mul_convolution_eq_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∀ κ a : H → ℂ, Continuous κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → ∀ f : H → ℂ, Continuous f → ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  first | exact @GlobalTheory.integral_mul_convolution_eq | exact GlobalTheory.integral_mul_convolution_eq | (intros; apply GlobalTheory.integral_mul_convolution_eq <;> assumption)

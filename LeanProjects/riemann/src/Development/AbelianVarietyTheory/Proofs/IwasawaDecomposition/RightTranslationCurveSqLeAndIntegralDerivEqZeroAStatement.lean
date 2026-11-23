import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RightTranslationCurveSqLeAndIntegralDerivEqZeroA
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 → ∀ f f' : K → ℂ, Continuous f → Continuous f' → (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) → (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  first | exact @GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | exact GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | (intros; apply GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero <;> assumption)

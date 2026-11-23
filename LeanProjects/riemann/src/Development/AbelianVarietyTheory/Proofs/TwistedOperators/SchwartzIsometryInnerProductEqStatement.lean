import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_isometry_inner_product_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ),
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  first | exact @GlobalTheory.schwartz_L2_isometry_preserves_inner | exact GlobalTheory.schwartz_L2_isometry_preserves_inner | (intros; apply GlobalTheory.schwartz_L2_isometry_preserves_inner <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralEqOfDerivs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_integral_eq_of_derivs : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Type} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    (μ : Measure P) [IsFiniteMeasureOnCompacts μ]
    (G : P → SchwartzMap V ℂ), Continuous G → ∀ (C : Set P), IsCompact C → (∀ p ∉ C, G p = 0) →
    ∀ (S : SchwartzMap V ℂ), (∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n S x = ∫ p, iteratedFDeriv ℝ n (G p) x ∂μ) →
    ∀ (l : SchwartzMap V ℂ →L[ℂ] ℂ), l S = ∫ p, l (G p) ∂μ := by
  first | exact @GlobalTheory.SchwClm.clm_integral_eq | exact GlobalTheory.SchwClm.clm_integral_eq | (intros; apply GlobalTheory.SchwClm.clm_integral_eq <;> assumption)

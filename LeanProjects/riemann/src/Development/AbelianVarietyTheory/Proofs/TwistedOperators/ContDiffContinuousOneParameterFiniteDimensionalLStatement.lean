import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W),
    (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) → A 0 = LinearMap.id →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  first | exact @GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | exact GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_toCLM_of_continuous_oneParameter <;> assumption)

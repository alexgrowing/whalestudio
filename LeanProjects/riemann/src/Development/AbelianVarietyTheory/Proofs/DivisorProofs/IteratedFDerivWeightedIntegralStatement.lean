import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWeightedIntegral
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedFDeriv_weighted_integral : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type} [MeasurableSpace W] (μ : Measure W) (Φ : W → SchwartzMap V ℂ) (φ : W → ℂ),
    (∀ n : ℕ, ∃ B : W → ℝ, Integrable B μ ∧ ∀ w x, ‖φ w‖ * ‖iteratedFDeriv ℝ n (Φ w) x‖ ≤ B w) →
    (∀ (n : ℕ) (x : V), AEStronglyMeasurable (fun w => φ w • iteratedFDeriv ℝ n (Φ w) x) μ) →
    ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n (fun y => ∫ w, φ w * Φ w y ∂μ) x = ∫ w, φ w • iteratedFDeriv ℝ n (Φ w) x ∂μ := by
  first | exact @GlobalTheory.iteratedFDeriv_integral_smul_schwartz | exact GlobalTheory.iteratedFDeriv_integral_smul_schwartz | (intros; apply GlobalTheory.iteratedFDeriv_integral_smul_schwartz <;> assumption)

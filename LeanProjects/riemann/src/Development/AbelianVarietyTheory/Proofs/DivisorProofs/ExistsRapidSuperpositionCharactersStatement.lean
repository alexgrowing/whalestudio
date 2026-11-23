import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rapid_superposition_characters' : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  first | exact @GlobalTheory.JSW.exists_rapid_superposition_characters | exact GlobalTheory.JSW.exists_rapid_superposition_characters | (intros; apply GlobalTheory.JSW.exists_rapid_superposition_characters <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientIntegralEquivariantComplex
import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_integral_equivariant_complex : ∀ (G : Type) [Group G] (P : Subgroup G) (X : Type) [MeasurableSpace X] (μ : Measure X) (a : X → G) (δ : P → ℝ≥0),
    (∀ Φ : G → ℝ≥0∞, (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
      (∀ g : G, AEMeasurable (fun x => Φ (a x * g)) μ) → ∀ g : G, ∫⁻ x, Φ (a x * g) ∂μ = ∫⁻ x, Φ (a x) ∂μ) →
    ∀ Ψ : G → ℂ, (∀ g : G, Integrable (fun x => Ψ (a x * g)) μ) → (∀ (p : P) (g : G), Ψ ((p : G) * g) = (δ p : ℂ) * Ψ g) →
    ∀ g : G, ∫ x, Ψ (a x * g) ∂μ = ∫ x, Ψ (a x) ∂μ := by
  first | exact @GlobalTheory.lintegral_translation_identity_to_complex | exact GlobalTheory.lintegral_translation_identity_to_complex | (intros; apply GlobalTheory.lintegral_translation_identity_to_complex <;> assumption)

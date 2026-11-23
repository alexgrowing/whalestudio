import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNMKIntegrationPiProduct
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaNMKIntegration_pi_product : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  first | exact @GlobalTheory.NMKProd.prod_formula | exact GlobalTheory.NMKProd.prod_formula | (intros; apply GlobalTheory.NMKProd.prod_formula <;> assumption)

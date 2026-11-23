import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirichletSeriesIntegralHolomorphic
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichlet_series_integral_holomorphic : ∀ {α ι : Type} [MeasurableSpace α] (μ : Measure α) (φ : ι → α → ℝ) (a : ℝ), (∀ i, Measurable (φ i)) →
    (∀ i x, 0 < φ i x) → (∀ s : ℝ, a < s → ∫⁻ x, ∑' i, ENNReal.ofReal (φ i x ^ s) ∂μ < ⊤) →
    (∀ s : ℂ, a < s.re → Integrable (fun x => ∑' i, (φ i x : ℂ) ^ s) μ) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∫ x, ∑' i, (φ i x : ℂ) ^ s ∂μ) {s | a < s.re} := by
  first | exact @GlobalTheory.TsumCpowHol.tsum_cpow_integrable_and_differentiableOn | exact GlobalTheory.TsumCpowHol.tsum_cpow_integrable_and_differentiableOn | (intros; apply GlobalTheory.TsumCpowHol.tsum_cpow_integrable_and_differentiableOn <;> assumption)

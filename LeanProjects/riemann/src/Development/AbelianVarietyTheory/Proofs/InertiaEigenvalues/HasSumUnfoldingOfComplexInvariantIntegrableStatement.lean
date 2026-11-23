import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumUnfoldingOfComplexInvariantIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  first | exact @GlobalTheory.UnfoldCplx.hasSum_complex | exact GlobalTheory.UnfoldCplx.hasSum_complex | (intros; apply GlobalTheory.UnfoldCplx.hasSum_complex <;> assumption)

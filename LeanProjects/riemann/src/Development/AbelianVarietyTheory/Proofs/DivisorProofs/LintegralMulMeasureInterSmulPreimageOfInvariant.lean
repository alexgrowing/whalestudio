import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory

theorem lintegral_mul_measure_inter_smul_preimage :
    ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  intro S X _ _ _ _ _ _ ν _ μ _ _ D hD E hE ψ hψ hinv
  have hmeas : Measurable (Function.uncurry fun (s : S) (y : X) =>
      ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y))) := by
    have hsm' : Measurable (fun p : S × X => p.1⁻¹ • p.2) :=
      (measurable_fst.inv).smul measurable_snd
    refine (hψ.comp measurable_snd).mul ?_
    exact ((measurable_one.indicator hE).comp measurable_fst).mul
      ((measurable_one.indicator hD).comp hsm')
  have h1 : ∀ y : X, ν (E ∩ {s | s⁻¹ • y ∈ D}) =
      ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂ν := by
    intro y
    have hm : MeasurableSet (E ∩ {s : S | s⁻¹ • y ∈ D}) :=
      hE.inter (hD.preimage (measurable_inv.smul_const y))
    rw [← lintegral_indicator_one hm]
    congr 1; ext s
    by_cases h1 : s ∈ E <;> by_cases h2 : s⁻¹ • y ∈ D <;> simp [Set.indicator, h1, h2]
  have h2 : ∀ s : S, ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ = ∫⁻ x in D, ψ x ∂μ := by
    intro s
    have hf : Measurable (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) :=
      hψ.mul (measurable_one.indicator hD)
    calc ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ
        = ∫⁻ y, (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) (s⁻¹ • y) ∂μ := by
          congr 1; ext y; simp only [hinv]
      _ = ∫⁻ x, ψ x * D.indicator (1 : X → ℝ≥0∞) x ∂μ :=
          (measurePreserving_smul s⁻¹ μ).lintegral_comp hf
      _ = ∫⁻ x in D, ψ x ∂μ := by
          rw [← lintegral_indicator hD]
          congr 1; ext x
          by_cases hx : x ∈ D <;> simp [Set.indicator, hx]
  calc ν E * ∫⁻ x in D, ψ x ∂μ
      = ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ ∂ν := by
        simp only [h2]
        rw [lintegral_mul_const _ (measurable_one.indicator hE), lintegral_indicator_one hE]
    _ = ∫⁻ s, ∫⁻ y, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂μ ∂ν := by
        congr 1; ext s
        rw [← lintegral_const_mul' _ _ (by by_cases h : s ∈ E <;> simp [Set.indicator, h])]
        congr 1; ext y; ring
    _ = ∫⁻ y, ∫⁻ s, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂ν ∂μ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
        congr 1; ext y
        have hm : Measurable (fun s : S =>
            E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) :=
          (measurable_one.indicator hE).mul
            ((measurable_one.indicator hD).comp (measurable_inv.smul_const y))
        rw [h1 y]
        exact lintegral_const_mul (ψ y) hm

end GlobalTheory

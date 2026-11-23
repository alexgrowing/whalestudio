import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem integral_tsum_prod_of_bounded : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X), μ 𝓕 ≠ ⊤ → ∀ (ι κ : Type) [Countable ι] [Countable κ]
    (Φ : ι → κ → X → ℂ), (∀ i k, Measurable (Φ i k)) → ∀ C : ℝ,
    (∀ u, Summable (fun p : ι × κ => ‖Φ p.1 p.2 u‖) ∧ ∑' p : ι × κ, ‖Φ p.1 p.2 u‖ ≤ C) →
    (∫ u in 𝓕, ∑' p : ι × κ, Φ p.1 p.2 u ∂μ = ∑' i, ∫ u in 𝓕, ∑' k, Φ i k u ∂μ) ∧
      Summable (fun i => ‖∫ u in 𝓕, ∑' k, Φ i k u ∂μ‖) := by
  intro X _ μ 𝓕 hμ ι κ _ _ Φ hm C hC
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hμ
  have hmeas : ∀ i, Measurable (fun u => ∑' k, Φ i k u) := fun i =>
    Measurable.tsum (fun k => hm i k)
  have hrow : ∀ u i, Summable (fun k => ‖Φ i k u‖) := fun u i => (hC u).1.prod_factor i
  have hle : ∀ u i, ‖∑' k, Φ i k u‖ ≤ ∑' k, ‖Φ i k u‖ := fun u i =>
    norm_tsum_le_tsum_norm (hrow u i)
  have hfin : ∀ u (s : Finset ι), ∑ i ∈ s, ‖∑' k, Φ i k u‖ ≤ C := by
    intro u s
    have h1 : Summable (fun i => ∑' k, ‖Φ i k u‖) := (hC u).1.prod
    calc ∑ i ∈ s, ‖∑' k, Φ i k u‖ ≤ ∑ i ∈ s, ∑' k, ‖Φ i k u‖ :=
          Finset.sum_le_sum fun i _ => hle u i
      _ ≤ ∑' i, ∑' k, ‖Φ i k u‖ :=
          h1.sum_le_tsum s fun i _ => tsum_nonneg fun k => norm_nonneg _
      _ = ∑' p : ι × κ, ‖Φ p.1 p.2 u‖ := ((hC u).1.tsum_prod).symm
      _ ≤ C := (hC u).2
  have hint : ∀ i, Integrable (fun u => ∑' k, Φ i k u) (μ.restrict 𝓕) := by
    intro i
    refine Integrable.of_bound (hmeas i).aestronglyMeasurable C (ae_of_all _ fun u => ?_)
    simpa using hfin u {i}
  have hsum : Summable (fun i => ∫ u in 𝓕, ‖∑' k, Φ i k u‖ ∂μ) := by
    refine summable_of_sum_le (c := ∫ _u in 𝓕, C ∂μ)
      (fun i => integral_nonneg fun u => norm_nonneg _) fun s => ?_
    rw [← integral_finset_sum s fun i _ => (hint i).norm]
    exact integral_mono (integrable_finset_sum s fun i _ => (hint i).norm) (integrable_const C)
      fun u => hfin u s
  refine ⟨?_, ?_⟩
  · rw [integral_tsum_of_summable_integral_norm hint hsum]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    exact (Summable.of_norm (hC u).1).tsum_prod
  · exact Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      (fun i => norm_integral_le_integral_norm _) hsum

end GlobalTheory

import Mathlib

theorem UpperTheory.involution_map_compact_finite :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X) (U : Set X) (ι : X → X), Measurable ι → IsClosed U → ContinuousOn ι U → (∀ x ∈ U, ι x ∈ U) → (∀ x ∈ U, ι (ι x) = x) → μ Uᶜ = 0 → (∀ K : Set X, IsCompact K → μ K < ⊤) → ∀ K : Set X, IsCompact K → (μ.map ι) K < ⊤ := by
  intro X _ _ _ _ μ U ι hm hU hc hmaps hinv h0 hfin K hK
  rw [MeasureTheory.Measure.map_apply hm hK.measurableSet]
  have hcomp : IsCompact (ι '' (K ∩ U)) :=
    (hK.inter_right hU).image_of_continuousOn (hc.mono Set.inter_subset_right)
  have hsub : ι ⁻¹' K ⊆ ι '' (K ∩ U) ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨ι x, ⟨hx, hmaps x hxU⟩, hinv x hxU⟩
    · exact Or.inr hxU
  calc μ (ι ⁻¹' K) ≤ μ (ι '' (K ∩ U) ∪ Uᶜ) := MeasureTheory.measure_mono hsub
    _ ≤ μ (ι '' (K ∩ U)) + μ Uᶜ := MeasureTheory.measure_union_le _ _
    _ = μ (ι '' (K ∩ U)) := by rw [h0, add_zero]
    _ < ⊤ := hfin _ hcomp

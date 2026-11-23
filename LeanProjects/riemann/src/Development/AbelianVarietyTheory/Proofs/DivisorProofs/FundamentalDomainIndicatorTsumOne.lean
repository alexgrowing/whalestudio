import Mathlib
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem fundamentalDomain_count_ae_eq_one :
    ∀ {G : Type} [Group G] [MeasurableSpace G] (μG : Measure G) (Q : Subgroup G) (𝓓 𝓓₀ : Set G),
    Countable Q → (∀ g : G, Measurable (g * ·)) → μG.IsMulLeftInvariant →
    IsFundamentalDomain Q 𝓓 μG → MeasurableSet 𝓓₀ → 𝓓₀ ⊆ 𝓓 → μG (𝓓 \ 𝓓₀) = 0 →
    ∀ᵐ y ∂μG, ∑' q : Q, 𝓓₀.indicator (1 : G → ENNReal) ((q : G) * y) = 1 := by
  intro G _ _ μG Q 𝓓 𝓓₀ hQ hL hμ h𝓓 _h0m h0s h0n
  haveI : MeasurableConstSMul Q G := ⟨fun g => hL g.1⟩
  haveI : SMulInvariantMeasure Q G μG := ⟨fun g s hs => by
    show μG ((fun x => (g : G) * x) ⁻¹' s) = μG s
    rw [← Measure.map_apply (hL g.1) hs, map_mul_left_eq_self]⟩
  have h1 := h𝓓.ae_covers
  have h2 : ∀ᵐ y ∂μG, ∀ q : Q, q • y ∉ 𝓓 \ 𝓓₀ := by
    rw [ae_all_iff]
    intro q
    have : μG ((fun y => q • y) ⁻¹' (𝓓 \ 𝓓₀)) = 0 := by
      rw [measure_preimage_smul]; exact h0n
    exact measure_eq_zero_iff_ae_notMem.1 this
  have h3 : ∀ᵐ y ∂μG, ∀ q q' : Q, q ≠ q' → ¬ (q • y ∈ 𝓓 ∧ q' • y ∈ 𝓓) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro q'
    by_cases hqq : q = q'
    · exact Filter.Eventually.of_forall (fun y h => absurd hqq h)
    · have hne : q⁻¹ ≠ q'⁻¹ := fun h => hqq (inv_injective h)
      have hd : μG (q⁻¹ • 𝓓 ∩ q'⁻¹ • 𝓓) = 0 := h𝓓.aedisjoint hne
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hd] with y hy _ hyy
      apply hy
      refine ⟨?_, ?_⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hyy.1
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hyy.2
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  obtain ⟨q, hq⟩ := hy1
  have hq0 : q • y ∈ 𝓓₀ := by
    by_contra h
    exact hy2 q ⟨hq, h⟩
  rw [tsum_eq_single q]
  · exact Set.indicator_of_mem hq0 _
  · intro b hb
    apply Set.indicator_of_notMem
    intro hb0
    exact hy3 b q hb ⟨h0s hb0, hq⟩

end GlobalTheory

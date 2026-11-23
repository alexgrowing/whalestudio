import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem unfold_integral_fundamentalDomain (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) : μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → ∀ c g : G → ℂ, Integrable c μ → Continuous g → (∃ B : ℝ, ∀ w, ‖g w‖ ≤ B) → ∫ w, c w * g w ∂μ = ∫ w in 𝓕, ∑' γ : Γ, c ((γ : G) + w) * g ((γ : G) + w) ∂μ := by
  intro hμ 𝓕 h𝓕 c g hc hg hB
  obtain ⟨B, hB⟩ := hB
  have hcg : Integrable (fun w => c w * g w) μ :=
    hc.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  rw [h𝓕.integral_eq_tsum'' _ hcg]
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun w => c ((γ : G) + w) * g ((γ : G) + w)) (μ.restrict 𝓕) := by
    intro γ
    exact (hcg.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_left μ (γ : G))).restrict
  have hfin : ∑' γ : Γ, ∫⁻ w in 𝓕, ‖c ((γ : G) + w) * g ((γ : G) + w)‖ₑ ∂μ ≠ ⊤ := by
    have := h𝓕.lintegral_eq_tsum'' (fun w => ‖c w * g w‖ₑ)
    simp only [AddSubgroup.vadd_def, vadd_eq_add] at this
    rw [← this]
    exact hcg.2.ne
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  exact (integral_tsum hmeas hfin).symm

end GlobalTheory

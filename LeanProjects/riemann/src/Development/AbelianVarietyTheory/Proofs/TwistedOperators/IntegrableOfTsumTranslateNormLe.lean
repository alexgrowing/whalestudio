import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem integrable_of_tsum_translate_norm_le
    (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [Countable Γ] (μ : Measure G) (hμ : μ.IsAddLeftInvariant) (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h𝓕μ : μ 𝓕 < ⊤) (c : G → ℂ) (hc : Continuous c)
    (C : ℝ) (hC : ∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧
      ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) : Integrable c μ := by
  haveI : VAddInvariantMeasure Γ G μ := ⟨fun g s _ => measure_preimage_add μ (g : G) s⟩
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [h𝓕.lintegral_eq_tsum'' (fun x => ‖c x‖ₑ)]
  rw [← lintegral_tsum (f := fun (γ : Γ) x => ‖c (γ +ᵥ x)‖ₑ) fun γ : Γ =>
    ((hc.comp (continuous_const_vadd (γ : G))).measurable.enorm).aemeasurable]
  have hpt : ∀ x, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ≤ ENNReal.ofReal C := by
    intro x
    have h1 : ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ = ENNReal.ofReal (∑' γ : Γ, ‖c ((γ : G) + x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hC x).1]
      refine tsum_congr fun γ => ?_
      rw [ofReal_norm_eq_enorm]
      rfl
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hC x).2
  calc ∫⁻ x in 𝓕, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, ENNReal.ofReal C ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal C * μ 𝓕 := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h𝓕μ

example : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ c : G → ℂ, Continuous c → ∀ C : ℝ, (∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧ ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) → Integrable c μ :=
  fun G _ _ _ _ _ _ Γ _ μ hμ 𝓕 h𝓕 h𝓕μ c hc C hC =>
    integrable_of_tsum_translate_norm_le G Γ μ hμ 𝓕 h𝓕 h𝓕μ c hc C hC

end GlobalTheory

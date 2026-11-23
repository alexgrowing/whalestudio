import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

open scoped Pointwise in

theorem covol_eq_measure_inter_fund : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) (μ : Measure G) (fund A : Set G), (Γ : Set G).Countable → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → MeasurableSet A → (∀ γ ∈ Γ, ∀ x ∈ A, γ * x ∈ A) → covol (Γ : Set G) μ A = μ (A ∩ fund) := by
  intro G _ _ _ Γ μ fund A hc hμ hf hcov hdis hA hinv
  have : Countable Γ := hc.to_subtype
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s hs => by
    have h := hμ γ γ.2
    conv_rhs => rw [← h]
    rw [Measure.map_apply (measurable_const_mul (γ : G)) hs]
    rfl⟩
  have hF : IsFundamentalDomain Γ fund μ := by
    refine IsFundamentalDomain.mk'' hf.nullMeasurableSet ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact ⟨⟨γ, hγ⟩, h⟩
    · intro γ hγ
      exact hdis γ γ.2 (fun h => hγ (Subtype.ext h))
    · intro γ
      exact (measurePreserving_smul γ μ).quasiMeasurePreserving
  apply le_antisymm
  · unfold covol
    refine iInf_le_of_le (A ∩ fund) (iInf_le_of_le (hA.inter hf) (iInf_le_of_le ?_ le_rfl))
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    exact ⟨γ, hγ, hinv γ hγ x hx, h⟩
  · unfold covol
    refine le_iInf fun D => le_iInf fun _ => le_iInf fun hD => ?_
    rw [hF.measure_eq_tsum D]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro x ⟨hx, hxf⟩
    obtain ⟨γ, hγ, h⟩ := hD x hx
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hxf⟩
    rw [Set.mem_inv_smul_set_iff]
    exact h

end GlobalTheory

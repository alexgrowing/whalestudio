import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

def SemidirectCovering.Statement (H L N : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L] [MeasurableSpace L]
    [BorelSpace L] [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] : Prop :=
  ∀ (i : L →* H) (q : H →* L) (j : N →* H), Continuous i → Continuous q → IsClosedEmbedding j →
    (∀ l, q (i l) = l) → (∀ g, q g = 1 ↔ g ∈ j.range) →
    ∀ (μL : Measure L) [μL.IsHaarMeasure] (μN : Measure N) [μN.IsHaarMeasure],
    (∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j) →
    ∀ (Γ : Subgroup H) (C : Set N) (T : Set L), IsCompact C → MeasurableSet T → μL T < ⊤ →
      (∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C) → (∀ l, ∃ γ ∈ Γ, q γ * l ∈ T) →
      ∀ (ν : Measure H) [ν.IsHaarMeasure],
        ∃ S : Set H, MeasurableSet S ∧ ν S < ⊤ ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ S

section Inhabitants

instance : BorelSpace C2 := ⟨(borel_eq_top_of_discrete).symm⟩

theorem SemidirectCovering.hypotheses_met : ∃ (i : C2 →* C2 × C2) (q : C2 × C2 →* C2)
    (j : C2 →* C2 × C2) (μL : Measure C2) (_ : μL.IsHaarMeasure) (μN : Measure C2)
    (_ : μN.IsHaarMeasure) (Γ : Subgroup (C2 × C2)) (C : Set C2) (T : Set C2)
    (ν : Measure (C2 × C2)) (_ : ν.IsHaarMeasure),
    Continuous i ∧ Continuous q ∧ IsClosedEmbedding j ∧ (∀ l, q (i l) = l) ∧
    (∀ g, q g = 1 ↔ g ∈ j.range) ∧
    (∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j) ∧ IsCompact C ∧ MeasurableSet T ∧
    μL T < ⊤ ∧ (∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C) ∧ (∀ l, ∃ γ ∈ Γ, q γ * l ∈ T) ∧
    i ≠ 1 ∧ j ≠ 1 := by
  refine ⟨MonoidHom.inl C2 C2, MonoidHom.fst C2 C2, MonoidHom.inr C2 C2, Measure.haar,
    inferInstance, Measure.haar, inferInstance, ⊤, Set.univ, Set.univ, Measure.haar, inferInstance,
    continuous_of_discreteTopology, continuous_of_discreteTopology,
    continuous_of_discreteTopology.isClosedEmbedding (fun a b hab => by simpa using congrArg Prod.snd hab),
    fun l => rfl, ?_, ?_, isCompact_univ, MeasurableSet.univ, measure_lt_top _ _,
    fun n => ⟨1, Subgroup.mem_top _, by simp⟩, fun l => ⟨1, Subgroup.mem_top _, by simp⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩
    constructor
    · intro hg
      refine ⟨b, ?_⟩
      simp only [MonoidHom.coe_fst] at hg
      simp [hg]
    · rintro ⟨n, hn⟩
      rw [← hn]
      simp
  · intro l
    congr 1
    funext n
    ext <;> simp
  · intro h1
    have := congrArg (fun f => (f (Multiplicative.ofAdd 1)).1) h1
    simp at this
  · intro h1
    have := congrArg (fun f => (f (Multiplicative.ofAdd 1)).2) h1
    simp at this

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume

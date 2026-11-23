import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem exists_fundamentalDomain_snd_of_two_smul_mem {ι : Type} [Fintype ι]
    (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ] :
    Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ →
    (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) →
    ∃ D : Set (ι → ℝ), MeasurableSet D ∧
      ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  intro hspan h2
  let L₂ : Submodule ℤ (ι → ℝ) := Λ.map (LinearMap.snd ℤ (ι → ℝ) (ι → ℝ))
  have hmem : ∀ b, b ∈ L₂ ↔ ∃ a, (a, b) ∈ Λ := by
    intro b
    simp only [L₂, Submodule.mem_map, LinearMap.snd_apply]
    constructor
    · rintro ⟨⟨a, b'⟩, h, rfl⟩; exact ⟨a, h⟩
    · rintro ⟨a, h⟩; exact ⟨(a, b), h, rfl⟩
  have hin : ∀ x : L₂, ((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)) ∈ Λ := by
    intro x
    obtain ⟨a, ha⟩ := (hmem x).1 x.2
    exact h2 a x ha
  haveI : DiscreteTopology L₂ := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : L₂ => (⟨((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)), hin x⟩ : Λ)) ?_ ?_
    · exact Continuous.subtype_mk
        (by fun_prop) _
    · intro x y hxy
      have h := congrArg (fun z : Λ => (z : (ι → ℝ) × (ι → ℝ)).2) hxy
      simp only at h
      exact Subtype.ext (smul_right_injective _ (two_ne_zero) h)
  haveI : IsZLattice ℝ L₂ := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro y _
    have hy : ((0 : ι → ℝ), y) ∈ Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := LinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) hy
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨⟨a, b⟩, h, rfl⟩
    exact (hmem b).2 ⟨a, h⟩
  refine ⟨latticeDomain L₂, measurableSet_latticeDomain L₂, fun y => ?_⟩
  obtain ⟨⟨l, hl⟩, h1, h3⟩ := existsUnique_add_mem_latticeDomain L₂ y
  refine ⟨l, ⟨(hmem l).1 hl, h1⟩, ?_⟩
  rintro m ⟨hm, hm'⟩
  exact congrArg Subtype.val (h3 ⟨m, (hmem m).2 hm⟩ hm')

end GlobalTheory

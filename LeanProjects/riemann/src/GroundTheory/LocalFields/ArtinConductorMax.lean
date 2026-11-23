import Mathlib
import GroundTheory.LocalFields.ArtinConductorDiscriminant

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

section Separate

end Separate

section Cut

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {L : IntermediateField K Ω}

def kerFixedField (ψ : (L ≃ₐ[K] L) →* ℂˣ) : IntermediateField K Ω :=
  IntermediateField.lift (IntermediateField.fixedField ψ.ker)

theorem kerFixedField_le (ψ : (L ≃ₐ[K] L) →* ℂˣ) : kerFixedField ψ ≤ L :=
  IntermediateField.lift_le _

instance [FiniteDimensional K L] (ψ : (L ≃ₐ[K] L) →* ℂˣ) : FiniteDimensional K (kerFixedField ψ) :=
  (IntermediateField.liftAlgEquiv (IntermediateField.fixedField ψ.ker)).toLinearEquiv.finiteDimensional

instance [FiniteDimensional K L] [IsGalois K L] (ψ : (L ≃ₐ[K] L) →* ℂˣ) :
    IsGalois K (kerFixedField ψ) :=
  IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv (IntermediateField.fixedField ψ.ker))

theorem ker_restrictAut_kerFixedField [FiniteDimensional K L] [IsGalois K L]
    (ψ : (L ≃ₐ[K] L) →* ℂˣ) : (restrictAut (kerFixedField_le ψ)).ker = ψ.ker := by
  ext σ
  rw [MonoidHom.mem_ker]
  conv_rhs => rw [← IntermediateField.fixingSubgroup_fixedField ψ.ker]
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h1 y hy
    have := congrArg (fun τ : kerFixedField ψ ≃ₐ[K] kerFixedField ψ ↦
      ((τ ⟨y.1, (IntermediateField.mem_lift y).2 hy⟩ : kerFixedField ψ) : Ω)) h1
    simp only [restrictAut_apply, AlgEquiv.one_apply] at this
    exact Subtype.ext this
  · intro h1
    refine AlgEquiv.ext fun x ↦ Subtype.ext ?_
    rw [restrictAut_apply, AlgEquiv.one_apply]
    exact congrArg Subtype.val (h1 _ ((IntermediateField.mem_lift ⟨x.1, kerFixedField_le ψ x.2⟩).1 x.2))

end Cut

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

section Max

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

end Max

section Factor

variable {L : IntermediateField K Ω} [FiniteDimensional K L] [IsGalois K L]

theorem restrictAut_surjective {M : IntermediateField K Ω} [FiniteDimensional K M] [IsGalois K M]
    (h : M ≤ L) : Function.Surjective (restrictAut (K := K) h) := by
  have hr := map_upperRamificationGroup_restrictAut (K := K) (Ω := Ω) h (-1)
  rw [upperRamificationGroup_of_nonpos (by norm_num), lowerRamificationGroupReal_eq_top le_rfl,
    upperRamificationGroup_of_nonpos (by norm_num), lowerRamificationGroupReal_eq_top le_rfl] at hr
  intro τ
  have hτ : τ ∈ (⊤ : Subgroup (L ≃ₐ[K] L)).map (restrictAut h) := hr ▸ Subgroup.mem_top τ
  obtain ⟨σ, _, hσ⟩ := hτ
  exact ⟨σ, hσ⟩

theorem exists_injective_comp_restrictAut_eq {M : IntermediateField K Ω} [FiniteDimensional K M]
    [IsGalois K M] (h : M ≤ L) (ψ : (L ≃ₐ[K] L) →* ℂˣ) (hker : (restrictAut h).ker = ψ.ker) :
    ∃ ψ' : (M ≃ₐ[K] M) →* ℂˣ, Function.Injective ψ' ∧ ψ'.comp (restrictAut h) = ψ := by
  have hsurj := restrictAut_surjective (K := K) (Ω := Ω) h
  let ψ' : (M ≃ₐ[K] M) →* ℂˣ := (restrictAut h).liftOfSurjective hsurj ⟨ψ, hker.le⟩
  have hcomp : ψ'.comp (restrictAut h) = ψ :=
    (restrictAut h).liftOfRightInverse_comp _ (Function.rightInverse_surjInv hsurj) ⟨ψ, hker.le⟩
  refine ⟨ψ', ?_, hcomp⟩
  rw [injective_iff_map_eq_one]
  intro τ hτ
  obtain ⟨σ, rfl⟩ := hsurj τ
  have hσ : σ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, ← hcomp]
    exact hτ
  rw [← hker] at hσ
  exact hσ

theorem isAbelianGalois_of_ker_eq {M : IntermediateField K Ω} [FiniteDimensional K M]
    [IsGalois K M] (h : M ≤ L) (ψ : (L ≃ₐ[K] L) →* ℂˣ) (hker : (restrictAut h).ker = ψ.ker) :
    IsAbelianGalois K M := by
  obtain ⟨ψ', hinj, -⟩ := exists_injective_comp_restrictAut_eq h ψ hker
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun a b ↦ hinj (by rw [map_mul, map_mul, mul_comm])⟩⟩
  exact { }

instance (ψ : (L ≃ₐ[K] L) →* ℂˣ) : IsAbelianGalois K (kerFixedField ψ) :=
  isAbelianGalois_of_ker_eq (kerFixedField_le ψ) ψ (ker_restrictAut_kerFixedField ψ)

end Factor

end GroundTheory.LocalField

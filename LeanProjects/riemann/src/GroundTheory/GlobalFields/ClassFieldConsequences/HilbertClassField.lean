import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup SemiLocal
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension)
open scoped nonZeroDivisors

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

abbrev hilbertClassField : IntermediateField K Ω :=
  (Modulus.one : Modulus K).rayClassField Ω

instance finiteDimensional_hilbertClassField : FiniteDimensional K (hilbertClassField K Ω) :=
  inferInstanceAs (FiniteDimensional K ((Modulus.one : Modulus K).rayClassField Ω))

instance isAbelianGalois_hilbertClassField : IsAbelianGalois K (hilbertClassField K Ω) :=
  inferInstanceAs (IsAbelianGalois K ((Modulus.one : Modulus K).rayClassField Ω))

theorem range_ideleClassNorm_hilbertClassField :
    (ideleClassNorm K (hilbertClassField K Ω)).range =
      (standardOpenSubgroup K).map (IdeleClassGroup.mk K) := by
  rw [← Modulus.congruenceSubgroup_one]
  exact (Modulus.one : Modulus K).range_ideleClassNorm_rayClassField Ω

theorem isUnramifiedEverywhere_hilbertClassField :
    IsUnramifiedEverywhere K (hilbertClassField K Ω) := by
  refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [isUnramifiedIn_iff_ramificationIdx]
    intro w hw
    have := hw
    exact (Modulus.one : Modulus K).ramificationIdx_rayClassField_eq_one Ω
      (Modulus.not_dvd_one_ideal v) w
  · rw [← infiniteLocalSymbol_eq_one_iff]
    ext1 x
    have hx : IdeleClassGroup.mk K (infiniteEmbedding v x) ∈
        (ideleClassNorm K (hilbertClassField K Ω)).range := by
      rw [range_ideleClassNorm_hilbertClassField]
      exact ⟨_, infiniteEmbedding_mem_standardOpenSubgroup v x, rfl⟩
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk,
      ideleSymbol_infiniteEmbedding] at hx
    rw [hx, MonoidHom.one_apply]

theorem le_hilbertClassField_iff (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    L ≤ hilbertClassField K Ω ↔ IsUnramifiedEverywhere K L := by
  constructor
  · intro hle
    exact (isUnramifiedEverywhere_hilbertClassField K Ω).of_le hle
  · intro h
    refine (range_ideleClassNorm_le_range_iff L (hilbertClassField K Ω)).1 ?_
    rw [range_ideleClassNorm_hilbertClassField]
    rintro _ ⟨x, hx, rfl⟩
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk]
    refine ideleSymbol_eq_one_of_isUnramifiedEverywhere K L h fun v ↦ ?_
    have hx' : x ∈ (Modulus.one : Modulus K).congruenceSubgroup := by
      rw [Modulus.congruenceSubgroup_one]
      exact hx
    have hv := ((Modulus.one : Modulus K).mem_congruenceSubgroup.1 hx').1 v
    rw [(Modulus.exponent_eq_zero_iff _ v).2 (Modulus.not_dvd_one_ideal v)] at hv
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
      (mem_unitsLevel.1 hv).1

def hilbertClassFieldArtinEquiv :
    ClassGroup (𝓞 K) ≃* (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω) :=
  Modulus.classGroupEquiv.symm.trans ((Modulus.one : Modulus K).rayClassArtinEquiv Ω)

theorem hilbertClassFieldArtinEquiv_mk0 (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 (hilbertClassField K Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    hilbertClassFieldArtinEquiv K Ω
        (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      arithFrobAt (𝓞 K) (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω) w.asIdeal := by
  change (Modulus.one : Modulus K).rayClassArtinEquiv Ω (Modulus.classGroupEquiv.symm
    (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) = _
  rw [← Modulus.classGroupEquiv_primeClass v, MulEquiv.symm_apply_apply]
  exact (Modulus.one : Modulus K).rayClassArtinEquiv_primeClass Ω (Modulus.not_dvd_one_ideal v) w

end

end GroundTheory.Global

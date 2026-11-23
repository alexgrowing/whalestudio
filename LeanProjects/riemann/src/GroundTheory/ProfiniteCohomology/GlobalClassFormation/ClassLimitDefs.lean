import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Sequence
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

abbrev unitsRep : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := galUnitsZ ℚ ℚ̄

abbrev classRep : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := Rep.ofMulDistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit

instance isDiscreteRep_classRep : IsDiscreteRep classRep := by
  refine (isDiscreteRep_iff classRep).2 fun z => ?_
  obtain ⟨F, c, rfl⟩ := IdeleClassLimit.exists_of (Additive.toMul z)
  have : FiniteDimensional ℚ F.1 := F.2
  refine Subgroup.isOpen_mono (H₁ := F.1.fixingSubgroup) (fun σ hσ ↦ ?_) F.1.fixingSubgroup_isOpen
  exact congrArg Additive.ofMul (IdeleClassLimit.smul_of_eq_of_mem_fixingSubgroup hσ c)

def diagMor : unitsRep ⟶ IdeleLimit.rep :=
  Rep.ofHom ⟨(MonoidHom.toAdditive IdeleLimit.diag).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (IdeleLimit.diag_map σ x.toMul)⟩

@[simp]
theorem diagMor_hom_apply (x : Additive ℚ̄ˣ) :
    diagMor.hom x = Additive.ofMul (IdeleLimit.diag x.toMul) :=
  rfl

def toClassMor : IdeleLimit.rep ⟶ classRep :=
  Rep.ofHom ⟨(MonoidHom.toAdditive IdeleLimit.toClassLimit).toIntLinearMap, fun σ => LinearMap.ext
    fun x => congrArg Additive.ofMul (IdeleLimit.toClassLimit_smul σ x.toMul)⟩

@[simp]
theorem toClassMor_hom_apply (x : Additive IdeleLimit) :
    toClassMor.hom x = Additive.ofMul (IdeleLimit.toClassLimit x.toMul) :=
  rfl

def idelesShortComplex : ShortComplex (Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  ShortComplex.mk diagMor toClassMor (by
    ext x
    exact congrArg Additive.ofMul (IdeleLimit.toClassLimit_diag x.toMul))

theorem shortExact_of_injective_of_surjective {k G : Type u} [CommRing k] [Group G]
    (S : ShortComplex (Rep.{u} k G)) (hf : Function.Injective S.f.hom)
    (hex : ∀ b, S.g.hom b = 0 → ∃ a, S.f.hom a = b) (hg : Function.Surjective S.g.hom) :
    S.ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    exact hex
  mono_f := (Rep.mono_iff_injective _).2 hf
  epi_g := (Rep.epi_iff_surjective _).2 hg

theorem idelesShortComplex_shortExact : idelesShortComplex.ShortExact := by
  refine shortExact_of_injective_of_surjective _ (fun x y h =>
    congrArg Additive.ofMul (IdeleLimit.diag_injective (congrArg Additive.toMul h))) (fun z hz => ?_)
    (fun c => ?_)
  · obtain ⟨a, ha⟩ := (IdeleLimit.mem_range_diag_iff (Additive.toMul z)).2
      (congrArg Additive.toMul hz)
    exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩
  · obtain ⟨z, hz⟩ := IdeleLimit.toClassLimit_surjective (Additive.toMul c)
    exact ⟨Additive.ofMul z, congrArg Additive.ofMul hz⟩

variable (K : FiniteSubfield)

abbrev unitsLimitRep : Rep ℤ K.1.fixingSubgroup := Rep.res K.1.fixingSubgroup.subtype unitsRep

abbrev classLimitRep : Rep ℤ K.1.fixingSubgroup := Rep.res K.1.fixingSubgroup.subtype classRep

abbrev idelesShortComplexRes : ShortComplex (Rep ℤ K.1.fixingSubgroup) :=
  idelesShortComplex.map (Rep.resFunctor K.1.fixingSubgroup.subtype)

theorem idelesShortComplexRes_shortExact : (idelesShortComplexRes K).ShortExact :=
  (Rep.shortExact_res _).2 idelesShortComplex_shortExact

end

end GroundTheory.ProfCoh

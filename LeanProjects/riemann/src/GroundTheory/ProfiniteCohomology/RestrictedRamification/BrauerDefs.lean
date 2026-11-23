import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

def gsRestrict : K.1.fixingSubgroup →* galUnramifiedOutside K.1 ℚ̄ S :=
  (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S)).comp
    (IntermediateField.fixingSubgroupEquiv K.1).toMonoidHom

theorem gsRestrict_apply (σ : K.1.fixingSubgroup) (x : maxUnramifiedOutside K.1 ℚ̄ S) :
    ((gsRestrict K S σ x : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) x :=
  AlgEquiv.restrictNormal_commutes (IntermediateField.fixingSubgroupEquiv K.1 σ) _ x

theorem continuous_gsRestrict : Continuous (gsRestrict K S) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ :=
    (krullTopology_mem_nhds_one_iff K.1 (maxUnramifiedOutside K.1 ℚ̄ S) s).1 hs
  have := K.2
  let E' : IntermediateField K.1 ℚ̄ := E.map (maxUnramifiedOutside K.1 ℚ̄ S).val
  have hE' : FiniteDimensional K.1 E' :=
    LinearEquiv.finiteDimensional (E.equivMap (maxUnramifiedOutside K.1 ℚ̄ S).val).toLinearEquiv
  have hE'₀ : FiniteDimensional ℚ E' := Module.Finite.trans K.1 E'
  have hE'' : FiniteDimensional ℚ (E'.restrictScalars ℚ) := hE'₀
  rw [Filter.mem_map, mem_nhds_subtype]
  refine ⟨((E'.restrictScalars ℚ).fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)),
    (krullTopology_mem_nhds_one_iff ℚ ℚ̄ _).2 ⟨E'.restrictScalars ℚ, hE'', le_rfl⟩, ?_⟩
  intro σ hσ
  apply hEs
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply Subtype.val_injective
  rw [gsRestrict_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ (x : ℚ̄) ⟨x, hx, rfl⟩

instance isAlgebraic_algebraicClosure_finiteSubfield : Algebra.IsAlgebraic K.1 ℚ̄ :=
  Algebra.IsAlgebraic.tower_top (K := ℚ) K.1

instance isIntegral_maxUnramifiedOutside_finiteSubfield :
    Algebra.IsIntegral K.1 (maxUnramifiedOutside K.1 ℚ̄ S) :=
  inferInstance

instance isDiscreteRep_galUnits_maxUnramifiedOutside :
    IsDiscreteRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
  isDiscreteRep_galUnits

instance isDiscreteRep_uliftIntToIntRep_galUnits_maxUnramifiedOutside :
    IsDiscreteRep (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) :=
  isDiscreteRep_uliftIntToIntRep _

instance isDiscreteRep_galSUnitsMax_finiteSubfield : IsDiscreteRep (galSUnitsMax K.1 ℚ̄ S) :=
  isDiscreteRep_galSUnits _ _

def gsUnitsMor :
    Rep.res (gsRestrict K S) (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) ⟶
      unitsLimitRep K :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ => LinearMap.ext fun _ => congrArg Additive.ofMul (Units.ext (gsRestrict_apply K S σ _))⟩

@[simp]
theorem gsUnitsMor_hom_apply (x : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ((Additive.toMul ((gsUnitsMor K S).hom x) : ℚ̄ˣ) : ℚ̄) =
      ((x.toMul : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : ℚ̄) :=
  rfl

def gsBrauerInfl (n : ℕ) :
    cohomology (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) n ⟶
      cohomology (unitsLimitRep K) n :=
  cohomologyMapAlong (gsRestrict K S) (continuous_gsRestrict K S) (gsUnitsMor K S) n

def sUnitsBrauer : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 →+ cohomology (unitsLimitRep K) 2 :=
  (gsBrauerInfl K S 2).hom.toAddMonoidHom.comp
    ((cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).toAddMonoidHom.comp
      (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom.toAddMonoidHom)

theorem sUnitsBrauer_apply (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    sUnitsBrauer K S y = (gsBrauerInfl K S 2).hom
      (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2
        ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y)) :=
  rfl

end

end GroundTheory.ProfCoh

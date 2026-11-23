import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
import GroundTheory.ProfiniteCohomology.FilteredHomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

instance : IsScalarTower K.1 F.1 E.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable (K F E) in

def levelRestrict : (E.1 ≃ₐ[K.1] E.1) →* (F.1 ≃ₐ[K.1] F.1) :=
  AlgEquiv.restrictNormalHom (F := K.1) (K₁ := E.1) F.1

theorem coe_levelRestrict_apply (τ : E.1 ≃ₐ[K.1] E.1) (x : F.1) :
    algebraMap F.1 E.1 (levelRestrict K F E τ x) = τ (algebraMap F.1 E.1 x) :=
  AlgEquiv.restrictNormal_commutes τ F.1 x

theorem levelRestrict_restrictHom (g : K.1.fixingSubgroup) :
    levelRestrict K F E (restrictHom (E := E) g) = restrictHom (E := F) g := by
  ext x
  have := coe_levelRestrict_apply (K := K) (F := F) (E := E) (restrictHom (E := E) g) x
  have h2 := congrArg Subtype.val this
  exact h2

theorem continuous_levelRestrict : Continuous (levelRestrict K F E) :=
  continuous_of_discreteTopology

theorem ideleMap_smul (τ : E.1 ≃ₐ[K.1] E.1) (x : IdeleGroup F.1) :
    ideleMap (Fact.out : F ≤ E) (levelRestrict K F E τ • x) = τ • ideleMap (Fact.out : F ≤ E) x := by
  rw [smul_idele_eq_ideleEquiv, smul_idele_eq_ideleEquiv]
  exact (ideleEquiv_ideleEmbedding_of_comm ((levelRestrict K F E τ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1)
    (τ : E.1 ≃+* E.1) (fun y ↦ (coe_levelRestrict_apply τ y).symm) x).symm

variable (K F E) in

def levelMap : Rep.res (levelRestrict K F E) (ideleRep K.1 F.1) ⟶ ideleRep K.1 E.1 :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (ideleMap (Fact.out : F ≤ E))).toIntLinearMap,
    fun τ => LinearMap.ext fun x => congrArg Additive.ofMul (ideleMap_smul τ x.toMul)⟩

@[simp]
theorem levelMap_hom_apply (x : Additive (IdeleGroup F.1)) :
    (levelMap K F E).hom x = Additive.ofMul (ideleMap (Fact.out : F ≤ E) x.toMul) :=
  rfl

variable (K F E) in

def levelTransition (n : ℕ) : cohomology (ideleRep K.1 F.1) n ⟶ cohomology (ideleRep K.1 E.1) n :=
  cohomologyMapAlong (levelRestrict K F E) continuous_levelRestrict (levelMap K F E) n

theorem levelCochains_comp :
    cochainsMapAlong (levelRestrict K F E) continuous_levelRestrict (levelMap K F E) ≫
      cochainsMapAlong restrictHom continuous_restrictHom (levelMor K E) =
      cochainsMapAlong restrictHom continuous_restrictHom (levelMor K F) := by
  rw [← cochainsMapAlong_comp]
  ext m x : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (of E (ideleMap (Fact.out : F ≤ E)
      ((x.1 fun i => levelRestrict K F E (restrictHom (E := E) (g i))).toMul))) =
    Additive.ofMul (of F ((x.1 fun i => restrictHom (E := F) (g i)).toMul))
  have hfun : (fun i => levelRestrict K F E (restrictHom (E := E) (g i))) =
      fun i => restrictHom (E := F) (g i) := funext fun i => levelRestrict_restrictHom (g i)
  refine (congrArg Additive.ofMul (of_ideleMap (Fact.out : F ≤ E) _)).trans ?_
  rw [hfun]

theorem levelTransition_comp_levelInfl (n : ℕ) :
    levelTransition K F E n ≫ levelInfl K E n = levelInfl K F n := by
  rw [levelTransition, levelInfl, levelInfl]
  unfold cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [levelCochains_comp]

end Transition

end

end GroundTheory.ProfCoh

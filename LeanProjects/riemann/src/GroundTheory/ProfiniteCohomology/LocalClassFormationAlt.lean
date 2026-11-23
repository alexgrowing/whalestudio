import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantRes
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Open

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsGalois K Ksep]

theorem fixingSubgroup_fixedField_openSubgroup (U : OpenSubgroup Gal(Ksep/K)) :
    (fixedField (U : Subgroup Gal(Ksep/K))).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨(U : Subgroup Gal(Ksep/K)), U.isClosed⟩

instance finiteDimensional_fixedField_openSubgroup (U : OpenSubgroup Gal(Ksep/K)) :
    FiniteDimensional K (fixedField (U : Subgroup Gal(Ksep/K))) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_fixedField_openSubgroup]
    exact U.isOpen)

theorem index_openSubgroup (U : OpenSubgroup Gal(Ksep/K)) :
    (U : Subgroup Gal(Ksep/K)).index = Module.finrank K (fixedField (U : Subgroup Gal(Ksep/K))) := by
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField_openSubgroup]

omit [IsGalois K Ksep] in

theorem fixedField_le_fixedField {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) :
    fixedField (U : Subgroup Gal(Ksep/K)) ≤ fixedField (V : Subgroup Gal(Ksep/K)) :=
  fun _ hx => (mem_fixedField_iff _ _).2 fun σ hσ => (mem_fixedField_iff _ _).1 hx σ (h hσ)

theorem relIndex_eq_finrank {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    (V : Subgroup Gal(Ksep/K)).relIndex U =
      Module.finrank (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K))) := by
  let _ := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower K (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := Subgroup.relIndex_mul_index (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)
  rw [index_openSubgroup, index_openSubgroup, ← Module.finrank_mul_finrank K
    (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K))), mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

def galFixedFieldToOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) →* (U : Subgroup Gal(Ksep/K)) :=
  (AlgEquiv.restrictScalarsHom K).codRestrict (U : Subgroup Gal(Ksep/K)) fun σ =>
    (fixingSubgroup_fixedField_openSubgroup U).le
      ((mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩)

@[simp]
theorem coe_galFixedFieldToOpen_apply (U : OpenSubgroup Gal(Ksep/K))
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) (x : Ksep) :
    ((galFixedFieldToOpen U σ : Gal(Ksep/K)) : Ksep → Ksep) x = σ x :=
  rfl

theorem continuous_galFixedFieldToOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Continuous (galFixedFieldToOpen U) :=
  (continuous_restrictScalarsHom_of_tower K (fixedField (U : Subgroup Gal(Ksep/K))) Ksep).subtype_mk _

theorem galFixedFieldToOpen_bijective (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Bijective (galFixedFieldToOpen U) := by
  refine ⟨fun σ τ h => AlgEquiv.ext fun x => ?_, fun τ => ?_⟩
  · exact congrArg (fun ρ : (U : Subgroup Gal(Ksep/K)) => (ρ : Gal(Ksep/K)) x) h
  · have hτ : (τ : Gal(Ksep/K)) ∈ (fixedField (U : Subgroup Gal(Ksep/K))).fixingSubgroup :=
      (fixingSubgroup_fixedField_openSubgroup U).ge τ.2
    refine ⟨fixingSubgroupEquiv _ ⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun x => rfl)⟩

noncomputable def galFixedFieldEquivOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) ≃* (U : Subgroup Gal(Ksep/K)) :=
  MulEquiv.ofBijective (galFixedFieldToOpen U) (galFixedFieldToOpen_bijective U)

theorem galFixedFieldEquivOpen_toMonoidHom (U : OpenSubgroup Gal(Ksep/K)) :
    (galFixedFieldEquivOpen U).toMonoidHom = galFixedFieldToOpen U :=
  rfl

theorem continuous_galFixedFieldEquivOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Continuous (galFixedFieldEquivOpen U).toMonoidHom :=
  continuous_galFixedFieldToOpen U

theorem continuous_galFixedFieldEquivOpen_symm (U : OpenSubgroup Gal(Ksep/K)) :
    Continuous (galFixedFieldEquivOpen U).symm.toMonoidHom := by
  have : IsGalois (fixedField (U : Subgroup Gal(Ksep/K))) Ksep :=
    IsGalois.tower_top_of_isGalois K _ Ksep
  exact (Continuous.homeoOfEquivCompactToT2 (f := (galFixedFieldEquivOpen U).toEquiv)
    (continuous_galFixedFieldToOpen U)).symm.continuous

instance isDiscreteRep_res_openSubgroup_galUnits (U : OpenSubgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) :=
  isDiscreteRep_res_subtype _ _

noncomputable def galUnitsOpenHom (U : OpenSubgroup Gal(Ksep/K)) :
    Rep.res (galFixedFieldEquivOpen U).toMonoidHom
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) ⟶
      galUnits.{0} (fixedField (U : Subgroup Gal(Ksep/K))) Ksep :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ksepˣ) (B := Additive Ksepˣ) (AddMonoidHom.id _),
    fun σ => by
      ext x
      rfl⟩

theorem galUnitsOpenHom_bijective (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Bijective (galUnitsOpenHom U).hom :=
  Function.bijective_id

noncomputable def openCohomologyIso (U : OpenSubgroup Gal(Ksep/K)) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) n ≅
      cohomology (galUnits.{0} (fixedField (U : Subgroup Gal(Ksep/K))) Ksep) n :=
  haveI := isIso_cohomologyMapAlong_of_mulEquiv (galFixedFieldEquivOpen U)
    (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U)
    (galUnitsOpenHom U) (galUnitsOpenHom_bijective U) n
  asIso (cohomologyMapAlong (galFixedFieldEquivOpen U).toMonoidHom
    (continuous_galFixedFieldEquivOpen U) (galUnitsOpenHom U) n)

theorem openCohomologyIso_hom (U : OpenSubgroup Gal(Ksep/K)) (n : ℕ) :
    (openCohomologyIso U n).hom = cohomologyMapAlong (galFixedFieldEquivOpen U).toMonoidHom
      (continuous_galFixedFieldEquivOpen U) (galUnitsOpenHom U) n :=
  rfl

theorem cohomologyResLE_comp_openCohomologyIso {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) (n : ℕ) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    haveI : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K)))
        (fixedField (V : Subgroup Gal(Ksep/K))) Ksep := IsScalarTower.of_algebraMap_eq' rfl
    cohomologyResLE (galUnits.{0} K Ksep) (show (V : Subgroup Gal(Ksep/K)) ≤ U from h) n ≫
        (openCohomologyIso V n).hom =
      (openCohomologyIso U n).hom ≫
        cohomologyMapAlong (AlgEquiv.restrictScalarsHom (fixedField (U : Subgroup Gal(Ksep/K))))
          (continuous_restrictScalarsHom_of_tower _ _ Ksep) (galUnitsResScalars _ _ Ksep) n := by
  let _ := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K)))
      Ksep := IsScalarTower.of_algebraMap_eq' rfl
  rw [openCohomologyIso_hom, openCohomologyIso_hom, cohomologyResLE, ← cohomologyMapAlong_comp,
    ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _
    (MonoidHom.ext fun σ => Subtype.ext (AlgEquiv.ext fun x => rfl)) (fun _ => rfl) n

end Open

section Formation

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  [ValuativeRel Ksep] [TopologicalSpace Ksep] [IsValuativeTopology Ksep] [ValuativeExtension K Ksep]

noncomputable def localInv (U : OpenSubgroup Gal(Ksep/K)) : H2Open (galUnits.{0} K Ksep) U →+ QZ :=
  (brauerInv (fixedField (U : Subgroup Gal(Ksep/K))) Ksep).comp
    (openCohomologyIso U 2).hom.hom.toAddMonoidHom

theorem localInv_apply (U : OpenSubgroup Gal(Ksep/K)) (x : H2Open (galUnits.{0} K Ksep) U) :
    localInv K Ksep U x =
      brauerInv (fixedField (U : Subgroup Gal(Ksep/K))) Ksep ((openCohomologyIso U 2).hom.hom x) :=
  AddMonoidHom.comp_apply _ _ x

theorem localInv_bijective (U : OpenSubgroup Gal(Ksep/K)) : Function.Bijective (localInv K Ksep U) :=
  (brauerInv_bijective _ Ksep).comp
    ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ksep]
  [TopologicalSpace Ksep] [IsValuativeTopology Ksep] [ValuativeExtension K Ksep] in

theorem isZero_H1_open (U : OpenSubgroup Gal(Ksep/K)) :
    Limits.IsZero (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) 1) :=
  (isZero_cohomology_one_galUnits (K := fixedField (U : Subgroup Gal(Ksep/K))) (L := Ksep)).of_iso
    (openCohomologyIso U 1)

theorem localInv_res (U V : OpenSubgroup Gal(Ksep/K)) (h : V ≤ U) (x : H2Open (galUnits.{0} K Ksep) U) :
    localInv K Ksep V ((cohomologyResLE (galUnits.{0} K Ksep) (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)
      2).hom x) = (V : Subgroup Gal(Ksep/K)).relIndex U • localInv K Ksep U x := by
  let _ := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K)))
      Ksep := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := Module.Finite.of_restrictScalars_finite K _ _
  have : ValuativeExtension (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) :=
    IntermediateField.valuativeExtension_inclusion (fixedField_le_fixedField h)
  have hsq := congrArg (fun φ => φ.hom x) (cohomologyResLE_comp_openCohomologyIso h 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
  rw [localInv_apply, localInv_apply, hsq, ← brauerRes_eq, brauerInv_brauerRes,
    relIndex_eq_finrank h]

noncomputable def localClassFormation : ClassFormation (galUnits.{0} K Ksep) where
  inv := localInv K Ksep
  isZero_H1_open_subgroups := isZero_H1_open K Ksep
  inv_res := localInv_res K Ksep
  inv_bijective := localInv_bijective K Ksep

theorem localClassFormation_inv (U : OpenSubgroup Gal(Ksep/K)) :
    (localClassFormation K Ksep).inv U = localInv K Ksep U := by
  simp only [localClassFormation]

end Formation

section SepClosure

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

noncomputable def localClassFormationOfIsSepClosure : ClassFormation (galUnits.{0} K Ksep) :=
  letI := algebraicValuativeRel K Ksep
  letI := algebraicTopology K Ksep
  haveI := algebraicTopology_isValuativeTopology K Ksep
  haveI := algebraicValuativeRel_valuativeExtension K Ksep
  localClassFormation K Ksep

end SepClosure

end GroundTheory.ProfCoh

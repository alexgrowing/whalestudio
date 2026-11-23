import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassSplit
import GroundTheory.ProfiniteCohomology.ClassFormationDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

def openSubgroupMap (U : OpenSubgroup K.1.fixingSubgroup) : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
  ⟨(U : Subgroup K.1.fixingSubgroup).map K.1.fixingSubgroup.subtype, by
    have hK : IsOpen (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := K.1.fixingSubgroup_isOpen
    have := hK.isOpenMap_subtype_val _ U.isOpen
    convert this using 1
    ext x
    simp⟩

theorem coe_openSubgroupMap (U : OpenSubgroup K.1.fixingSubgroup) :
    (openSubgroupMap U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) =
      (U : Subgroup K.1.fixingSubgroup).map K.1.fixingSubgroup.subtype :=
  rfl

def fieldOf (U : OpenSubgroup K.1.fixingSubgroup) : FiniteSubfield :=
  ofOpenSubgroup (openSubgroupMap U)

theorem fixingSubgroup_fieldOf (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup = (U : Subgroup K.1.fixingSubgroup).map K.1.fixingSubgroup.subtype :=
  fixingSubgroup_ofOpenSubgroup (openSubgroupMap U)

theorem fixingSubgroup_fieldOf_le (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup ≤ K.1.fixingSubgroup := by
  rw [fixingSubgroup_fieldOf]
  rintro _ ⟨g, _, rfl⟩
  exact g.2

instance fact_le_fieldOf (U : OpenSubgroup K.1.fixingSubgroup) : Fact (K ≤ fieldOf U) :=
  ⟨by
    have h := IntermediateField.fixedField_antitone (fixingSubgroup_fieldOf_le U)
    rwa [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at h⟩

theorem subgroupOf_fieldOf (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup.subgroupOf K.1.fixingSubgroup = U := by
  rw [fixingSubgroup_fieldOf, Subgroup.subgroupOf]
  exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem fieldOf_le_fieldOf {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) : fieldOf U ≤ fieldOf V := by
  have hle : (fieldOf V).1.fixingSubgroup ≤ (fieldOf U).1.fixingSubgroup := by
    rw [fixingSubgroup_fieldOf, fixingSubgroup_fieldOf]
    exact Subgroup.map_mono h
  have h' := IntermediateField.fixedField_antitone hle
  rwa [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at h'

def openEquiv (U : OpenSubgroup K.1.fixingSubgroup) : (U : Subgroup K.1.fixingSubgroup) ≃* (fieldOf U).1.fixingSubgroup :=
  (MulEquiv.subgroupCongr (subgroupOf_fieldOf U).symm).trans
    (Subgroup.subgroupOfEquivOfLe (fixingSubgroup_fieldOf_le U))

@[simp]
theorem coe_openEquiv_apply (U : OpenSubgroup K.1.fixingSubgroup) (g : (U : Subgroup K.1.fixingSubgroup)) :
    ((openEquiv U g : (fieldOf U).1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) = ((g : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
  rfl

theorem continuous_openEquiv (U : OpenSubgroup K.1.fixingSubgroup) : Continuous (openEquiv U).toMonoidHom :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem continuous_openEquiv_symm (U : OpenSubgroup K.1.fixingSubgroup) :
    Continuous (openEquiv U).symm.toMonoidHom :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

def classOpenMor (U : OpenSubgroup K.1.fixingSubgroup) :
    Rep.res (openEquiv U).symm.toMonoidHom (Rep.res (U : Subgroup K.1.fixingSubgroup).subtype (classLimitRep K)) ⟶
      classLimitRep (fieldOf U) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def classOpenIso (U : OpenSubgroup K.1.fixingSubgroup) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup K.1.fixingSubgroup).subtype (classLimitRep K)) n ≅
      cohomology (classLimitRep (fieldOf U)) n :=
  haveI := isIso_cohomologyMapAlong_of_mulEquiv (openEquiv U).symm (continuous_openEquiv_symm U)
    (continuous_openEquiv U) (classOpenMor U) Function.bijective_id n
  asIso (cohomologyMapAlong (openEquiv U).symm.toMonoidHom (continuous_openEquiv_symm U) (classOpenMor U) n)

theorem cohomologyResLE_classOpenIso {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) (n : ℕ) :
    haveI : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
    cohomologyResLE (classLimitRep K) (show (V : Subgroup K.1.fixingSubgroup) ≤ U from h) n ≫
        (classOpenIso V n).hom =
      (classOpenIso U n).hom ≫ classResField (fieldOf U) (fieldOf V) n := by
  have : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
  rw [classOpenIso, classOpenIso, asIso_hom, asIso_hom, cohomologyResLE, classResField,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun g => Subtype.ext (Subtype.ext rfl)) (fun _ => rfl) n

theorem relIndex_eq_finrank_fieldOf {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) :
    letI := algebraOfLE (fieldOf_le_fieldOf h)
    (V : Subgroup K.1.fixingSubgroup).relIndex U = Module.finrank (fieldOf U).1 (fieldOf V).1 := by
  have := relIndex_fixingSubgroup (fieldOf_le_fieldOf h)
  rw [fixingSubgroup_fieldOf, fixingSubgroup_fieldOf,
    Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective] at this
  exact this

end

end GroundTheory.ProfCoh

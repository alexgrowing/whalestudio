import Mathlib
import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply

namespace GroundTheory.ProfCoh

open IntermediateField InfiniteGalois

universe u

variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]

section FixingSubgroup

theorem isOpen_fixingSubgroup_finiteGalois (E : FiniteGaloisIntermediateField K L) :
    IsOpen (E.fixingSubgroup : Set Gal(L/K)) :=
  fixingSubgroup_isOpen E.toIntermediateField

theorem normal_fixingSubgroup_finiteGalois [IsGalois K L] (E : FiniteGaloisIntermediateField K L) :
    E.fixingSubgroup.Normal :=
  (normal_iff_isGalois E.toIntermediateField).2 E.isGalois

variable [IsGalois K L]

def fixingOpenNormalSubgroup (E : FiniteGaloisIntermediateField K L) :
    OpenNormalSubgroup Gal(L/K) where
  toSubgroup := E.fixingSubgroup
  isOpen' := isOpen_fixingSubgroup_finiteGalois E
  isNormal' := normal_fixingSubgroup_finiteGalois E

@[simp]
theorem coe_fixingOpenNormalSubgroup
    (E : FiniteGaloisIntermediateField K L) :
    (fixingOpenNormalSubgroup E : Subgroup Gal(L/K)) = E.fixingSubgroup :=
  rfl

end FixingSubgroup

section FixedField

variable [IsGalois K L] (U : OpenNormalSubgroup Gal(L/K))

def openNormalToClosed : ClosedSubgroup Gal(L/K) :=
  ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩

instance : (openNormalToClosed U).Normal :=
  U.isNormal'

@[simp]
theorem fixingSubgroup_fixedField_openNormalSubgroup :
    (fixedField (U : Subgroup Gal(L/K))).fixingSubgroup = U :=
  fixingSubgroup_fixedField (openNormalToClosed U)

instance finiteDimensional_fixedField_openNormalSubgroup :
    FiniteDimensional K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (isOpen_iff_finite _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isOpen

instance isGalois_fixedField_openNormalSubgroup :
    IsGalois K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (normal_iff_isGalois _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isNormal'

noncomputable def fixedFiniteGalois : FiniteGaloisIntermediateField K L where
  toIntermediateField := fixedField (U : Subgroup Gal(L/K))

@[simp]
theorem fixedFiniteGalois_toIntermediateField :
    (fixedFiniteGalois U).toIntermediateField = fixedField (U : Subgroup Gal(L/K)) :=
  rfl

noncomputable def quotientEquivGal :
    Gal(L/K) ⧸ (U : Subgroup Gal(L/K)) ≃* Gal(fixedField (U : Subgroup Gal(L/K))/K) :=
  normalAutEquivQuotient (openNormalToClosed U)

@[simp]
theorem quotientEquivGal_mk_apply (σ : Gal(L/K)) (x : fixedField (U : Subgroup Gal(L/K))) :
    ((quotientEquivGal U (σ : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) x : _) : L) = σ x :=
  AlgEquiv.restrictNormal_commutes σ _ x

omit [IsGalois K L] in

theorem mem_invariants_galAdd_iff (x : L) :
    x ∈ Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ↔
      x ∈ fixedField (U : Subgroup Gal(L/K)) :=
  ⟨fun h σ => h σ, fun h σ => h σ⟩

omit [IsGalois K L] in

def invariantsGalAddEquiv :
    Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ≃ₗ[K]
      fixedField (U : Subgroup Gal(L/K)) where
  toFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).1 x.2⟩
  invFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem invariantsGalAddEquiv_quotientToInvariants (q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
    (x : Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    invariantsGalAddEquiv U (((galAdd K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q x) =
      quotientEquivGal U q (invariantsGalAddEquiv U x) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply Subtype.ext
    rw [quotientEquivGal_mk_apply]
    rfl

end FixedField

section Correspondence

variable [IsGalois K L]

@[simp]
theorem fixingOpenNormalSubgroup_fixedFiniteGalois
    (U : OpenNormalSubgroup Gal(L/K)) : fixingOpenNormalSubgroup (fixedFiniteGalois U) = U := by
  ext σ
  change σ ∈ (fixedField (U : Subgroup Gal(L/K))).fixingSubgroup ↔ σ ∈ (U : Subgroup Gal(L/K))
  rw [fixingSubgroup_fixedField_openNormalSubgroup]

@[simp]
theorem fixedFiniteGalois_fixingOpenNormalSubgroup
    (E : FiniteGaloisIntermediateField K L) : fixedFiniteGalois (fixingOpenNormalSubgroup E) = E :=
  FiniteGaloisIntermediateField.val_injective (fixedField_fixingSubgroup E.toIntermediateField)

noncomputable def openNormalSubgroupEquiv :
    OpenNormalSubgroup Gal(L/K) ≃o (FiniteGaloisIntermediateField K L)ᵒᵈ where
  toFun U := OrderDual.toDual (fixedFiniteGalois U)
  invFun E := fixingOpenNormalSubgroup (OrderDual.ofDual E)
  left_inv U := fixingOpenNormalSubgroup_fixedFiniteGalois U
  right_inv E := fixedFiniteGalois_fixingOpenNormalSubgroup (OrderDual.ofDual E)
  map_rel_iff' {U V} := by
    change fixedField (V : Subgroup Gal(L/K)) ≤ fixedField (U : Subgroup Gal(L/K)) ↔ U ≤ V
    rw [le_iff_le, fixingSubgroup_fixedField_openNormalSubgroup]
    exact Iff.rfl

@[simp]
theorem openNormalSubgroupEquiv_apply (U : OpenNormalSubgroup Gal(L/K)) :
    (OrderDual.ofDual (openNormalSubgroupEquiv U)).toIntermediateField =
      fixedField (U : Subgroup Gal(L/K)) :=
  rfl

@[simp]
theorem coe_openNormalSubgroupEquiv_symm_apply (E : FiniteGaloisIntermediateField K L) :
    ((openNormalSubgroupEquiv.symm (OrderDual.toDual E) : OpenNormalSubgroup Gal(L/K)) :
      Subgroup Gal(L/K)) = E.fixingSubgroup :=
  rfl

end Correspondence

section Cofinal

variable [IsGalois K L]

theorem exists_finiteGalois_le (E : IntermediateField K L) [FiniteDimensional K E] :
    ∃ F : FiniteGaloisIntermediateField K L, E ≤ F.toIntermediateField :=
  ⟨{ toIntermediateField := normalClosure K E L
     finiteDimensional := normalClosure.is_finiteDimensional K E L
     isGalois := IsGalois.normalClosure K E L }, le_normalClosure E⟩

theorem exists_finiteGalois_mem (x : L) :
    ∃ F : FiniteGaloisIntermediateField K L, x ∈ F.toIntermediateField :=
  ⟨FiniteGaloisIntermediateField.adjoin K {x},
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩

end Cofinal

end GroundTheory.ProfCoh

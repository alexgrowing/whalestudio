import Mathlib
import GroundTheory.GlobalFields.IdeleClassGroup.Theory
import GroundTheory.GlobalFields.NormResidueSymbol.Cyclotomic
import GroundTheory.LocalFields.AbstractLocalReciprocity.Isomorphism

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract
open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace FiniteSubfield

abbrev openSubgroup (F : FiniteSubfield) : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
  ⟨F.1.fixingSubgroup, F.1.fixingSubgroup_isOpen⟩

@[simp]
theorem coe_openSubgroup (F : FiniteSubfield) :
    (F.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = F.1.fixingSubgroup :=
  rfl

theorem openSubgroup_le {F E : FiniteSubfield} (h : F ≤ E) : E.openSubgroup ≤ F.openSubgroup :=
  fun _ hx ↦ IntermediateField.fixingSubgroup_le (show F.1 ≤ E.1 from h) hx

variable (F E : FiniteSubfield) [Fact (F ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal]

instance normal_openSubgroup :
    ((E.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf F.openSubgroup).Normal :=
  ‹(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal›

def quotientGaloisEquiv :
    ((F.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ⧸
        (E.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf F.openSubgroup) ≃*
      (E.1 ≃ₐ[F.1] E.1) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_restrictHom (F := F) (E := E)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictHom_surjective (F := F) (E := E)))

@[simp]
theorem quotientGaloisEquiv_mk (g : F.1.fixingSubgroup) :
    quotientGaloisEquiv F E
        (QuotientGroup.mk (s := (E.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf F.openSubgroup) g) =
      restrictHom g :=
  rfl

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic

section Map

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

abbrev reciprocityEquiv :
    Abelianization ((K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ⧸
        (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf K.openSubgroup) ≃*
      tateZero IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup :=
  classFieldTheory.toClassFieldData.reciprocityAbEquiv (openSubgroup_le hKL.out)
    classFieldTheory.classFieldAxiom

abbrev normClass : IdeleClassGroup K.1 →*
    tateZero IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup :=
  (QuotientGroup.mk' (norm IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).range).comp (fixedEquiv K).toMonoidHom

def abstractSymbol : IdeleClassGroup K.1 →* Abelianization (L.1 ≃ₐ[K.1] L.1) :=
  (Abelianization.map (quotientGaloisEquiv K L).toMonoidHom).comp
    ((reciprocityEquiv K L).symm.toMonoidHom.comp (normClass K L))

theorem abstractSymbol_apply (c : IdeleClassGroup K.1) :
    abstractSymbol K L c = Abelianization.map (quotientGaloisEquiv K L).toMonoidHom
      ((reciprocityEquiv K L).symm (normClass K L c)) :=
  rfl

theorem abstractSymbol_eq_of_reciprocity (c : IdeleClassGroup K.1) (g : K.1.fixingSubgroup)
    (h : classFieldTheory.toClassFieldData.reciprocity (openSubgroup_le hKL.out)
        classFieldTheory.classFieldAxiom
        (QuotientGroup.mk (s := (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf K.openSubgroup) g) =
      normClass K L c) :
    abstractSymbol K L c = Abelianization.of (restrictHom g) := by
  have e : (reciprocityEquiv K L).symm (normClass K L c) =
      Abelianization.of (QuotientGroup.mk (s := (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf
        K.openSubgroup) g) := by
    rw [MulEquiv.symm_apply_eq, ClassFieldData.reciprocityAbEquiv_of]
    exact h.symm
  rw [abstractSymbol_apply, e, Abelianization.map_of]
  rfl

end Map

section Layers

variable (K L : FiniteSubfield)

theorem inf_ker_degree_le_of_le_sup_zhatField (hL : L.1 ≤ K.1 ⊔ zhatField) :
    K.1.fixingSubgroup ⊓ degree.ker ≤ L.1.fixingSubgroup := by
  rw [← fixingSubgroup_zhatField, ← IntermediateField.fixingSubgroup_sup]
  exact IntermediateField.fixingSubgroup_le hL

theorem normal_of_le_sup_zhatField (hKL : K ≤ L) (hL : L.1 ≤ K.1 ⊔ zhatField) :
    (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal :=
  normal_of_unramified (d := degree)
    (IntermediateField.fixingSubgroup_le (show K.1 ≤ L.1 from hKL))
    (inf_ker_degree_le_of_le_sup_zhatField K L hL)

variable [Fact (K ≤ L)] [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem isMulCommutative_of_le_sup_zhatField (hL : L.1 ≤ K.1 ⊔ zhatField) :
    IsMulCommutative (L.1 ≃ₐ[K.1] L.1) := by
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := L) σ
  obtain ⟨h, rfl⟩ := restrictHom_surjective (F := K) (E := L) τ
  have hk : (h * g)⁻¹ * (g * h) ∈ (restrictHom (F := K) (E := L)).ker := by
    rw [ker_restrictHom, Subgroup.mem_subgroupOf]
    refine inf_ker_degree_le_of_le_sup_zhatField K L hL ⟨((h * g)⁻¹ * (g * h)).2, MonoidHom.mem_ker.2 ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [mul_comm (degree (h : ℚ̄ ≃ₐ[ℚ] ℚ̄)) (degree (g : ℚ̄ ≃ₐ[ℚ] ℚ̄))]
    exact inv_mul_cancel _
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
  rw [← map_mul, ← map_mul]
  exact hk.symm

end Layers

end IdeleClassLimit

end

end GroundTheory.Global

import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.InfKerDegreeLeOfLeSupZhatField

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract IdeleGroup
open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic ProfiniteInteger

theorem val_norm_fixedEquiv (K : FiniteSubfield) (a : IdeleClassGroup K.1) :
    val (norm IdeleClassLimit ⊤ K.1.fixingSubgroup (fixedEquiv K a)) = cycDegree (cycSymbol K a) := by
  have h := val_norm_of (U := K.1.fixingSubgroup) rfl a (fixedEquiv K a).2
  convert h using 3
  exact Subtype.ext (coe_fixedEquiv K a)

theorem degree_eq_valuation_pow (K : FiniteSubfield) (a : IdeleClassGroup K.1) {g : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hg : cycRestrict g = cycSymbol K a) :
    classFieldTheory.deg g =
      classFieldTheory.valuation K.openSubgroup (fixedEquiv K a) ^
        inertiaDegree classFieldTheory.deg (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
  have h3 : degree g = cycDegree (cycSymbol K a) := by
    rw [← hg, ← MonoidHom.comp_apply, cycDegree_comp_cycRestrict]
  rw [classFieldTheory.valuation_pow K.openSubgroup (fixedEquiv K a)]
  convert h3.trans (val_norm_fixedEquiv K a).symm using 2
  · exact classFieldTheory_deg
  · rfl

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem abstractSymbol_eq_of_cycRestrict_eq (hL : L.1 ≤ K.1 ⊔ zhatField) (a : IdeleClassGroup K.1)
    (g : K.1.fixingSubgroup) (hg : cycRestrict (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = cycSymbol K a) :
    abstractSymbol K L a = Abelianization.of (restrictHom g) := by
  set D := classFieldTheory.toClassFieldData
  have hLK : L.openSubgroup ≤ K.openSubgroup := openSubgroup_le hKL.out
  have hu : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ⊓ D.deg.ker ≤ L.openSubgroup :=
    inf_ker_degree_le_of_le_sup_zhatField K L hL
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K.openSubgroup (Multiplicative.ofAdd 1)
  have hr := D.reciprocityAbEquiv_symm_of_unramified hLK classFieldTheory.classFieldAxiom hu hφ
    (fixedEquiv K a)
  set f := D.relInertiaDegreePNat hLK with hf
  set z := Multiplicative.toAdd (D.valuation K.openSubgroup (fixedEquiv K a)) with hz
  set n := (proj f z).val with hn

  obtain ⟨y, hy⟩ : ∃ y : ℤ̂, z - (n : ℤ̂) = (f : ℕ) • y := by
    refine exists_eq_nsmul_of_proj_eq_zero ?_
    rw [map_sub, map_natCast, hn, ZMod.natCast_zmod_val, sub_self]

  have hmem : ((φ ^ n)⁻¹ * g : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))) ∈
      (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf K.openSubgroup := by
    rw [Subgroup.mem_subgroupOf, mem_iff_map_mem_of_unramified (d := D.deg) hLK hu
      ((φ ^ n)⁻¹ * g : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).2,
      D.mem_map_deg_iff L.openSubgroup]
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    have hφd : D.deg φ = Multiplicative.ofAdd 1 ^ inertiaDegree D.deg
        (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      rw [← D.relDeg_pow K.openSubgroup φ, hφ]
    have hgd : D.deg g = D.valuation K.openSubgroup (fixedEquiv K a) ^
        inertiaDegree D.deg (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
      degree_eq_valuation_pow K a hg
    rw [inertiaDegree_eq_mul D.surjective_deg hLK]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, map_mul, map_inv, map_pow]
    rw [hφd, show D.deg (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = _ from hgd]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_mul, toAdd_inv, toAdd_ofAdd]
    change _ = _ + _ • z
    rw [sub_eq_iff_eq_add'.1 hy, hf, ClassFieldData.coe_relInertiaDegreePNat]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  have e : (reciprocityEquiv K L).symm (normClass K L a) =
      Abelianization.of (QuotientGroup.mk (s := (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf
        K.openSubgroup) g) := by
    refine hr.trans ?_
    rw [← map_pow, ← QuotientGroup.mk_pow]
    exact congrArg _ (QuotientGroup.eq.2 hmem)
  rw [abstractSymbol_apply, e, Abelianization.map_of]
  rfl

theorem abstractSymbol_mk_of_le_sup_zhatField [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]
    (hL : L.1 ≤ K.1 ⊔ zhatField) (x : IdeleGroup K.1) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 x) = Abelianization.of (ideleSymbol K.1 L.1 x) := by
  obtain ⟨g, hgK, hg⟩ := exists_mem_fixingSubgroup_cycRestrict_eq K (IdeleClassGroup.mk K.1 x)
  rw [abstractSymbol_eq_of_cycRestrict_eq K L hL _ ⟨g, hgK⟩ hg,
    restrictHom_eq_ideleSymbol_of_le_sup K L (hL.trans (sup_le_sup_left zhatField_le_maxCyclotomic _))
      ⟨g, hgK⟩ x hg]

theorem range_diagonal_le_ker_ideleSymbol_of_le_sup_zhatField [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]
    (hL : L.1 ≤ K.1 ⊔ zhatField) : (diagonal K.1).range ≤ (ideleSymbol K.1 L.1).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal_eq_one_of_le_sup K L
    (hL.trans (sup_le_sup_left zhatField_le_maxCyclotomic _)) a

theorem abstractSymbol_eq_ideleClassSymbol [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]
    (hL : L.1 ≤ K.1 ⊔ zhatField) :
    abstractSymbol K L = Abelianization.of.comp (ideleClassSymbol L.1
      (range_diagonal_le_ker_ideleSymbol_of_le_sup_zhatField K L hL)) := by
  refine MonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K.1 c
  rw [MonoidHom.comp_apply, ideleClassSymbol_mk, abstractSymbol_mk_of_le_sup_zhatField K L hL]

end IdeleClassLimit

end

end GroundTheory.Global

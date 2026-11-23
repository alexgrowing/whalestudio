import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.InfKerDegreeLeOfLeSupZhatField
import GroundTheory.LocalFields.AbstractLocalReciprocity.Functoriality
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract
open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield

section Kernel

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

omit [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] in

theorem normClass_ideleClassNorm (c : IdeleClassGroup L.1) :
    normClass K L (FiniteSubfield.ideleClassNorm hKL.out c) = 1 := by
  change (QuotientGroup.mk (fixedEquiv K (FiniteSubfield.ideleClassNorm hKL.out c)) :
    tateZero IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup) = 1
  rw [QuotientGroup.eq_one_iff, ← norm_fixedEquiv hKL.out c]
  exact ⟨_, rfl⟩

theorem abstractSymbol_ideleClassNorm_eq_one (c : IdeleClassGroup L.1) :
    abstractSymbol K L (FiniteSubfield.ideleClassNorm hKL.out c) = 1 := by
  rw [abstractSymbol_apply, normClass_ideleClassNorm, map_one, map_one]

theorem exists_abstractSymbol_eq (c : IdeleClassGroup K.1) :
    ∃ g : K.1.fixingSubgroup, abstractSymbol K L c = Abelianization.of (restrictHom g) := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (abstractSymbol K L c)
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := L) σ
  exact ⟨g, hσ.symm⟩

end Kernel

section Square

variable {K L K' L' : FiniteSubfield} [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [hKL' : Fact (K' ≤ L')]
  [(L'.1.fixingSubgroup.subgroupOf K'.1.fixingSubgroup).Normal]

omit [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]
  [(L'.1.fixingSubgroup.subgroupOf K'.1.fixingSubgroup).Normal] in

theorem normTateZero_normClass (hK : K ≤ K') (hL : L ≤ L') (c : IdeleClassGroup K'.1) :
    normTateZero (openSubgroup_le hK) (openSubgroup_le hL) (openSubgroup_le hKL'.out)
        (openSubgroup_le hKL.out) (normClass K' L' c) =
      normClass K L (FiniteSubfield.ideleClassNorm hK c) := by
  change normTateZero (openSubgroup_le hK) (openSubgroup_le hL) (openSubgroup_le hKL'.out)
      (openSubgroup_le hKL.out) (QuotientGroup.mk (fixedEquiv K' c)) =
    QuotientGroup.mk (fixedEquiv K (FiniteSubfield.ideleClassNorm hK c))
  rw [normTateZero_mk]
  exact congrArg _ (norm_fixedEquiv hK c)

theorem abstractSymbol_ideleClassNorm (hK : K ≤ K') (hL : L ≤ L') (c : IdeleClassGroup K'.1)
    (g : K'.1.fixingSubgroup) (hg : abstractSymbol K' L' c = Abelianization.of (restrictHom g)) :
    abstractSymbol K L (FiniteSubfield.ideleClassNorm hK c) =
      Abelianization.of (restrictHom (⟨g, IntermediateField.fixingSubgroup_le
        (show K.1 ≤ K'.1 from hK) g.2⟩ : K.1.fixingSubgroup)) := by
  set D := classFieldTheory.toClassFieldData
  have e : (reciprocityEquiv K' L').symm (normClass K' L' c) =
      Abelianization.of (QuotientGroup.mk (s := (L'.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf
        K'.openSubgroup) g) := by
    apply (quotientGaloisEquiv K' L').abelianizationCongr.injective
    rw [abelianizationCongr_of, quotientGaloisEquiv_mk]
    exact hg
  rw [abstractSymbol_apply, ← normTateZero_normClass hK hL c]
  have h2 := D.reciprocityAbEquiv_symm_normTateZero classFieldTheory.classFieldAxiom
    (openSubgroup_le hKL.out) (openSubgroup_le hKL'.out) (openSubgroup_le hK) (openSubgroup_le hL)
    (normClass K' L' c)
  rw [h2, e, Abelianization.map_of, Abelianization.map_of, galRestrict_mk]
  rfl

instance isScalarTower_of_fact {F E M : FiniteSubfield} [Fact (F ≤ E)] [Fact (E ≤ M)] [Fact (F ≤ M)] :
    IsScalarTower F.1 E.1 M.1 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

theorem abstractSymbol_ideleClassNorm_eq_map [hK : Fact (K ≤ K')] [Fact (L ≤ L')] [Fact (K ≤ L')]
    (c : IdeleClassGroup K'.1) :
    abstractSymbol K L (FiniteSubfield.ideleClassNorm hK.out c) =
      Abelianization.map ((AlgEquiv.restrictNormalHom (F := K.1) (K₁ := L'.1) L.1).comp
        (restrictScalarsHom (L' := L'.1) K.1)) (abstractSymbol K' L' c) := by
  obtain ⟨g, hg⟩ := exists_abstractSymbol_eq K' L' c
  rw [abstractSymbol_ideleClassNorm hK.out (Fact.out : L ≤ L') c g hg, hg, Abelianization.map_of]
  congr 1
  refine AlgEquiv.ext fun x ↦ Subtype.ext ?_
  have h := congrArg (fun z : L'.1 ↦ (z : ℚ̄))
    (AlgEquiv.restrictNormal_commutes ((restrictHom g : L'.1 ≃ₐ[K'.1] L'.1).restrictScalars K.1) L.1 x)
  exact h.symm

end Square

end IdeleClassLimit

end

end GroundTheory.Global

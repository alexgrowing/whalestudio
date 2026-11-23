import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem trdeg_le_of_ringEquiv_square {K L K' L' : Type} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (f' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : f'.comp (eK : K →+* K') = (eL : L →+* L').comp f) :
    @Algebra.trdeg K L _ _ f.toAlgebra ≤ @Algebra.trdeg K' L' _ _ f'.toAlgebra := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr f.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  rw [← hs.cardinalMk_eq_trdeg]
  have hi : AlgebraicIndependent K' ((eL : L → L') ∘ ((↑) : s → L)) :=
    (algebraicIndependent_ringHom_iff_of_comp_eq eK (eL : L →+* L') eL.injective h).mpr hs.1
  simpa using hi.lift_cardinalMk_le_trdeg

theorem trdeg_eq_of_ringEquiv_square {K L K' L' : Type} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (f' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : f'.comp (eK : K →+* K') = (eL : L →+* L').comp f) :
    @Algebra.trdeg K L _ _ f.toAlgebra = @Algebra.trdeg K' L' _ _ f'.toAlgebra := by
  refine le_antisymm (trdeg_le_of_ringEquiv_square f f' eK eL h)
    (trdeg_le_of_ringEquiv_square f' f eK.symm eL.symm ?_)
  ext x
  have := congrArg (fun g => eL.symm (g (eK.symm x))) h
  simpa using this.symm

end GlobalTheory

namespace GlobalTheory
theorem ΓSpecIso_inv_germ_residue_residueFieldMap {R B : CommRingCat.{0}} (φ : R ⟶ B) (x : Spec B) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (Spec.map φ x) trivial ≫
        (Spec R).residue (Spec.map φ x) ≫ (Spec.map φ).residueFieldMap x =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ x trivial ≫ (Spec B).residue x := by
  rw [Scheme.residue_residueFieldMap]
  erw [Scheme.Hom.germ_stalkMap_assoc (Spec.map φ) ⊤ x trivial]
  have hn := Scheme.ΓSpecIso_naturality φ
  rw [← Category.assoc, ← Category.assoc φ]
  congr 1
  show (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop = φ ≫ (Scheme.ΓSpecIso B).inv
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
end GlobalTheory

namespace GlobalTheory

end GlobalTheory

namespace GlobalTheory

end GlobalTheory

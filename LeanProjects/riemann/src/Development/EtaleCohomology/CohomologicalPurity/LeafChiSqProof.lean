import Development.EtaleCohomology.CohomologicalPurity.LeafExcOfEqvPfSq

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem dblPO (A : Arrow Spc) : IsPushout A.hom A.hom (dbl.inl A) (dbl.inr A) :=
  IsPushout.of_hasPushout A.hom A.hom

theorem mmPO {P' P : Arrow Spc} (φ : P' ⟶ P) : IsPushout P'.hom (P'.hom ≫ φ.right) (ii φ) (jj φ) :=
  IsPushout.of_hasPushout _ _

theorem LeafChiSq_of : LeafChiSq := by
  intro P' P φ
  have s2 : IsPushout ((P'.hom ≫ φ.right) ≫ jj φ) P'.hom (dbl.inr (QQ φ)) (ii φ ≫ dbl.inl (QQ φ)) :=
    IsPushout.paste_horiz (mmPO φ).flip (dblPO (QQ φ)).flip
  have c : IsPushout P'.hom (P'.hom ≫ (chi φ).right) (dbl.inl P' ≫ dbl.map (chi φ)) (dbl.inr (QQ φ)) := by
    have e1 : P'.hom ≫ (chi φ).right = (P'.hom ≫ φ.right) ≫ jj φ := ij_cond φ
    have e2 : dbl.inl P' ≫ dbl.map (chi φ) = ii φ ≫ dbl.inl (QQ φ) := dinl_map (chi φ)
    rw [e1, e2]; exact s2.flip
  exact IsPushout.of_top c (dbl.inr_map (chi φ)) (dblPO P')
end LateralTheory.CohomologicalPurity.TubeCut

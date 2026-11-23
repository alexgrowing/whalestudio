import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding.EmbedOfLines
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.LineChartPf

attribute [local instance] MvPolynomial.gradedAlgebra

def eU : {j : Fin 2 // j ≠ 0} ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨1, by decide⟩
  left_inv := by
    rintro ⟨j, hj⟩
    apply Subtype.ext
    fin_cases j
    · exact absurd rfl hj
    · rfl
  right_inv := by intro; rfl

def awayEquiv : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ≃+* Polynomial ℤ :=
  (GlobalTheory.ProjSpace.polyEquivAway ℤ 1 0).symm.trans
    ((MvPolynomial.renameEquiv ℤ eU).trans (MvPolynomial.uniqueAlgEquiv ℤ PUnit.{1})).toRingEquiv

def projectiveLineAffineChartOverIntegers : Spec (CommRingCat.of (Polynomial ℤ)) ⟶ P1 :=
  Spec.map awayEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X 0)
      (MvPolynomial.isHomogeneous_X ℤ 0) one_pos

instance : IsOpenImmersion projectiveLineAffineChartOverIntegers := by
  unfold projectiveLineAffineChartOverIntegers
  haveI : IsIso (Spec.map awayEquiv.toCommRingCatIso.hom) := inferInstance
  haveI : IsOpenImmersion (Spec.map awayEquiv.toCommRingCatIso.hom) := IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp (Spec.map awayEquiv.toCommRingCatIso.hom) (Proj.awayι _ _ _ _)

def zIso : Spec (CommRingCat.of ℤ) ≅ ⊤_ Scheme := specZIsTerminal.uniqueUpToIso terminalIsTerminal

theorem tensor_C (R : Type) [CommRing R] (a : R) :
    (polyEquivTensor ℤ R).symm (a ⊗ₜ[ℤ] (1 : Polynomial ℤ)) = Polynomial.C a := by
  rw [polyEquivTensor_symm_apply_tmul, ← Polynomial.C_1, Polynomial.sum_C_index (by simp)]
  simp

theorem LineChart_of : LateralTheory.E.EmbedPf.LineChart := by
  intro L S l hl R _ j0 hj0
  obtain ⟨_, f, hsq⟩ := hl
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ))))
    (terminal.from S) (terminal.from P1) j0 projectiveLineAffineChartOverIntegers zIso.hom
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  let E := (polyEquivTensor ℤ R).toRingEquiv.toCommRingCatIso
  refine ⟨Spec.map E.inv ≫ (pullbackSpecIso ℤ R (Polynomial ℤ)).inv ≫ m ≫ hsq.flip.isoPullback.inv,
    inferInstance, ?_⟩
  simp only [Category.assoc, IsPullback.isoPullback_inv_fst, m, pullback.lift_fst,
    pullbackSpecIso_inv_fst_assoc]
  have key : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := R) (B := Polynomial ℤ)) ≫ E.inv =
      CommRingCat.ofHom Polynomial.C := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact tensor_C R a
  rw [← Spec.map_comp_assoc, key]

end LateralTheory.E.LineChartPf

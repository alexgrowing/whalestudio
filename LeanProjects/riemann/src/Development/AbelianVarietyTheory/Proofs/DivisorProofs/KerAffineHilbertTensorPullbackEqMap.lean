import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaApplyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionTensorPullbackRingHomBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertIdealSheafOfQuotientIdealTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertBaseChangeAppLECompSpecTensorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem ker_kappa_xI_comap : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.affineOpens), letI := (GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra; ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U ∧ RingHom.ker (GlobalTheory.HilbAff.kappa A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) ((GlobalTheory.HilbAff.xI A B C J).comap (GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)) := by
  intro A B C _ _ _ _ _ J Z h U
  letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        show secAlg C h U (algebraMap A C a) = secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U a
        rw [secAlg_comp]; rfl }
  refine ⟨φ, rfl, ?_⟩
  haveI : IsAffineHom (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ (U : Z.Opens)) :=
    U.2.preimage _
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) ⟨_, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine, GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, GlobalTheory.T.affineHilbertBaseChange_appLE_comp_specTensor A B C Z h U φ rfl, ← Ideal.map_map,
    Ideal.comap_map_of_bijective _ (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl

end GlobalTheory.HilbAff

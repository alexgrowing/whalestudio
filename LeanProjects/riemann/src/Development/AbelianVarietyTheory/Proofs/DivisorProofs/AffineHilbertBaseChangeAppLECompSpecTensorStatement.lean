import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertBaseChangeAppLECompSpecTensor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaApplyEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertBaseChange_appLE_comp_specTensor : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.Opens), letI := (GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra; ∀ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U → ((GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤ ((pullback.snd (GlobalTheory.HilbAff.str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp)).hom.comp (GlobalTheory.HilbAff.psi A B C) = (GlobalTheory.HilbAff.theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
  first | (exact @GlobalTheory.HilbAff.bc_appLE_comp_psi) | (exact GlobalTheory.HilbAff.bc_appLE_comp_psi) | (intros; apply GlobalTheory.HilbAff.bc_appLE_comp_psi <;> assumption)

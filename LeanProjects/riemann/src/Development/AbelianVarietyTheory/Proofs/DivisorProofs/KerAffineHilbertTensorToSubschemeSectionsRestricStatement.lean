import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U V : T.affineOpens) (h : (U : T.Opens) ≤ V), letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra; letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra; ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧ (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤ RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  first | (exact @GlobalTheory.HilbAff.kappa_res) | (exact GlobalTheory.HilbAff.kappa_res) | (intros; apply GlobalTheory.HilbAff.kappa_res  <;> assumption)

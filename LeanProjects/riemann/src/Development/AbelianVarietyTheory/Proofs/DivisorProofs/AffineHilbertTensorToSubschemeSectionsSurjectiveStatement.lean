import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.affineOpens), Function.Surjective (GlobalTheory.HilbAff.kappa A B g I U) := by
  first | (exact @GlobalTheory.HilbAff.kappa_surjective) | (exact GlobalTheory.HilbAff.kappa_surjective) | (intros; apply GlobalTheory.HilbAff.kappa_surjective  <;> assumption)

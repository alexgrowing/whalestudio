import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFinitePresentationOfEtaleCover
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_finite_presentation_of_etale_cover : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → LocallyOfFinitePresentation f := by
  first | (exact @GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale) | (exact GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale) | (intros; apply GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale  <;> assumption)

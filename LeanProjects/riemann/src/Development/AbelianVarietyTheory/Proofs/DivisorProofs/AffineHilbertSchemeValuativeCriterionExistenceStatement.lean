import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeValuativeCriterionExistence
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  first | (exact @GlobalTheory.HilbAff.valuativeExistence) | (exact GlobalTheory.HilbAff.valuativeExistence) | (intros; apply GlobalTheory.HilbAff.valuativeExistence  <;> assumption)

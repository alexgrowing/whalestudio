import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertValuativeCriterionUniqueness
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbert_valuativeCriterion_uniqueness : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ValuativeCriterion.Uniqueness (R.homEquiv (𝟙 H)).1 := by
  first | exact @GlobalTheory.HilbAff.valuativeCriterion_uniqueness | exact GlobalTheory.HilbAff.valuativeCriterion_uniqueness | (intros; apply GlobalTheory.HilbAff.valuativeCriterion_uniqueness <;> assumption)

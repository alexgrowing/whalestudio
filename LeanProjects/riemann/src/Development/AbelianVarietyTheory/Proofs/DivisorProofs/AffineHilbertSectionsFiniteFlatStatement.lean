import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsFiniteFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertSections_finite_flat : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens), Module.Finite Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) ∧ Module.Flat Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) := by
  first | (exact @GlobalTheory.HilbAff.sec_finite_flat) | (exact GlobalTheory.HilbAff.sec_finite_flat) | (intros; apply GlobalTheory.HilbAff.sec_finite_flat  <;> assumption)

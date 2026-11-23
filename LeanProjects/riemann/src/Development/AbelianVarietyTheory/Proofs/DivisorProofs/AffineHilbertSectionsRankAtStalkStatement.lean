import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsRankAtStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertSections_rankAtStalk : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) (P : PrimeSpectrum Γ(Z, W)), Module.rankAtStalk (GlobalTheory.HilbAff.Sec A B y W) P = r := by
  first | (exact @GlobalTheory.HilbAff.rankAtStalk_sec) | (exact GlobalTheory.HilbAff.rankAtStalk_sec) | (intros; apply GlobalTheory.HilbAff.rankAtStalk_sec  <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertCoordinateMapBijectiveOfLeAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertCoordinateMap_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  first | (exact @GlobalTheory.HilbAff.coord_bijective_of_le_affine) | (exact GlobalTheory.HilbAff.coord_bijective_of_le_affine) | (intros; apply GlobalTheory.HilbAff.coord_bijective_of_le_affine  <;> assumption)

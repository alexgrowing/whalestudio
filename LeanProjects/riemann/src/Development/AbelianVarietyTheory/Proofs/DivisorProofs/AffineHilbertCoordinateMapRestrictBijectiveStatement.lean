import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapRestrictBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertCoordinateMap_restrict_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (U : Z.Opens) (W : U.toScheme.Opens), Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y (U.ι ''ᵁ W)) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) W) := by
  first | (exact @GlobalTheory.HilbAff.coord_restrict_bijective) | (exact GlobalTheory.HilbAff.coord_restrict_bijective) | (intros; apply GlobalTheory.HilbAff.coord_restrict_bijective  <;> assumption)

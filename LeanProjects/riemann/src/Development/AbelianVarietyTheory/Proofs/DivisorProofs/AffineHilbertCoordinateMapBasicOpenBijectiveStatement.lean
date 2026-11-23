import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapBasicOpenBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) (f : Γ(Z, W)), Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y (Z.basicOpen f)) ↔ Function.Bijective (LocalizedModule.map (Submonoid.powers f) (GlobalTheory.HilbAff.coord A B e σ y W)) := by
  first | (exact @GlobalTheory.HilbAff.coord_basicOpen_bijective_iff) | (exact GlobalTheory.HilbAff.coord_basicOpen_bijective_iff) | (intros; apply GlobalTheory.HilbAff.coord_basicOpen_bijective_iff  <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhood
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  first | (exact @GlobalTheory.HilbAff.exists_basic_nhd) | (exact GlobalTheory.HilbAff.exists_basic_nhd) | (intros; apply GlobalTheory.HilbAff.exists_basic_nhd  <;> assumption)

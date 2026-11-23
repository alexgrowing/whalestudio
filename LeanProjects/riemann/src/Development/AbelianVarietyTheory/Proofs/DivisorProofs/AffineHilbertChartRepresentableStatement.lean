import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertChartRepresentable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertChart_representable : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N), ∃ (X : Scheme.{0}) (x : (GlobalTheory.HilbAff.functor A B r).obj (op X)), IsAffine X ∧ LocallyOfFiniteType x.1 ∧ GlobalTheory.HilbAff.Basic A B e σ x ∧ ∀ (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), GlobalTheory.HilbAff.Basic A B e σ y → ∃! g : Z ⟶ X, (GlobalTheory.HilbAff.functor A B r).map g.op x = y := by
  first | (exact @GlobalTheory.HilbAff.chart_represents) | (exact GlobalTheory.HilbAff.chart_represents) | (intros; apply GlobalTheory.HilbAff.chart_represents <;> assumption)

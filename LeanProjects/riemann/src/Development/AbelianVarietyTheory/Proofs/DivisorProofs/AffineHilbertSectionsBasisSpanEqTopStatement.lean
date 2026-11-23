import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsBasisSpanEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertSections_basis_span_eq_top : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens), Submodule.span Γ(Z, W) (Set.range fun j => GlobalTheory.HilbAff.gen A B y W (e j)) = ⊤ := by
  first | (exact @GlobalTheory.HilbAff.span_gen_eq_top) | (exact GlobalTheory.HilbAff.span_gen_eq_top) | (intros; apply GlobalTheory.HilbAff.span_gen_eq_top  <;> assumption)

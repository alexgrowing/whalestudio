import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRelativeDimOfTrdeg
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_relative_dim_of_trdeg : ∀ {X S : Scheme.{0}} (f : X ⟶ S) (n : ℕ), Smooth f →
    (∀ x : X, (∀ x' : X, f x' = f x → x' ⤳ x → x' = x) →
      @Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _ (f.residueFieldMap x).hom.toAlgebra = n) →
    SmoothOfRelativeDimension n f := by
  first | exact @GlobalTheory.RelDimFibCrit.smoothOfRelativeDimension_of_trdeg | exact GlobalTheory.RelDimFibCrit.smoothOfRelativeDimension_of_trdeg | (intros; apply GlobalTheory.RelDimFibCrit.smoothOfRelativeDimension_of_trdeg <;> assumption)

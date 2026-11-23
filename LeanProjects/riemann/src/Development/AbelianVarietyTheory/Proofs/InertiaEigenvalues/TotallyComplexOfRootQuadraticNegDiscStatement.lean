import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexOfRootQuadraticNegDisc
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyComplex_of_root_quadratic_neg_disc : ∀ (K : Type) [Field K] [NumberField K] (x : K) (a b : ℤ), x ^ 2 + (a : K) * x + (b : K) = 0 →
    a ^ 2 < 4 * b → NumberField.IsTotallyComplex K := by
  first | exact @GlobalTheory.totallyComplex_of_root_quadratic_neg_disc | exact GlobalTheory.totallyComplex_of_root_quadratic_neg_disc | (intros; apply GlobalTheory.totallyComplex_of_root_quadratic_neg_disc <;> assumption)

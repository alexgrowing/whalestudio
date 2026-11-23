import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
open GlobalTheory.LogU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt : ∀ (n i j : ℕ), i + j < n → MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (GlobalTheory.LogU.logDefect n) = 0 := by
  first | (exact @GlobalTheory.LogU.logDefect_coeff_eq_zero) | (exact GlobalTheory.LogU.logDefect_coeff_eq_zero) | (intros; apply GlobalTheory.LogU.logDefect_coeff_eq_zero  <;> assumption)

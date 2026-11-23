import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  first | exact @GlobalTheory.PMon.Gauss.acris_mul_eq_zero | exact GlobalTheory.PMon.Gauss.acris_mul_eq_zero | (intros; apply GlobalTheory.PMon.Gauss.acris_mul_eq_zero <;> assumption)

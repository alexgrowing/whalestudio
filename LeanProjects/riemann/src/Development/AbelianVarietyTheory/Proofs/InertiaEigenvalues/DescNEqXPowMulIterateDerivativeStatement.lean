import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivative
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' : ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * (⇑(derivative K))^[p] f := by
  first | exact @GlobalTheory.BKReal.descN_eq_X_pow_mul_iterate_derivative | exact GlobalTheory.BKReal.descN_eq_X_pow_mul_iterate_derivative | (intros; apply GlobalTheory.BKReal.descN_eq_X_pow_mul_iterate_derivative <;> assumption)

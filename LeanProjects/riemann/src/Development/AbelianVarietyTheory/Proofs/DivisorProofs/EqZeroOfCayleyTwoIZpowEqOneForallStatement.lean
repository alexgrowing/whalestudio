import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCayleyTwoIZpowEqOneForall
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_cayley_two_I_zpow_eq_one_forall : ∀ m : ℤ, (∀ x : ℝ, ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) ^ m = 1) → m = 0 := by
  first | exact @GlobalTheory.zpow_cayley_two_eq_one_forall | exact GlobalTheory.zpow_cayley_two_eq_one_forall | (intros; apply GlobalTheory.zpow_cayley_two_eq_one_forall <;> assumption)

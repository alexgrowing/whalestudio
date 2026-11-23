import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  first | exact @GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | exact GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | (intros; apply GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero <;> assumption)

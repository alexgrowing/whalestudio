import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  first | exact @GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | exact GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | (intros; apply GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero <;> assumption)

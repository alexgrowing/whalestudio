import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneAdditiveFormalGroupLawXPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose : ∀ (R : Type) [CommRing R] (d N : ℕ) (m : Fin d), 1 ≤ N → cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N, monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i)) (N.choose i : R) := by
  first | exact @GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow | exact GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow | (intros; apply GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombination
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_shifted_series_eq_integral_poly_combination : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  first | exact @GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral | exact GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral | (intros; apply GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral <;> assumption)

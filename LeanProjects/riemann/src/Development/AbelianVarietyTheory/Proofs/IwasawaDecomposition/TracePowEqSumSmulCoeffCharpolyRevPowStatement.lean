import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEqSumSmulCoeffCharpolyRevPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_pow_eq_sum_smul_coeff_charpolyRev : ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ → ℝ, ∀ (S : Type) [CommRing S] [Algebra ℝ S] (N : ℕ) (L : Matrix (Fin N) (Fin N) S), ∑ k ∈ Finset.range (n + 1), c k • ((Matrix.charpolyRev (-L)) ^ k).coeff n = (L ^ n).trace := by
  first | exact @GlobalTheory.trace_pow_eq_sum_smul_coeff_charpolyRev_pow | exact GlobalTheory.trace_pow_eq_sum_smul_coeff_charpolyRev_pow | (intros; apply GlobalTheory.trace_pow_eq_sum_smul_coeff_charpolyRev_pow <;> assumption)

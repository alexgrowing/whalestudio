import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowFinProdKroneckerAddBinomial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_finProdKronecker_add_binomial : ∀ {R : Type} [CommRing R] {M N : ℕ} (L : Matrix (Fin M) (Fin M) R) (L' : Matrix (Fin N) (Fin N) R) (i : ℕ), ((kron L 1 + kron 1 L') ^ i).trace = ∑ a ∈ Finset.range (i + 1), (i.choose a : R) * (L ^ a).trace * (L' ^ (i - a)).trace := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add | exact GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add <;> assumption)

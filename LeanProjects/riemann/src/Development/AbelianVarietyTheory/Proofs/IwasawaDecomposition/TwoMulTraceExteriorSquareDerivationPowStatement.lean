import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulTraceExteriorSquareDerivationPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_trace_exteriorSquareDerivation_pow : ∀ {R : Type} [CommRing R] {M : ℕ} (L : Matrix (Fin M) (Fin M) R) (i : ℕ), 2 * ((wedge2Lie L) ^ i).trace = ((kron L 1 + kron 1 L) ^ i).trace - 2 ^ i * (L ^ i).trace := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | exact GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | (intros; apply GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow <;> assumption)

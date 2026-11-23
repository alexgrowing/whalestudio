import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieDirectSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_sum | exact GlobalTheory.GoodMetric.PolyRep.lie_sum | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_sum <;> assumption)

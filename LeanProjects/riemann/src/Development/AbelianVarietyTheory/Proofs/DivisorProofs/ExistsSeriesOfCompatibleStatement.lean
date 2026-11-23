import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeriesOfCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_of_compatible' : ∀ (p : ℕ) (O σ : Type) [CommRing O] [Fintype σ] [IsAdicComplete (Ideal.span {(p : O)}) O] (A : ℕ → Type) [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)], (∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)) → ∀ (x : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n) (t : ∀ n, A n), (∀ n, IsEval p (x n) (E n)) → (∀ n, ∃ f, E n f = t n) → (∀ n f, E (n + 1) f = t (n + 1) → E n f = t n) → (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∃ g, ∀ n, E n g = t n := by
  first | exact @GlobalTheory.CChartLimit.exists_series_of_compatible | exact GlobalTheory.CChartLimit.exists_series_of_compatible | (intros; apply GlobalTheory.CChartLimit.exists_series_of_compatible <;> assumption)

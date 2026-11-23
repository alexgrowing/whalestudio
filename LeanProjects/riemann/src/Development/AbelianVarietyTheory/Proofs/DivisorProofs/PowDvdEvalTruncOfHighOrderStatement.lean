import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdEvalTruncOfHighOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_dvd_eval_trunc_of_high_order : ∀ (p : ℕ) (B : Type) [CommRing B] (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∃ L : ℕ, ∀ (k : ℕ) (h : MvPowerSeries σ B), (∀ α : σ →₀ ℕ, α.degree < L * k → coeff α h = 0) → ∀ n : σ →₀ ℕ, (p : B) ^ k ∣ MvPolynomial.eval z (trunc' B n h) := by
  first | exact @GlobalTheory.trunc'_eval_dvd_of_order | exact GlobalTheory.trunc'_eval_dvd_of_order | (intros; apply GlobalTheory.trunc'_eval_dvd_of_order <;> assumption)

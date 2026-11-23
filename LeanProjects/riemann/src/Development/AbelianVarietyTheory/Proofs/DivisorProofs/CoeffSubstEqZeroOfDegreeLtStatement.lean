import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' : ∀ (R : Type) [CommRing R] (σ τ : Type) [Fintype σ] (u : σ → MvPowerSeries τ R) (f : MvPowerSeries σ R) (M : ℕ), (∀ i, constantCoeff (u i) = 0) → (∀ α : σ →₀ ℕ, α.degree < M → coeff α f = 0) → ∀ β : τ →₀ ℕ, β.degree < M → coeff β (subst u f) = 0 := by
  first | exact @GlobalTheory.coeff_subst_eq_zero_of_degree_lt | exact GlobalTheory.coeff_subst_eq_zero_of_degree_lt | (intros; apply GlobalTheory.coeff_subst_eq_zero_of_degree_lt <;> assumption)

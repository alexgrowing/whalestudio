import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivation_coeff_eq_zero_of_degree_lt : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R) (r : ℕ), (∀ α : Fin d →₀ ℕ, α.degree < r + 1 → coeff α F = 0) → ∀ α : Fin d →₀ ℕ, α.degree < r → coeff α (invDer μ u F) = 0 := by
  first | exact @GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | exact GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | (intros; apply GlobalTheory.invDer_coeff_eq_zero_of_degree_lt <;> assumption)

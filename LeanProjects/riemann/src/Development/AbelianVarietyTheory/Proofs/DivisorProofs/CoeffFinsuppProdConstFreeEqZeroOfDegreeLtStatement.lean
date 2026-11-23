import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFinsuppProdConstFreeEqZeroOfDegreeLt
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt : ∀ (R : Type) [CommRing R] (σ τ : Type) (u : τ → MvPowerSeries σ R), (∀ j, constantCoeff (u j) = 0) → ∀ (α : τ →₀ ℕ) (β : σ →₀ ℕ), β.degree < α.degree → coeff β (α.prod fun j e => u j ^ e) = 0 := by
  first | exact @GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt | exact GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt | (intros; apply GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt <;> assumption)

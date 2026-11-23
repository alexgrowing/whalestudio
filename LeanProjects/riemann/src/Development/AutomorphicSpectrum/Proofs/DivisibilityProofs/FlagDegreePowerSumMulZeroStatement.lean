import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePowerSumMulZero
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_power_sum_mul_zero : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (k : ℕ) (G : RP Ψ N), 1 ≤ k → degFl (pk τ k * G) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.degFl_pk_mul_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Top.degFl_pk_mul_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.degFl_pk_mul_eq_zero <;> assumption)

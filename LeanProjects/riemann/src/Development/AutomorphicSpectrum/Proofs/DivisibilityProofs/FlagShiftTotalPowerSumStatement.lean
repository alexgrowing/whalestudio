import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalPowerSum
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_shift_total_power_sum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ σ : Ψ) (k : ℕ) (Q : RP Ψ N), 1 ≤ k → Sh j σ (pk τ k * Q) = (if σ = τ then k * degFl (pkLow j τ (k - 1) * Q) else 0) ∧ Tot σ (pk τ k * Q) = (if σ = τ ∧ k = 1 then N * degFl Q else 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul | exact GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul <;> assumption)

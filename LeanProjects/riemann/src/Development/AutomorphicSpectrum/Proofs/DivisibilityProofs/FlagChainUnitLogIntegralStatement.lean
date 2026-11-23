import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainUnitLogIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chain_unit_log_integral : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ k₀ : K, (∀ a : K, a = k₀) → ∀ j : K → FlBlock Ψ N, IsChain j → ptsIntegral (PPart j) (pot fun _ : Fin (N - 1) => unitLine j k₀) (fun _ => 1) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first <;> assumption)

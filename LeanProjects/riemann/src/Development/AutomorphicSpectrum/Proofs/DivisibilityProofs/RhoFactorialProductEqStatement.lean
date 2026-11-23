import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoFactorialProductEq
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rho_factorial_product_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), ∏ p, (((rhoM Ψ N) p).factorial : ℝ) = ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.prod_rhoM_factorial | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.prod_rhoM_factorial | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.prod_rhoM_factorial <;> assumption)

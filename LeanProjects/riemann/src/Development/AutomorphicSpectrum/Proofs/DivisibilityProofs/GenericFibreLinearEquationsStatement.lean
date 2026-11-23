import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericFibreLinearEquations
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsBlockMapDrop
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_linear_equations : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N), IsChain j → ∀ k₀ : K, (∀ k, ((j k).2 : ℕ) ≤ (j k₀).2) → (∃ k, k ≠ k₀) → ∃ G : GenFibre (dropV j k₀) (PPart j), ∃ S : Set (MRingOver G.Φ (fibreIdx (PIdx j) (Subtype.val : {k // k ≠ k₀} → K))), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (Subtype.val : {k // k ≠ k₀} → K) G = Ideal.span S := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.FibreLin.fibre_lin | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.FibreLin.fibre_lin | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.FibreLin.fibre_lin <;> assumption)

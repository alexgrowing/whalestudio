import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_weight_formula : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (lam : Wt Ψ N), flagDeg lam = ((dimFl Ψ N).factorial : ℝ) * ∏ τ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) ∧ (RegDominant lam → 0 < flagDeg lam) ∧ (Dominant lam → 0 ≤ flagDeg lam) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl | exact GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl <;> assumption)

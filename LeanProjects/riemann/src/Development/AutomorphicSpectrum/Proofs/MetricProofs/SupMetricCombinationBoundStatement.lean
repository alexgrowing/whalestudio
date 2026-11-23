import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SupMetricCombinationBound
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sup_metric_combination_bound : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (R : RootModel Ψ N) (lam : Wt Ψ N) (n' : Option (Ψ × Fin N) → ℤ) (p : ℕ) [Fact p.Prime] (z : (Σ k, R.ι k) → PadicAlgCl p) (rec : Ψ × Fin N → ℝ) (θ : ℝ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ j, (n' j : ℝ) = R.coef lam 0 j) → (∀ r, 0 < rec r) → (∀ r, |Real.log (supMet (R.xdeg r) z) - Real.log (rec r)| ≤ θ * Real.log p) → supMet (combLine (R.line 1) n').a z ≤ (p : ℝ) ^ (θ * l1 lam) * ∏ r, rec r ^ n' (some r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.supMet_line_le_record | exact GlobalTheory.CompanionTheory.Ar.Small.supMet_line_le_record | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.supMet_line_le_record <;> assumption)

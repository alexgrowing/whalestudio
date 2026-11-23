import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshAddPshPotentialOnOpen
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSetStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_add_psh_potential_on_open : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) (f : X → ℝ) (Θ : LocPot X), IsOpen U → IsPotential A P → IsPotential A Θ → A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) → IsPsh A Θ → IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | exact GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | (intros; apply GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh <;> assumption)

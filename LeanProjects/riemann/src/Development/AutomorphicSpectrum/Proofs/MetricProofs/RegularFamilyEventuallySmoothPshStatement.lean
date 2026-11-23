import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyEventuallySmoothPsh
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
theorem _root_.GlobalTheory.T.regular_family_eventually_smooth_psh : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsRegFamily A Θ L s th ph phT C t₀ → ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot | exact GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot <;> assumption)

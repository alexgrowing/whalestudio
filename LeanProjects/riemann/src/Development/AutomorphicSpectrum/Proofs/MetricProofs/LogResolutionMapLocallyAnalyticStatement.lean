import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalytic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_map_locally_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOrbitBound
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_orbit_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : PB.AnSys D σ) (P : Ideal (MRing ι)) (Re : PB.Realis S P), Re.J = ⊤ → ∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts P) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → Re.π x ∈ S.open') → ∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → ReciprocityTheory.AnForm.P.rW S.L S.s (Re.π x) ≤ C * (1 + |Real.log ‖z‖|) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc | exact GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeConjugateCusp
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  first | exact @LevelTowerAlt.riemann_lattice_conjugate_cusp | exact LevelTowerAlt.riemann_lattice_conjugate_cusp

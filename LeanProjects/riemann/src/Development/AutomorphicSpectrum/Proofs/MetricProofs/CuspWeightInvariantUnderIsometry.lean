import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeIsometryTransport
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (g' : ℕ) (Λ' : Type) [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)), IsCMFam σ → φ '' Set.range R.P = Set.range R'.P → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) → (∀ a x, φ (R.B a x) = R'.B a (φ x)) → R'.cuspW σ = R.cuspW σ ∧ R'.lam1 = R.lam1 ∧ (∀ m, R'.HasRank σ m ↔ R.HasRank σ m) ∧ ∃ α : Λ ≃ₗ[𝓞 E] Λ', (∀ v, R'.P (α v) = φ (R.P v)) ∧ ∀ I, IsIsoSub R.form I → R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  first | exact @LevelTowerAlt.riemann_lattice_isometry_transport | exact LevelTowerAlt.riemann_lattice_isometry_transport

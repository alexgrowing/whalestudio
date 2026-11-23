import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariables
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_density_change_of_variables : ∀ (n : ℕ) (φ ψ : (Fin n → ℂ) → ℝ) (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ) (t : Fin n → ℂ), AnalyticAt ℂ A t → AnalyticAt ℂ G t → ContDiffAt ℝ 2 φ (A t) → (∀ᶠ t' in 𝓝 t, ψ t' = φ (A t') + (G t').re) → maDensity (fun (_ : Fin n) => ψ) t = ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * maDensity (fun (_ : Fin n) => φ) (A t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul <;> assumption)

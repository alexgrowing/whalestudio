import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartHessHolo

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem maDensity_const_eq_normSq_jacobian_mul :
    ∀ (n : ℕ) (φ ψ : (Fin n → ℂ) → ℝ) (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ)
      (t : Fin n → ℂ), AnalyticAt ℂ A t → AnalyticAt ℂ G t → ContDiffAt ℝ 2 φ (A t) →
      (∀ᶠ t' in 𝓝 t, ψ t' = φ (A t') + (G t').re) →
      maDensity (fun (_ : Fin n) => ψ) t =
        ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * maDensity (fun (_ : Fin n) => φ) (A t) := by
  intro n φ ψ A G t hA hG hφ hψ
  have h := GroundTheory.Heights₂.Heights.ChartEnergySwapHessian.maDensity_comp_holo
    (fun (_ : Fin n) => ψ) (fun (_ : Fin n) => φ) A G t (fun _ => hφ) hA.contDiffAt hG.contDiffAt
    (fun _ => hψ)
  rw [h, LinearMap.det_toMatrix', Complex.normSq_eq_norm_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp

import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetChange
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_change_of_basis_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (bb d : Fin m → Fin g → ℂ) (Y M : Matrix (Fin m) (Fin m) ℂ) (κ : ℝ), 0 < κ → (∀ b, d b = ∑ c, Y c b • bb c) → R.gram d * M = (κ : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) → M.PosDef → Y.det ≠ 0 ∧ -Real.log M.det.re = 2 * Real.log ‖Y.det‖ + Real.log (R.gram bb).det.re - m * Real.log κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog.log_det_change | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog.log_det_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog.log_det_change <;> assumption)

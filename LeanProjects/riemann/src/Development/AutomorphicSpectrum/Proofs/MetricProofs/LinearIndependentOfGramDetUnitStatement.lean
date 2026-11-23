import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentOfGramDetUnit
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
theorem _root_.GlobalTheory.T.linearIndependent_of_gram_det_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (d : Fin m → Fin g → ℂ), IsUnit (R.gram d).det → LinearIndependent ℂ d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.linearIndependent_of_isUnit_gram_det | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.linearIndependent_of_isUnit_gram_det | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.linearIndependent_of_isUnit_gram_det <;> assumption)

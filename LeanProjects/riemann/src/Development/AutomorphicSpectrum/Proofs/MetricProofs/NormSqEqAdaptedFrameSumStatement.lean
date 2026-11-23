import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormSqEqAdaptedFrameSum
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_eq_adapted_frame_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → C.IsAdapted R A → ∀ x, R.normSq x = 2 * C.c * ∑ τ, (star (C.cinv (A τ) τ *ᵥ C.vec x τ) ⬝ᵥ (C.cinv (A τ) τ *ᵥ C.vec x τ)).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_adapted | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_adapted <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicAdaptedFrameOnBall
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
theorem _root_.GlobalTheory.T.holomorphic_adapted_frame_on_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted (F.R 0) A₀ → ∃ (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom F.q) ∧ DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ t ∈ ballDom F.q, ∀ A, C.IsAdapted (F.R t) A → Z t = moebBall F.q (fun τ => C.cinv (A₀ τ) τ * A τ) 0) ∧ ∀ t ∈ ballDom F.q, ballPot F.q (Z t) = ballPot F.q t + (G t).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists <;> assumption)

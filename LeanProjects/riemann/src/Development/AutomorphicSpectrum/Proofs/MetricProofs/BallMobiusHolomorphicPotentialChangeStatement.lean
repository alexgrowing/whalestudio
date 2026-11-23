import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChange
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
theorem _root_.GlobalTheory.T.ball_mobius_holomorphic_potential_change : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → DifferentiableOn ℂ (moebBall q u) (ballDom q) ∧ Set.MapsTo (moebBall q u) (ballDom q) (ballDom q) ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (ballDom q) ∧ ∀ t ∈ ballDom q, ballPot q (moebBall q u t) = ballPot q t + (G t).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props <;> assumption)

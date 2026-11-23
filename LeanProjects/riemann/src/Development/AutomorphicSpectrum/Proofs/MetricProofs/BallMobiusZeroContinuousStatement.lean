import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuous
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
theorem _root_.GlobalTheory.T.ball_mobius_zero_continuous : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, Continuous fun x => f x τ) → (∀ x τ, IsSgU (f x τ)) → Continuous fun x => moebBall q (f x) 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero <;> assumption)

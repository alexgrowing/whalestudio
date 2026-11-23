import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsThetaSupBoundLogMean
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_sup_bound_log_mean : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (Φ : ℝ), 1 ≤ D.g → 0 ≤ Φ → D.HasTheta th Φ → ∃ M : (L →+* ℂ) → ℝ, (∀ σ, 0 < M σ) ∧ D.SupLe th M ∧ mean L (fun σ => Real.log (M σ)) ≤ Φ + C * D.g * Real.log (2 + D.g + Φ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Sup.mean_log_sup | exact GlobalTheory.CompanionTheory.Ar.Sl.Sup.mean_log_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Sup.mean_log_sup <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TorsionValueNormEqThetaNorm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_value_norm_eq_theta_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (n : ℕ) (s : Out.H0 D.t.PP.L n) (θ : (Fin D.g → ℂ) → ℂ) (y : Over.mk (emb σ) ⟶ D.t.G) (w : Fin D.g → ℂ) (N : ℕ) (T : ℂ), a.IsFn s θ → y.left = a.pt w → TorsVal D.t.PP s y N T → ‖T‖ = a.nrm n θ w ^ (N ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsArch.torsVal_norm | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsArch.torsVal_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsArch.torsVal_norm <;> assumption)

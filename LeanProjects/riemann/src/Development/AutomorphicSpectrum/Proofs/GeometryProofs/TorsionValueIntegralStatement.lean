import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueIntegral
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_value_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (K : Type) [Field K] [NumberField K] (c : 𝓞 L →+* K) (y : Over.mk (spMap c) ⟶ D.t.G) (N : ℕ) (T : K), TorsVal D.t.PP th y N T → IsIntegral ℤ T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.IntTors.integral_torsVal | exact GlobalTheory.CompanionTheory.Ar.Sl.IntTors.integral_torsVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.IntTors.integral_torsVal <;> assumption)

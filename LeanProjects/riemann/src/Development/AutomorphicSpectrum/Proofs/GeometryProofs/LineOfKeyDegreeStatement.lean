import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineOfKeyDegree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_of_key_degree : KeyDegSt → LineSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.LineProof.line_of_key | exact GlobalTheory.CompanionTheory.Ar.Sl.LineProof.line_of_key | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.LineProof.line_of_key <;> assumption)

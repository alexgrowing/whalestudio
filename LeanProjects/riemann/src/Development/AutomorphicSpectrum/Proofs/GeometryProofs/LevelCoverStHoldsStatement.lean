import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHolds
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LevelCoverSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LevelCoverSt_holds : GlobalTheory.CompanionTheory.Ar.XR.LevelCoverSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.levelCover | exact GlobalTheory.CompanionTheory.Ar.XR.levelCover | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.levelCover <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGaga
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_zero_from_resolution_and_gaga : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.Flat.GagaSections → GlobalTheory.CompanionTheory.Ar.Flat.FlatLineGenerator := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga | exact GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga <;> assumption)

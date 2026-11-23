import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHolds
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PropFTop_holds : PropFTop := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.propFTop | exact GlobalTheory.CompanionTheory.Ar.Flat.propFTop | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.propFTop <;> assumption)

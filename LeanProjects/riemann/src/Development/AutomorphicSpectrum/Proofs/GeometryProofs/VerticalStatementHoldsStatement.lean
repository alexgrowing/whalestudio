import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalStatementHolds
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_statement_holds : VerticalStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds | exact GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds <;> assumption)

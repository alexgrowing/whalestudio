import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystem
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system <;> assumption)

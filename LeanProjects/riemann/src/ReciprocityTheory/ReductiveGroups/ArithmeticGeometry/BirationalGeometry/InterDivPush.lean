import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushC

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem resDivPush_of (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hI : PtsIntegrableStatement) (h1 : DivPushResSideStatement)
    (h2 : DivPushPointStatement) : ResDivPushStatement :=
  resDivPush_of_fibre hE hB hI divPushCommonProj (divPushFibre_of h1 h2)

end ReciprocityTheory.ChartRestriction.G.Geo

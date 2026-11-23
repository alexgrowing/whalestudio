import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCFinal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonLiftPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.H1

theorem cmLiftCondition_of_laws (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) (h1c : ReciprocityTheory.ChartRestriction.G.DVR.PositiveValuationMaximalIdeal)
    (hTW : ReciprocityTheory.ChartRestriction.G.DVR.TWStatement) (hU : ReciprocityTheory.ChartRestriction.G.DVR.UUStatement) : OneCStatement :=
  cmLiftCondition_of_torsion hL h1c hTW hU (canonLiftFix_of_laws hL) dimSplit

end ReciprocityTheory.ChartRestriction.G.H1

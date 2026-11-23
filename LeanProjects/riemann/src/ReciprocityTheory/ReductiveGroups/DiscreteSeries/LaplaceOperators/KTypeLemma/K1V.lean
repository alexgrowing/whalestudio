import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StandardKTypeOfCentralChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CentralChar

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem k1V (n : ℕ) : LowestKTypeEulerTensorStandard n :=
  standardKType_of_centralChar n (centralChar n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK

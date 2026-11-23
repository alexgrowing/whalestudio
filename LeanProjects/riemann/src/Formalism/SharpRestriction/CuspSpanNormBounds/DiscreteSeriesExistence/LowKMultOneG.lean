import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DiscreteSeriesUniqueLargeGap

namespace Formalism.MainNotions.BesselDiscreteSeries

theorem lowest_K_type_mult_one_of_gaps : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG :=
  fun N ε lam H _ _ σ hp hσ h hg hthr => ReciprocityTheory.ChartRestriction.DS.final_lowKMultOneG N ε lam H σ hp hσ h hg hthr

end Formalism.MainNotions.BesselDiscreteSeries

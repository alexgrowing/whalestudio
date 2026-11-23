import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeBoundAtMaximumOfTransference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlagSpanBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalChartNormControlHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem frameAtMaximum_of_transference (hD5 : CoveringRadiusStatement) : FrameAtMaximum (E := E) :=
  frameAtMaximum_of_lower_bound (latticeBoundAtMaximum_of_transference hD5) orthonormalChartNormControl_holds

end ReciprocityTheory.ChartRestriction.G.FD

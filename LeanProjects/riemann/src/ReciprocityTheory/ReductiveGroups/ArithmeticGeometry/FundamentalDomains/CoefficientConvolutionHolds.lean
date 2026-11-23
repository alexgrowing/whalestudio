import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionOfSubCoefficients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem coefficientConvolution_holds : CoefficientConvolution (E := E) :=
  PeriodLatticeMembership.coefficientConvolution_of_subCoefficients (fun r X la P hP ξ hξ x hx ω hωp hωi k ν hk =>
    SublatticeCoefficients.subCoeff X la P hP ξ hξ x hx ω hωp hωi k ν hk)

end ReciprocityTheory.ChartRestriction.G.FD

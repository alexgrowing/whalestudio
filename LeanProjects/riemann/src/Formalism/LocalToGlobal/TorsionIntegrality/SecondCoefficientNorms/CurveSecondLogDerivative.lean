import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CurveIntegerMultiplicationSeries

namespace Formalism.L2.Th1.C

theorem curveFrame : CurveFrame := curve_formal_frame
theorem curve_second_log_derivative : CurveSecondLogDerivative := curve_second_log_derivative_holds
theorem curveEndoR : CurveEndoR := curve_real_multiplication_series
theorem curveEndoAll : CurveEndoAll := curve_all_endomorphism_series

end Formalism.L2.Th1.C

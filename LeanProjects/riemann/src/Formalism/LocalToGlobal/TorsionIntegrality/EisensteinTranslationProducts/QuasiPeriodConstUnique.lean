import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OperatorUComm
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SgStar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HermHalfRight

namespace Formalism.L2.Th1.F

theorem areaPos : AreaPos := areaPos_thm
theorem etaSplit : EtaSplit := etaSplit_of legendre
theorem altEInt : AltEInt := alternating_form_integral
theorem altEBasis : AltEBasis := alternating_form_basis
theorem semiCharMul : SemiCharMul := semi_character_mul
theorem opUMul : OpUMul := operator_u_mul
theorem opUComm : OpUComm := operator_u_comm
theorem sgStarQuasi : SgStarQuasi := sgStarQuasi_of sigmaQuasi etaSplit
theorem sgStarFixed : SgStarFixed := sgStarFixed_of sgStarQuasi
theorem sigmaTaylorLow :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 :=
  sigmaTaylorLow_of sigmaEntire sigmaSummable
theorem sgStarBasic : SgStarBasic :=
  sgStarBasic_of sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaTaylorLow
theorem th0Const : ThetaZeroConstant := th0Const_of sgStarBasic
theorem th0Basic : ThetaZeroBasic := th0Basic_of sgStarBasic sgStarQuasi altEInt
theorem th0Class : ThetaZeroClass := th0Class_of sgStarBasic sgStarQuasi
theorem th0LogDeriv : ThetaZeroLogDerivative := th0LogDeriv_of sigmaLogDeriv etaSplit zetaQuasi zetaOdd

end Formalism.L2.Th1.F

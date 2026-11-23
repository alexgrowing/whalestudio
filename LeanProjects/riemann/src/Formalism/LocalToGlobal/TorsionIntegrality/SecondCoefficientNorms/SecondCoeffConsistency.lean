import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffSubstBinomSeries
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.HasSecondLogDerivPowerSeriesExp
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideA
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideB

namespace Formalism.L2.Th1.C

theorem mvExpLaws : MvExpLaws := formalExpLaws'
theorem mvExpSubst : MvExpSubst := formalExpSubst'
theorem lGSubgroup : LGSubgroup := lGSubgroup_of mvExpLaws
theorem lGBinom : LGBinom := expIntegralBinomial'
theorem lGHalf : LGHalf := lGHalf_of mvExpLaws
theorem intBinomScalar : IntBinomScalar := intBinomialScalar'
theorem lGSubst : LGSubst := lGSubst_of mvExpSubst
theorem lGSubstMv : LGSubstMv := expIntegralMvSubst'
theorem intSubst : IntSubst := coeffsInSubst'

theorem isogenyIffBar : IsogenyIffBar := isogenyIffBar_of mvExpLaws

theorem veluXFromZ : VeluXFromZ := veluXOfSigma'
theorem isogenyU : IsogenyU := isogenyU_of mvExpLaws mvExpSubst
theorem phNormUnit : PhNormUnit := phNormUnit_of mvExpLaws mvExpSubst lGHalf isogenyU

end Formalism.L2.Th1.C

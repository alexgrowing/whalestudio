import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntPSDerivativeOfLG
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntegralEndomorphismFromDatum

namespace Formalism.L2.Th1.C

theorem ptClosure : PtClosure := integralPointClosure'
theorem adjFromNorm : AdjFromNorm := adjoint_from_norm_form
theorem normAdjAll : NormAdjAll := norm_adjoint_all_places
theorem unitaryInv : UnitaryInv := unitary_inverse_identity
theorem hyperbolicSum : HyperbolicSum := hyperbolic_sum_identity

theorem endIntClosed : EndIntClosed := integralEndoClosed'
theorem binomClosed : BinomClosed := binomialScalarClosed'
theorem phNormClosed : PhNormClosed := logNormClosed'
theorem zLinClosed : ZLinClosed := scalarLinearClosed'
theorem zLinInt : ZLinInt := scalarLinearInt'
theorem endoAll : EndoAll := endoAll_of normAdjAll

theorem jetAdditive : JetAdditive := jetAdditivity
theorem jetOne : JetOne := jetOne'
theorem jetAdj : JetAdj := jetAdjoint'
theorem jetExp : JetExp := jetExp'

theorem endIntFromDatum : EndIntFromDatum := integral_endomorphism_from_datum
theorem phNormFromDatum : PhNormFromDatum := phi_norm_from_datum
theorem endoAllFromData : EndoAllFromData := endoAllFromData_of endoAll

end Formalism.L2.Th1.C

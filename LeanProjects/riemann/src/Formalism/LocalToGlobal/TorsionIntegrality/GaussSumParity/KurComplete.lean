import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExistsUnitFactorizationBounded
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IntegralPartAtVariable

namespace Formalism.L2.Th1.D

theorem ringAFacts : RingAFacts := ring_a_facts
theorem kurIntegers : KurIntegers := KurIntegers_of ringAFacts
theorem kurUnram : KurUnram := KurUnram_of kurIntegers
theorem kurRoots : KurRoots := unramified_completion_roots
theorem kurComplete : KurComplete := unramified_completion_complete
theorem frobAIsom : FrobAIsom := FrobAIsom_of ringAFacts
theorem kurFrob : KurFrob := KurFrob_of frobA frobAIsom kurIntegers kurUnram
theorem fOfBetaHyp : FOfBetaHyp := f_of_beta_hypotheses

end Formalism.L2.Th1.D

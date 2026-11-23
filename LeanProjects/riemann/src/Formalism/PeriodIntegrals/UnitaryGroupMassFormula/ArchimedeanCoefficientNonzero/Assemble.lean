import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Factor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.InnerInvOfDS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Smooth

namespace PI.BICNZ

theorem betaInfCoefNZ_of_limits (hS : Formalism.FourierDecayAlt.ThreeDimData.SchurH) (hL : LeftLimit) (hR : RightLimit) :
    Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ :=
  betaInfCoefNZ_of (betaFactor_of (phiAt_of hS) left_profile_contDiff_two right_profile_contDiff_two) hL hR

end PI.BICNZ

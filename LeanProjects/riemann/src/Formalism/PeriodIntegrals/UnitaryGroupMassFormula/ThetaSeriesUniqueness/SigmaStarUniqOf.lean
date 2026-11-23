import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.CoefShift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.ZeroOfCoef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SiegelSetShiftInvariance
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SiegelSetCompleteness

namespace PI.SSU

theorem sigmaStarUniq_of (h : AreaLat) : SigmaStarUniq :=
  main_of (key_of siegel_set_shift_invariance siegel_set_completeness) h

end PI.SSU

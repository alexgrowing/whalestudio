import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.GelfCptOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.MulIntMatMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.IntegrableOfContinuousCpt

namespace PI.UnitaryGroupMassFormula.GelfCpt

theorem gelfCpt_of : PI.UMultOne.IntSpan → PI.UMultOne.ConvComm → PI.UMultOne.GelfandCompact :=
  gelfCpt_of_steps avgStep mulStep

end PI.UnitaryGroupMassFormula.GelfCpt

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.PhiXFinrankRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.CardFibreCompl

namespace PI.DensSplitW

theorem fiberCard_holds : FiberCard := by
  intro K V U _ _ _ _ _ _ _ φ hφ k g
  exact FibreCount.fiber_card φ hφ g

end PI.DensSplitW

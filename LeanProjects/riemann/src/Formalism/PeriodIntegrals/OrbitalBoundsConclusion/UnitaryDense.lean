import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.VanishInvertible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Decomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Derived

theorem productFramesDense_holds : PI.FramesDense := PI.UD.framesDense_of PI.UD.svdStep PI.UD.gramStep

theorem unitaryGroupDense_holds : PI.UnitaryDense := unitaryDense_of productFramesDense_holds

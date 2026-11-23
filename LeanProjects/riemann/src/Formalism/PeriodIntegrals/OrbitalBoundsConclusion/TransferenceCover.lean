import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.NumericMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall

theorem transference_covering : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

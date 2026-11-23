import Formalism.PeriodIntegrals.SzCt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SzCtOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.FirstCoordinateLeThreeScale
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SizeFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Places

theorem sz_constant_term : PI.SzCt.SzCt :=
  PI.SzCt.UnitaryGroupMassFormula.szCt_of PI.SzCt.UnitaryGroupMassFormula.rowA PI.SzCt.UnitaryGroupMassFormula.rowB PI.SzCt.UnitaryGroupMassFormula.rowC
    PI.SzCt.UnitaryGroupMassFormula.sizeFacts PI.SzCt.UnitaryGroupMassFormula.placeFacts

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExistsAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.CoefXOfMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.Assemble

theorem flagRelevScalar (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E] : Formalism.L2.SG.IdCell.RelevScalar E K :=
  PI.FRS.relevScalar_of PI.FRS.dualExists PI.FRS.coefAdd PI.FRS.coefSmul PI.FRS.coefE
    PI.FRS.coefLow E K

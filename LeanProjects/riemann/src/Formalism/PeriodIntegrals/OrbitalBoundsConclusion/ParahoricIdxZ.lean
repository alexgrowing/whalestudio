import Mathlib
import Formalism.PeriodIntegrals.ParahoricIdxZ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.SpanIsMaximal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.IdxStep

theorem parahoric_index_int : PI.ParahoricIdxZ :=
  PI.ParahoricIdxZ.W.parahoricIdxZ_of PI.ParahoricIdxZ.W.idxStep PI.ParahoricIdxZ.W.cardStep

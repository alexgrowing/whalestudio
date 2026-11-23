import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell

theorem quantum_w_big_cell : Formalism.FourierDecayAlt.Q.WCellBigCell :=
  fun k r c μ => PI.QnWCellW.main k r c μ

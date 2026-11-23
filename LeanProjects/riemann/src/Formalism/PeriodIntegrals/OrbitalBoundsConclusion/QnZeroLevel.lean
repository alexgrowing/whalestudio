import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroLevelIndex.SecondMinorZeroLevelFormula

theorem capelli_zero_level : Formalism.FourierDecayAlt.Q.CapLZero ∧ Formalism.FourierDecayAlt.Q.TLZero :=
  PI.QnZeroLevelWork.qnZeroLevel

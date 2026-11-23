import Mathlib
import Formalism.PeriodIntegrals.SqfDivDeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.CardMonicTwoRootsLe

theorem squarefree_div_degree : PI.SqfDivDeg.Claim :=
  PI.SqfDivDeg.W.sqfDivDeg_of_rootDense PI.SqfDivDeg.W.rootDense

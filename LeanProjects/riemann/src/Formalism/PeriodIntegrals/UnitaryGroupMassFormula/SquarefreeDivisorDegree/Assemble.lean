import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.SqfDivDegOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.FibreNonempty

namespace PI.SqfDivDeg.W

theorem sqfDivDeg_of_rootDense (hA : RootDense) : PI.SqfDivDeg.Claim :=
  sqfDivDeg_of hA mainCount

end PI.SqfDivDeg.W

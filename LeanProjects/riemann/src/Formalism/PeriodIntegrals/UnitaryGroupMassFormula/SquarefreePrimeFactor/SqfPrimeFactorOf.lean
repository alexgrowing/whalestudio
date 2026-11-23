import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.ClaimOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.SquarefreeCountEstimate
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.IrreducibleCountLowerBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.Analytic

namespace PI.SqfPrimeFactor.W

theorem sqfPrimeFactor_of (hRS : PI.PrimesDyadicRS.Claim) : PI.SqfPrimeFactor.Claim :=
  claim_of squarefree_count_estimate irreducible_count_lower_bound (analytic_of hRS)

end PI.SqfPrimeFactor.W

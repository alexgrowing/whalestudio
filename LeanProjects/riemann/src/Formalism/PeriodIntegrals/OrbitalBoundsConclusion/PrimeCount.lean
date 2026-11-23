import Mathlib
import Formalism.PeriodIntegrals.PrimeCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.ChebyshevPrimeBoundsLogFact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.CountSuccLe

theorem prime_count_bound : PI.PrimeCountBound :=
  PI.PC.primeCountBound_of 131072 (PI.PC.pcLarge_of PI.PC.psiUpperBound_holds) PI.PC.pcSmall

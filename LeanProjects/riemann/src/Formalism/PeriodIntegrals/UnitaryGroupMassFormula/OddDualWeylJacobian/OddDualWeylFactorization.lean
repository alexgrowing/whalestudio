import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.RevColOneTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.TransvectionMulApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightMultiplicity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacobiMinorIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.MnrUpdateEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightDualOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.AevalMulHomog
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.EvalDuality
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.ExistsEqMulOfColumnSpanLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.DegreeBalance
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightVectorUnique

namespace PI.OddDualWeyl

theorem odd_dual_weyl_factorization {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ)
    (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam :=
  oddDualWeyl_of rowOpIntertwining highest_weight_multiplicity highest_weight_divisibility hermitianDiagonalization lowestWeightMem (highestWeightDual_of jacobiMinorReverse) weight_homomorphism degreeBalance
    evalDuality highest_weight_vector_unique columnSpanDual reverseSignUnit twistedWeylStep O m lam

end PI.OddDualWeyl

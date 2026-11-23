import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOneInduction

namespace PI.KLW

theorem kerLocIso_of_normOne (h : NormOne) : PI.KerIso.LocIso := lattice_reduction (lattice_from_norm_one h)

end PI.KLW

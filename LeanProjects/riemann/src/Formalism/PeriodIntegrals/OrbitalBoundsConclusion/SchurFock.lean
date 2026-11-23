import Formalism.PeriodIntegrals.SchurFock
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.SchurFockOf

theorem schur_fock : PI.SchurFock := PI.WSF.schurFock_of highest_weight_irreducible

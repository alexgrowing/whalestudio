import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NotIntAllOfLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.TrDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGSmall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.T2SpaceOfNonarchimedeanLocalField
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.DApprox
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NormGOfLocDiff

theorem count_not_integral : PI.CntLocalParts.NotIntAll :=
  have hD : PI.CntNotIntW.LocDiff :=
    PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
      (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
      PI.CntNotIntW.small_powers_bound
  PI.CntNotIntW.notIntAll_of_loc (PI.CntNotIntW.locGen_of hD PI.CntNotIntW.dual_lattice_powers)
    (PI.CntNotIntW.normG_of_locDiff hD)

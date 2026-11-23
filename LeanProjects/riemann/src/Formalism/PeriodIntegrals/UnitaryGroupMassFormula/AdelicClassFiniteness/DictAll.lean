import Mathlib
import Formalism.PeriodIntegrals.AdelClassFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictInter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictTop

namespace PIW.AdelClassFin

theorem lattice_intersection' : LInter := lInter_of dual_intersection
theorem lattice_denominator : LDenom := lDenom_of dual_denominator
theorem lattice_dense : LDense := lDense_of dual_dense
theorem dual_hat_lattice : LHatDual := lHatDual_of dual_intersection lattice_denominator lattice_dense dual_hat_integral
theorem lattice_m_is_lattice : MLat := mLat_of lattice_intersection' lattice_denominator
theorem lattice_m_generation : MGen := mGen_of lattice_denominator lattice_dense
theorem lattice_m_dual : MDual := mDual_of dual_intersection dual_hat_integral dual_hat_lattice lattice_m_generation
theorem lattice_map_injective : MInj := mInj_of lattice_m_generation

theorem stDict : StDict := stDict_of lattice_m_is_lattice lattice_m_dual lattice_map_injective lattice_m_equiv

end PIW.AdelClassFin

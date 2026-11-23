import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.FibreShapeOf

theorem Formalism.L2.SG.MassRatio.mass_ratio_euler_eq : Formalism.L2.SG.MassRatio.EulerEq :=
  CMEul.eulerEq_of_fib (CMEulFib.stepFib_of CMEul.euler_factor_conjugate)

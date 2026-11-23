import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.TorusEigenvalueFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.ModelMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred

theorem modelIso_of : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso :=
  fun hp hu hh => PI.WMI.modelIso_of_steps (PI.WMI.polyExt_of hp hu) PI.WMI.lambda_integrality
    PI.WMI.torus_eigenvalue_formula PI.WMI.lower_triangular_invariance PI.WMI.model_map_equivariance PI.WMI.determinant_splitting_formula hh

theorem polynomial_model_iso (hp : PI.PolyCoef) (hu : PI.UnitaryDense) : PI.ModelIso :=
  modelIso_of hp hu highest_weight_irreducible

import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelIntegralValue
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelCellContinuous
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelLineZero
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EisensteinS2LimitFormulaOfHkLimit
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorEvenTheta
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AreaCov
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.GoodModelLatticeGen

namespace Formalism.L2.Th1.F

theorem hkSummable : HkSummable := hecke_kernel_summable
theorem hkRowIntegral : HkRowIntegral := hecke_kernel_line_integral
theorem hkCellBound : HkCellBound := hecke_kernel_cell_bound
theorem hkCellCont : HkCellCont := hecke_kernel_cell_continuous
theorem hkIntZero : HkIntZero := hecke_kernel_integral_zero
theorem hkIntValue : HkIntValue := hecke_kernel_integral_value
theorem hkJRules : HkJRules := hecke_kernel_j_rules
theorem hkRowZero : HkRowZero := hecke_kernel_line_zero
theorem hkIntLimit : HkIntLimit := hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules
theorem hkLimit : HkLimit :=
  hkLimit_of hecke_kernel_summable hecke_kernel_line_integral hecke_kernel_cell_bound hecke_kernel_cell_continuous hecke_kernel_integral_zero
    hecke_kernel_line_zero (hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules)
theorem eisenstein_s2_limit_formula : EisensteinS2LimitFormula := eisensteinS2LimitFormula_of_hkLimit hkLimit
theorem taylorTh0 : TaylorTh0 := taylor_even_theta
theorem areaCovolume : AreaCovolume := area_covolume
theorem uSerLattice : USerLattice := u_series_lattice
theorem goodModelLattice : GoodModelLattice := good_model_lattice

end Formalism.L2.Th1.F

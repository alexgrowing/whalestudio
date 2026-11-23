import Development.EtaleCohomology.WeilConjectures.AdicFinPf
import Development.EtaleCohomology.KummerTheory.AdicLimPfGlue
import Development.EtaleCohomology.KummerTheory.AdicAlgPf
import Development.EtaleCohomology.KummerTheory.AdicDegPf

namespace LateralTheory.Fin.AdicDeg
theorem etale_adic_cohomology_finiteness_holds : LateralTheory.KummerTheory.AdicFin := by
  apply LateralTheory.EWeil.AdicFinPf.AdicFin_of
theorem etale_adic_inverse_limit_comparison_holds : LateralTheory.KummerTheory.AdicLim := by
  apply LateralTheory.KummerTheory.AdicLim_of_fin <;> first | exact etale_adic_cohomology_finiteness_holds
theorem etale_adic_algebraic_comparison_holds : LateralTheory.KummerTheory.AdicAlg := by
  apply LateralTheory.KummerTheory.AdicAlg_of
theorem etale_adic_degree_bound_of_adic_finiteness : LateralTheory.KummerTheory.AdicDeg := by
  apply LateralTheory.KummerTheory.AdicDeg_of <;> first | exact etale_adic_inverse_limit_comparison_holds | exact etale_adic_algebraic_comparison_holds
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.AdicDeg := etale_adic_degree_bound_of_adic_finiteness
end LateralTheory.Fin.AdicDeg

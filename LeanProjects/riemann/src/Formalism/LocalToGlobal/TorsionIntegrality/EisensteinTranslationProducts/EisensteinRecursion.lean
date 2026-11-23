import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bridge
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MkLeOfDenseRange
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Universal

namespace Formalism.L2.Th1.F

theorem wpNumDen : WpNumDen := weierstrass_numerator_denominator
theorem pOfIsWp : POfIsWp := weierstrass_p_of_series
theorem pOfLattice : POfLattice := weierstrass_p_of_lattice
theorem curveBridge : CurveBridge := curve_weierstrass_series_eq
theorem iotaExists : IotaExists := iotaExists_thm
theorem sigmaUniversal : SigmaUniversal := sigma_universal
theorem hasCMByIsogeny : HasCMByIsogeny := hasCMByIsogeny_of' isogenyFormulaInstance

end Formalism.L2.Th1.F

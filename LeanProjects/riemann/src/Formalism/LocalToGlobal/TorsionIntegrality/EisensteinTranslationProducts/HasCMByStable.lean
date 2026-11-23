import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HasCMByIsogenyOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaScale

namespace Formalism.L2.Th1.F

theorem hasCMByStable : HasCMByStable := has_cm_stable
theorem hasCMByScale : HasCMByScale := has_cm_scale
theorem cmPairHasCMBy : CmPairHasCMBy := cm_pair_has_cm
theorem jInvScale : JInvScale := j_invariant_scale
theorem seriesScale : SeriesScale := series_scale
theorem sigmaScale : SigmaScale := sigma_scale'
theorem seriesMap : SeriesMap := series_map

end Formalism.L2.Th1.F

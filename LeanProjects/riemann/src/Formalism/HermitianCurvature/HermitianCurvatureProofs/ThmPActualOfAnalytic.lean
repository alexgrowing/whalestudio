import Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfIsHaarOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

noncomputable section

namespace Formalism.FourierDecayAlt.P5

theorem thmPActualOfAnalytic (hE : HerAnalyticEAll) : ThmPActual :=
  thmPActualOfE Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hE

theorem thmPActualOfHerC (hAn : HerAnalyticCAll) : ThmPActual :=
  thmPActualOfZ Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hAn

theorem thmPActualOfCore (hF : HerAnalyticFAll) : ThmPActual :=
  thmPActualOfCoreMZ Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt topDensMeasAll hF

end Formalism.FourierDecayAlt.P5

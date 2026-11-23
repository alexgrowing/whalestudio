import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnlyOfLeviCurve
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianPartLevi

namespace Formalism.FourierDecayAlt.P

theorem z_only : LevelPointCoordinates.ZOnly :=
  z_only_of_levi_curve levi_curve hermitian_part_levi

end Formalism.FourierDecayAlt.P

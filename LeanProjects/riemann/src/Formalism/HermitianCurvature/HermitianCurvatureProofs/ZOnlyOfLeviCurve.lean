import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnlyOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointEntryContDiffOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeOperatorClass

namespace Formalism.FourierDecayAlt.P

theorem z_only_of_levi_curve (hC : WirtingerOperators.CurveLevi) (hH : WirtingerOperators.HpartLevi) : LevelPointCoordinates.ZOnly :=
  WirtingerOperators.zOnly_of_parts hC hH xi_coefficient xi_coefficient_vector xiMem_statement xi_smooth
    right_derivative_operator_class wirtinger_slice_smooth

end Formalism.FourierDecayAlt.P

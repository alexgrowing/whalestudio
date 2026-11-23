import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfLeaves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopLocalBuiltPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatioAlt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift

namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_head_top (hH : Formalism.FourierDecayAlt.KB.HeadTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := fun hA =>
  built_bounds_compact_of_leaves radial_head hH degree_of_lift_pairing top_local_built_places degree_top
    top_ratio (germ_parts_compact_support kernel_continuity_built germ_rate_bound hA)
    (fun hA' => uniform_decay_of_place hA' radial_head hH
      (uniform_decay_of_heads radial_head hH)) hA

end Formalism.FourierDecayAlt.P

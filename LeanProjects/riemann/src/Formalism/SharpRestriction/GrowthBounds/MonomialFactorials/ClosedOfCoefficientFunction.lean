import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryFinitenessWindowLevelDimOnAdmissible
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDecompProved

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_coefficient_function (D : Formalism.BasicNotions.D7) (hF : RestFunY) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_symmetric_finite D (restYbc_of_funY hF) hO h

end Formalism.MainNotions.G.SymmetricFormBlocks

end

import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthBasisLat
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.OrthBasisLatOf

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_orthogonal_splitting (D : Formalism.BasicNotions.D7) (hS : OrthSplit) (hG : GoodLeSmall) (h : RestWinE D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  integralityFromMetric_of_orthBasisLat D (orthBasisLat_of freeLat_proved hS) hG h

end Formalism.MainNotions.G.SymmetricFormBlocks

end

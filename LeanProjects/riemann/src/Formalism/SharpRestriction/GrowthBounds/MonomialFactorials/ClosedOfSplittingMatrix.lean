import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOrthogonalSplitting
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.GoodLeSmallMat

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_splitting_matrix (D : Formalism.BasicNotions.D7) (hS : OrthSplit) (hM : GoodLeSmallMat) (h : RestWinE D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_orthogonal_splitting D hS (goodLeSmall_of hM) h

end Formalism.MainNotions.G.SymmetricFormBlocks

end

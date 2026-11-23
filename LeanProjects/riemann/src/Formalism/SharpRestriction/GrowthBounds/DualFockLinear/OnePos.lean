import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RowGenCoeffZero
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ThetaInjHd

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

theorem onePos_of_opBound (hOB : OpBound) (hT : RestTheta) (hW : RestWt) : OnePos :=
  onePos_of hOB restAdj restStab hT hW restRep restRep2

end Formalism.MainNotions.TestSideCounting

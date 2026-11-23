import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryWindowOnAdmissible
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CmapMemRestrictSupport

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_orthogonal_lattice (D : Formalism.BasicNotions.D7) (hO : OrthLat) (h : SymmetryWindowOnAdmissible D) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_symmetric_dims D restFunY_proved hO h

end Formalism.MainNotions.G.SymmetricFormBlocks

end

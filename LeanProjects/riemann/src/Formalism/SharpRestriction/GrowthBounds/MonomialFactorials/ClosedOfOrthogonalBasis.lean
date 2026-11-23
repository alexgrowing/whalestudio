import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOrthogonalLattice
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.OrthCountOf

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_orthogonal_basis (D : Formalism.BasicNotions.D7) (hB : OrthBasisLat) (hG : GoodLeSmall) (h : SymmetryWindowOnAdmissible D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_orthogonal_lattice D (orthLat_of' hB hG) h

end Formalism.MainNotions.G.SymmetricFormBlocks

end

import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoMinorIntegrality
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedLatticeSum

noncomputable section

namespace Formalism.MainNotions.LatticeSumConvergence

theorem LatSum_holds : Formalism.MainNotions.KTwoMinorIntegrality.LatSum :=
  fun ι _ P R hR hsep => Formalism.MainNotions.WeightedLatticeSum.latSum ι P R hR hsep

end Formalism.MainNotions.LatticeSumConvergence

end

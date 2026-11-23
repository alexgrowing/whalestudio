import Formalism.FilteredPoleLength.ReducedBasisBounds.LocalStepLevelsExt
import Formalism.FilteredPoleLength.LocalDescentLevels.LengthResidueFieldBase
import Formalism.FilteredPoleLength.LocalDescentLevels.LevelsChain

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem levelsLengthSum : LevelsLengthSum := by
  intro O' _ _ ι _ Rr A _ _ _ _ _ _ _ _ x mm n F r R h0 hn hmono hinj hlen hsum
  rw [Module.length_pi_of_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h := filteredPoleLength O' (Rr z) (A z) (x z) (mm z) (n z) (F z) (r z) (h0 z) (hn z)
    (hmono z) (hinj z) (hlen z)
  rw [h, hsum z]

end Formalism.LatticeBaseChangeAlt

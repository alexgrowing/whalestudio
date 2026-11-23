import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaTrivialV
import GroundTheory.PAdicHodge.ExtRobbaBezout
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Module PhiModule

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}
  [CompleteSpace L] [IsAlgClosed L]

instance instIsBezoutRobbaTilde : IsBezout T.RobbaTilde := T.isBezout_robbaTilde

namespace TeichFrob

variable (F : T.TeichFrob)

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

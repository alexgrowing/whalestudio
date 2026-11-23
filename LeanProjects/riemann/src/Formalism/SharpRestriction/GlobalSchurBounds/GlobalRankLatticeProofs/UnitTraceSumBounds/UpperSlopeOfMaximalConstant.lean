import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdSlopeLow
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

namespace Formalism.MainNotions.flipTwoThree

theorem stdSlopeLow_holds : StdSlopeLow := standard_slope_lower

theorem hookBound_holds : HookBound := hook_length_bound

theorem lower_slope_of_column_slope (D : Formalism.BasicNotions.D7) (hC : ColSlopeEq D) : SlopeLowerOpenPart D := slopeLowerOpen_of_std_hook stdSlopeLow_holds hookBound_holds D hC

end Formalism.MainNotions.flipTwoThree

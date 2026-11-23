import ReciprocityTheory.SemistableReduction.SemiDeg
import ReciprocityTheory.SemistableReduction.SemiContract
import ReciprocityTheory.SemistableReduction.LatAll

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed

import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

abbrev oT {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) : IdF (sP Q).A := stdI Q (some 0) 0

abbrev oB {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) : IdF (sP Q).A := stdI Q none 0

end CrystallineSemistableComparison.Pb

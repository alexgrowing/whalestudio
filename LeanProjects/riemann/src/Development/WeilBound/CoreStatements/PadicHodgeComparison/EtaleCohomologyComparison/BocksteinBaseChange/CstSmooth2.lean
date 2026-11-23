import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SumCoord
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicCyclicCup.LAdicPassageNarrowDuality

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

theorem cstSmooth_of_side (h : EtSideS) : CstSmooth := cstSmooth_of_p Pb.pSeam h

theorem cstSmooth (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : CstSmooth := cstSmooth_of_side (etSideS h4 h8)

end CrystallineSemistableComparison

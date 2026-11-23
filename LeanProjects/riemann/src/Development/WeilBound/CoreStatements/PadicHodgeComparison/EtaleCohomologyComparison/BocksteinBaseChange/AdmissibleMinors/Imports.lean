import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.MemOfMulIsU
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.RedSum
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.FilRZero

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

theorem inj : ComparisonInjectiveStrict := by
  intro l _ K R G P hR hE
  exact Inj.reduce P hR hE (fun M N u hu n r => Inj.filR_pull (Model.genMap u hu) (Model.genMap_q u hu) n r)
    (fun M hM d hc n => Inj.conn P hR hE M hM d hc n)

end CrystallineSemistableComparison

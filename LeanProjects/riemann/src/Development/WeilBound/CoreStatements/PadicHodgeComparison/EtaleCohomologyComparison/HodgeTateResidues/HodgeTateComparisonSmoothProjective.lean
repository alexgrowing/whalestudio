import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HtOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.DlogClassExistsUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LvLink
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Formal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.HT

theorem hodgeTate_of_etale_side (h : EtSideS) : HodgeTateMapExists := ht_of lvEx kFin dlog_class_exists_unique kTop h

theorem hodgeTate_comparison_smooth_projective (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : HodgeTateMapExists :=
  hodgeTate_of_etale_side fun l _ K _ => (etSide (zIn formalIn h4 h8) l K).1

end CrystallineSemistableComparison.HT

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClosingTrueCols
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Cv

theorem row_level_valuations : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  refine Row0.row (H := EvC fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u)
    (validForConstructedPointClasses_eventuallyWorkingClass (EvP.of_all fun _ K _ β hβ => ?_)) Lk
  refine GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u) ?_ K β
    (hQ _ _ _ _ _ hβ)
  intro B f T w Z O nch hv hs _ u
  rw [hv.tw_eq]
  exact GlobalTheory.LvT.Built.TrueCols.closing_true_cols w.I w.ok hv.jets hs w.l Z w.l0 O.X u

end GlobalTheory.Fc.Cv

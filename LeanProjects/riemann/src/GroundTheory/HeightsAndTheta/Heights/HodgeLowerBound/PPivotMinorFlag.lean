import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPivotMinorFlag
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem PivotMinorFlag.full : PivotMinorFlag.Statement := by
  intro R _ n M a b hab
  exact ⟨⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩, pivotMinor_eq_flagMinor M a b hab⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree

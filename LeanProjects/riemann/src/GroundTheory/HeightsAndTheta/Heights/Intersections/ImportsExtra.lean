import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ContinuousMinorRatioLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

theorem pullbackPushforward_holds.proof (hGen : BlockGenFinite.Statement) (hIsol : FibreIsolFinite.Statement) :
    pullbackPushforward_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv hP' hP hΨ
  exact ⟨fun j => pullbackPushforward_holds.pullBad_null R hGen hv hP' hP Ψ hΨ j,
    fun y => pullbackPushforward_holds.pullFib_finite R hIsol hv hP' hP Ψ hΨ y⟩

end GroundTheory.Heights₂.Heights.Inter

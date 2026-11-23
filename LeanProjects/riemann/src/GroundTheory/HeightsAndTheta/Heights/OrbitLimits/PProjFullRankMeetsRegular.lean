import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjFullRankMeetsRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRankTransfer
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjMaxRankRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ProjFullRankMeetsRegular.of_found (hT : ProjRankTransfer.Statement)
    (hM : ProjMaxRankMeetsPsi0.Statement) (hR : ProjMaxRankRegular.Statement) :
    ProjFullRankMeetsRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y, hyc, hy⟩ := hT K ι P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y', hyc', hy', h0⟩ := hM K ι P J n R Ψ V BV hH y hy
  refine ⟨y', ?_, hR K ι P J n R Ψ V BV hH y' hy' h0⟩
  rw [connectedComponent_eq hyc]
  exact hyc'

end GroundTheory.Heights₂.Heights.Targets

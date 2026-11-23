import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegularClosureOpen
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjFullRankMeetsRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ProjFullRankDense.of_found (hOpen : ProjRegularClosureOpen.Statement)
    (hMeet : ProjFullRankMeetsRegular.Statement) : ProjFullRankDense.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y, hyc, hy⟩ := hMeet K ι P J n R Ψ V BV hH hC hΨ x hx
  have hO : IsOpen (closure (projRegular R Ψ BV)) := hOpen K ι P J n R Ψ V BV hH
  have hcl : IsClopen (closure (projRegular R Ψ BV)) := ⟨isClosed_closure, hO⟩
  rw [hO.interior_eq]
  have hsub := hcl.connectedComponent_subset (subset_closure hy)
  rw [← connectedComponent_eq hyc] at hsub
  exact hsub mem_connectedComponent

end GroundTheory.Heights₂.Heights.Targets

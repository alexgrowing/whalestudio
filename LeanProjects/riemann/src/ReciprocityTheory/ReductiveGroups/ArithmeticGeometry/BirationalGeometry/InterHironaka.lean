import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterResExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedZ

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem resExists_of_hironaka (h : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC ∧ ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE) :
    ResExistsStatement :=
  resExists_of_projLogRes (ReciprocityTheory.AnForm.R.projLogResC_of_C h.1 h.2) h.2 pcRadical pcEquidim pcMinContract
    jacNotInP pcContract

section

variable (h : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC ∧ ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
include h

theorem stokes_of_hironaka : StokesStatement :=
  stokes_of_resolution (resExists_of_hironaka h) resBridge

theorem poincareLelong_of_hironaka (hPush : ResDivPushStatement) : ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution_pushforward (resExists_of_hironaka h) resBridge hPush

end

end ReciprocityTheory.ChartRestriction.G.Geo

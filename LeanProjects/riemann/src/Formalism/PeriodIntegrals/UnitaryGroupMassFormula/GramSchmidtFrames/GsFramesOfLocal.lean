import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.PartEq

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

theorem gsFrames_of_local (hL : GfLocal) : GsFrames :=
  gsFrames_of_gf gfBase gfSat gfStab hL

end PI.UnitaryGroupMassFormula.GsFr

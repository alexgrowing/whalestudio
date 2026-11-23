import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.ThetaSeriesExistence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocGlob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GlueHoldsVar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GWGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocalAssemblyPrincipal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemMain

namespace PI.ScRefExists.Top

open PI.ScRefExists.Sk

theorem target_of_wframe (h : WFrame) : PI.ScRefExists.Target :=
  target_of_steps PI.ScRefExists.GlueC.glue_holds_var PI.ScRefExists.TH.theta_series_existence
    PI.ScRefExists.Id.idemLift PI.ScRefExists.LG.local_global_principle_alt
    (PI.ScRefExists.GWG.globW_of (gwpp_of h PI.ScRefExists.PPA.local_assembly_principal)
      PI.ScRefExists.GWG.chinese_remainder_gluing)

end PI.ScRefExists.Top

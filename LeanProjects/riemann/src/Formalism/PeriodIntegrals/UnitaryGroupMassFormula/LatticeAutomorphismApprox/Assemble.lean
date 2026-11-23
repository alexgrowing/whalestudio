import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocalIdempotentExistence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.GlueHoldsVar

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

theorem scXuExists_of (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) : _root_.PI.ScXuExists.Target :=
  target_of' local_idempotent_existence hS hA hB existsLatticeAutomorphismApprox Gl.glue_holds_var

end PI.UnitaryGroupMassFormula.ScXuExists

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.WeylForKOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.TypePlOf

noncomputable section

namespace PI.WeylForKWork

theorem weylForK_of_leaves (hB : Blocks) (hBD : BlockDiag) (hT : TorusWt) (hW : WtUniq) (hM : MinIrr)
    (hC : CDomRes) (hD : DimStep) (hF : FormulaStep) : PI.WeylForU → PI.WeylForK := by
  exact fun hU => weylForK_of_steps hB (typePl_of hB hBD hT hW hM hC) (typeMi_of hB hBD hT hW hM hC)
    hD hF hU

end PI.WeylForKWork

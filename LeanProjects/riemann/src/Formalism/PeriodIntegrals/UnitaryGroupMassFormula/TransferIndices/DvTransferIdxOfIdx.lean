import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.BlockMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.SumIndexFormula

noncomputable section

namespace PI.Dv.TIW

theorem dvTransferIdx_of_idx (hI : PI.Dv.IdxCalc) (hG : GrpData) : ∃ C : ℝ, PI.Dv.Conclusion4b C :=
  ⟨1, dvTransferIdx_of (block_index_formula hI) (sum_index_formula hI) hG volume_nonneg volume_finite' volume_sum_le⟩

end PI.Dv.TIW

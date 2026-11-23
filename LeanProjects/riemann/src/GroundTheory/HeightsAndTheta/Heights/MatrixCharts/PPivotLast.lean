import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem PivotLast.proof (hPI : PivotInvDiag.Statement) : PivotLast.Statement := by
  intro d S hS x
  have h1 := MCCusp.sq_le_inv_diag_mul_qf hS x (Fin.last d)
  have h2 := hPI d S hS
  have hpos : 0 < S⁻¹ (Fin.last d) (Fin.last d) := hS.inv.diag_pos
  have hp : 0 < pivot S d := by
    by_contra hc
    push_neg at hc
    have := mul_nonpos_of_nonneg_of_nonpos hpos.le hc
    linarith
  calc x (Fin.last d) ^ 2 * pivot S d
      ≤ (S⁻¹ (Fin.last d) (Fin.last d) * MCSchur.qf S x) * pivot S d :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ = MCSchur.qf S x * (S⁻¹ (Fin.last d) (Fin.last d) * pivot S d) := by ring
    _ = MCSchur.qf S x := by rw [h2, mul_one]

end

end GroundTheory.Heights₂.Heights

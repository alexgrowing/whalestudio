import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramSubLast.proof : IntGramSubLast.Statement := by
  intro d k S M hM
  ext i j
  simp only [intGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.submatrix_apply, Fin.sum_univ_castSucc, hM, Int.cast_zero, zero_mul, mul_zero,
    add_zero]

end

end GroundTheory.Heights₂.Heights

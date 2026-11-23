import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramQf.proof : IntGramQf.Statement := by
  intro d k S N z
  simp only [MCSchur.qf, intGram, ← mulVec_mulVec]
  rw [dotProduct_mulVec, vecMul_transpose]

end

end GroundTheory.Heights₂.Heights

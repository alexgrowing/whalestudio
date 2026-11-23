import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem LeadMinorLeading.proof : LeadMinorLeading.Statement := by
  intro d S m h j hj
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.submatrix_apply]
  have ha : (a : ℕ) < m := lt_of_lt_of_le a.2 hj
  have hb : (b : ℕ) < m := lt_of_lt_of_le b.2 hj
  rw [dif_pos ⟨ha, hb⟩, dif_pos ⟨ha.trans_le h, hb.trans_le h⟩]
  rfl

end

end GroundTheory.Heights₂.Heights

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem LeadMinorBasic.proof : LeadMinorBasic.Statement := by
  intro d S
  refine ⟨?_, ?_, ?_⟩
  · simp [leadMinor]
  · unfold leadMinor
    congr 1
    ext a b
    simp only [Matrix.of_apply]
    rw [dif_pos ⟨a.2, b.2⟩]
  · intro hS i hi
    have e : (Matrix.of fun a b : Fin i =>
        if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) =
        S.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [dif_pos ⟨a.2.trans_le hi, b.2.trans_le hi⟩]
      rfl
    unfold leadMinor
    rw [e]
    exact (hS.submatrix (Fin.castLE_injective hi)).det_pos

end

end GroundTheory.Heights₂.Heights

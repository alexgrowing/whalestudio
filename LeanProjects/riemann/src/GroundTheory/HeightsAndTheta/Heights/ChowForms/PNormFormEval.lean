import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormEval.proof : NormFormEval.Statement := by
  intro R S _ _ _ _ _ n η u
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R S)]
  unfold normForm
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end GroundTheory.Heights₂.Heights

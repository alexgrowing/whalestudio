import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramUnimodular.proof : IntGramUnimodular.Statement := by
  intro d k S N U hU
  have hmap : (N * U).map (Int.cast : ℤ → ℝ) =
      N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have hdet : (U.map (Int.cast : ℤ → ℝ)).det = ((U.det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det U).symm
  have hsq : ((U.det : ℤ) : ℝ) * (U.det : ℝ) = 1 := by
    rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num
  unfold intGram
  rw [hmap, transpose_mul]
  have e : (U.map (Int.cast : ℤ → ℝ))ᵀ * (N.map (Int.cast : ℤ → ℝ))ᵀ * S *
      (N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ)) =
      (U.map (Int.cast : ℤ → ℝ))ᵀ * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)) *
        U.map (Int.cast : ℤ → ℝ) := by
    simp only [Matrix.mul_assoc]
  rw [e, det_mul, det_mul, det_transpose, hdet]
  calc (U.det : ℝ) * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det * (U.det : ℝ)
      = ((U.det : ℤ) : ℝ) * (U.det : ℝ) *
          ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det := by ring
    _ = _ := by rw [hsq, one_mul]

end

end GroundTheory.Heights₂.Heights

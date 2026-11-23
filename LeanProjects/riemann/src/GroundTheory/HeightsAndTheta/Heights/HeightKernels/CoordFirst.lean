import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

theorem sq_coord_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (hY : Y.PosDef)
    (i : ι) (v : ι → ℝ) : v i ^ 2 ≤ Y⁻¹ i i * qf Y v := by
  have hU : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hsymm : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set w : ι → ℝ := Y⁻¹ *ᵥ Pi.single i 1 with hw
  have hYw : Y *ᵥ w = Pi.single i 1 := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hwY : ∀ x : ι → ℝ, w ⬝ᵥ (Y *ᵥ x) = x i := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hYw]
    simp [dotProduct, Pi.single_apply]
  have hxY : ∀ x : ι → ℝ, x ⬝ᵥ (Y *ᵥ w) = x i := by
    intro x
    rw [hYw]
    simp [dotProduct, Pi.single_apply]
  have hwi : w i = Y⁻¹ i i := by
    rw [hw]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hpos : 0 < Y⁻¹ i i := hY.inv.diag_pos
  have hnn : ∀ t : ℝ, 0 ≤ qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
    intro t
    have h0 : 0 ≤ (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) := by
      have := hY.posSemidef.dotProduct_mulVec_nonneg (v - t • w)
      simpa using this
    have hexp : (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) =
        qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hwY, hwY, hxY, hwi]
      simp only [qf]
      ring
    linarith
  have h := hnn (v i / Y⁻¹ i i)
  have hne : Y⁻¹ i i ≠ 0 := ne_of_gt hpos
  have e : qf Y v - 2 * (v i / Y⁻¹ i i) * v i + (v i / Y⁻¹ i i) ^ 2 * Y⁻¹ i i =
      qf Y v - v i ^ 2 / Y⁻¹ i i := by
    field_simp
    ring
  rw [e] at h
  have h2 : v i ^ 2 / Y⁻¹ i i ≤ qf Y v := by linarith
  rwa [div_le_iff₀ hpos, mul_comm] at h2

end KCoord

theorem FirstCoordinateBound.intersectionNumber_baseChange : FirstCoordinateBound.Statement := by
  intro g _ Y hY v
  have h := KCoord.sq_coord_le Y hY 0 v
  rw [div_le_iff₀ hY.inv.diag_pos, mul_comm]
  exact h

end GroundTheory.Heights₂.Heights

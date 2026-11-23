import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.HermValueIsLeast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCCusp

open Matrix GroundTheory.Heights₂.Heights.MCSchur

noncomputable section

section QF

variable {ι : Type*} [Fintype ι]

theorem dot_mulVec_symm {Z : Matrix ι ι ℝ} (hZ : Zᵀ = Z) (u w : ι → ℝ) :
    u ⬝ᵥ (Z *ᵥ w) = w ⬝ᵥ (Z *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hZ, dotProduct_comm]

theorem transpose_eq_of_posSemidef {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) : Zᵀ = Z := by
  have := hZ.1
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

theorem qf_nonneg {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u : ι → ℝ) : 0 ≤ qf Z u := by
  have := hZ.dotProduct_mulVec_nonneg u
  simpa [qf] using this

theorem bil_sq_le {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u w : ι → ℝ) :
    (w ⬝ᵥ (Z *ᵥ u)) ^ 2 ≤ qf Z w * qf Z u := by
  have hs := transpose_eq_of_posSemidef hZ
  have key : ∀ x : ℝ, 0 ≤ qf Z w * (x * x) + (-2 * (w ⬝ᵥ (Z *ᵥ u))) * x + qf Z u := by
    intro x
    have h := qf_nonneg hZ (u - x • w)
    have e : qf Z (u - x • w) = qf Z w * (x * x) + (-2 * (w ⬝ᵥ (Z *ᵥ u))) * x + qf Z u := by
      simp only [qf, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [dot_mulVec_symm hs u w]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

variable [DecidableEq ι]

theorem sq_le_inv_diag_mul_qf {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (x : ι → ℝ) (i : ι) :
    x i ^ 2 ≤ Z⁻¹ i i * qf Z x := by
  have hs := transpose_eq_of_posSemidef hZ.posSemidef
  have hu : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit
  set w := Z⁻¹ *ᵥ Pi.single i 1 with hw
  have hZw : Z *ᵥ w = Pi.single i 1 := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have h1 : w ⬝ᵥ (Z *ᵥ x) = x i := by
    rw [dot_mulVec_symm hs, hZw, dotProduct_single, mul_one]
  have h2 : qf Z w = Z⁻¹ i i := by
    rw [qf, hZw, dotProduct_single, mul_one, hw, mulVec_single]
    simp
  have := bil_sq_le hZ.posSemidef x w
  rwa [h1, h2] at this

theorem inv_diag_le {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (i : ι) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, ε * x i ^ 2 ≤ qf Z x) : Z⁻¹ i i ≤ 1 / ε := by
  have hs := transpose_eq_of_posSemidef hZ.posSemidef
  have hu : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit
  set w := Z⁻¹ *ᵥ Pi.single i 1 with hw
  have hZw : Z *ᵥ w = Pi.single i 1 := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hwi : w i = Z⁻¹ i i := by rw [hw, mulVec_single]; simp
  have h2 : qf Z w = Z⁻¹ i i := by rw [qf, hZw, dotProduct_single, mul_one, hwi]
  have hpos : 0 < Z⁻¹ i i := hZ.inv.diag_pos
  have := h w
  rw [h2, hwi] at this
  rw [le_div_iff₀ hε]
  nlinarith

end QF

end

end GroundTheory.Heights₂.Heights.MCCusp

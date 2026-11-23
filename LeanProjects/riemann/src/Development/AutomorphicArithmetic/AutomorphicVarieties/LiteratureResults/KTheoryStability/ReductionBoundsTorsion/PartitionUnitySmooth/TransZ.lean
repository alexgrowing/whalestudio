import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.MzMulEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Gramlow

open Matrix

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem isHermitian_real_smul_add_real_smul {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (l : ℝ) (hl : 0 < l)
    (h : ∀ c : Fin n → ℤ, c ≠ 0 → l ≤ TZ.cz c ⬝ᵥ G *ᵥ TZ.cz c) :
    l ^ n ≤ (4 * (n : ℝ)) ^ n * G.det := by
  have h1 := UpperTheory.V.KT.gramlow (Fin n) (l⁻¹ • G) (hG.smul (inv_pos.2 hl)) (fun c hc => by
    have hc' := h c hc
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, le_inv_mul_iff₀ hl, mul_one]
    exact hc')
  rw [Matrix.det_smul, Fintype.card_fin, inv_pow] at h1
  have hln : 0 < l ^ n := pow_pos hl n
  calc l ^ n = l ^ n * 1 := (mul_one _).symm
    _ ≤ l ^ n * ((4 * (n : ℝ)) ^ n * ((l ^ n)⁻¹ * G.det)) := mul_le_mul_of_nonneg_left h1 hln.le
    _ = (4 * (n : ℝ)) ^ n * G.det := by field_simp

private theorem v_sub_one_add_le_v_pow_l_sub_one (n : ℕ) (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G.PosDef)
    (δ : ℝ) (hδ : 0 < δ) (hD : TZ.Dual G δ) :
    ∃ v : Fin (n + 1) → ℤ, v ≠ 0 ∧
      TZ.cz v ⬝ᵥ G *ᵥ TZ.cz v ≤ 2 * (4 * ((n : ℝ) + 1)) ^ 2 / δ := by
  by_contra hne
  push_neg at hne
  have hdet := hG.det_pos
  have ha : 0 < 4 * ((n : ℝ) + 1) := by positivity
  have h1 := isHermitian_real_smul_add_real_smul G hG (2 * (4 * ((n : ℝ) + 1)) ^ 2 / δ) (by positivity)
    (fun c hc => (hne c hc).le)
  have h2 := isHermitian_real_smul_add_real_smul G⁻¹ hG.inv δ hδ hD
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h2
  push_cast at h1 h2
  have key := mul_le_mul h1 h2 (by positivity) (by positivity)
  rw [← mul_pow, div_mul_cancel₀ _ hδ.ne'] at key
  have e : (4 * ((n : ℝ) + 1)) ^ (n + 1) * G.det * ((4 * ((n : ℝ) + 1)) ^ (n + 1) * (G.det)⁻¹)
      = ((4 * ((n : ℝ) + 1)) ^ 2) ^ (n + 1) := by
    calc _ = ((4 * ((n : ℝ) + 1)) ^ (n + 1)) ^ 2 * (G.det * (G.det)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hdet.ne', mul_one, pow_right_comm]
  rw [e, mul_pow] at key
  have hX : 0 < ((4 * ((n : ℝ) + 1)) ^ 2) ^ (n + 1) := by positivity
  have h2p : (2 : ℝ) ≤ 2 ^ (n + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

theorem pf_TransZ : TransZ := by
  intro d
  obtain ⟨C, hC, h⟩ := TZ.core (fun n => 2 * (4 * ((n : ℝ) + 1)) ^ 2) (fun n => by positivity)
    (fun n G hG δ hδ hD => v_sub_one_add_le_v_pow_l_sub_one n G hG δ hδ hD) d
  exact ⟨C, hC, fun ι _ _ hι G hG δ hδ hD => TZ.reidx h ι hι G hG δ hδ hD⟩

end PositivityTheory.KB.SmoothPartitionUnityBasic

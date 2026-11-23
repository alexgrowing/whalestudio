import ReciprocityTheory.SemistableReduction.ShareBallA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

def sbDp (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 1 else 0

def sbDn (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 0 else 1

theorem sb_signMat_eq (p r : ℕ) : signMat p r = sbDp p r - sbDn p r := by
  simp only [signMat, sgn, sbDp, sbDn, diagonal_sub]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_add_Dn (p r : ℕ) : sbDp p r + sbDn p r = 1 := by
  simp only [sbDp, sbDn, diagonal_add]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dp (p r : ℕ) : sbDp p r * sbDp p r = sbDp p r := by
  simp only [sbDp, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dn (p r : ℕ) : sbDn p r * sbDn p r = sbDn p r := by
  simp only [sbDn, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dn (p r : ℕ) : sbDp p r * sbDn p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dp (p r : ℕ) : sbDn p r * sbDp p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_herm (p r : ℕ) : (sbDp p r)ᴴ = sbDp p r := by
  simp only [sbDp, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_Dn_herm (p r : ℕ) : (sbDn p r)ᴴ = sbDn p r := by
  simp only [sbDn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_herm (p r : ℕ) : (signMat p r)ᴴ = signMat p r := by
  simp only [signMat, sgn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_mul_J (p r : ℕ) : signMat p r * signMat p r = 1 := by
  simp only [signMat, sgn, diagonal_mul_diagonal]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = normSq (sbDp p r *ᵥ u) := by
  simp only [posSq, normSq, sbDp, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = normSq (sbDn p r *ᵥ u) := by
  simp only [negSq, normSq, sbDn, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_herm_swap {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : Mᴴ = M) (v w : Fin r → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by
  rw [star_mulVec, hM, dotProduct_mulVec]

theorem sb_dot_Dp (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDp p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dp_herm p r) v (sbDp p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dp_mul_Dp] at h
  exact h

theorem sb_dot_Dn (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDn p r *ᵥ w) = star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dn_herm p r) v (sbDn p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dn_mul_Dn] at h
  exact h

theorem sb_dot_split (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ w = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) +
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [← sb_dot_Dp p v w, ← sb_dot_Dn p v w, ← dotProduct_add, ← add_mulVec, sb_Dp_add_Dn,
    one_mulVec]

theorem sb_dot_J (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (signMat p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) -
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [sb_signMat_eq, sub_mulVec, dotProduct_sub, sb_dot_Dp p v w, sb_dot_Dn p v w]

private theorem re_star_dotProduct_self_eq_normSq {r : ℕ} (x : Fin r → ℂ) : (star x ⬝ᵥ x).re = normSq x := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, normSq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (star (x k) * x k).re = (x k).re * (x k).re + (x k).im * (x k).im := by
    simp [Complex.mul_re] <;> ring
  rw [h1, ← Complex.normSq_apply]
  first
    | exact (Complex.sq_norm _).symm
    | exact Complex.normSq_eq_norm_sq _
    | simp [Complex.sq_abs]

theorem sb_re_dot_J (p : ℕ) {r : ℕ} (v : Fin r → ℂ) :
    (star v ⬝ᵥ (signMat p r *ᵥ v)).re = posSq p v - negSq p v := by
  rw [sb_dot_J, Complex.sub_re, re_star_dotProduct_self_eq_normSq, re_star_dotProduct_self_eq_normSq, sb_posSq_eq, sb_negSq_eq]

theorem sb_cs {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re ^ 2 ≤ normSq v * normSq w := by
  have h1 : |(star v ⬝ᵥ w).re| ≤ ∑ k, ‖v k‖ * ‖w k‖ := by
    have e1 : |(star v ⬝ᵥ w).re| ≤ ‖star v ⬝ᵥ w‖ := by
      first
        | exact Complex.abs_re_le_norm _
        | exact RCLike.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
    have e2 : ‖star v ⬝ᵥ w‖ ≤ ∑ k, ‖star (v k) * w k‖ := by
      unfold dotProduct
      exact norm_sum_le _ _
    have e3 : ∑ k, ‖star (v k) * w k‖ = ∑ k, ‖v k‖ * ‖w k‖ := by
      simp [norm_mul, norm_star]
    linarith
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖v k‖) (fun k => ‖w k‖)
  have h3 : (star v ⬝ᵥ w).re ^ 2 ≤ (∑ k, ‖v k‖ * ‖w k‖) ^ 2 :=
    sq_le_sq.mpr (h1.trans (le_abs_self _))
  unfold normSq
  exact h3.trans h2

private theorem two_mul_one_add_mul_le_of_le_mul (a b c d s : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hcd : c ≤ s * d) (hs1 : s < 1) (hle : a * c ≤ b * d) :
    2 * (1 + s) * (a * c) ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
  rcases eq_or_lt_of_le hd with h0 | hdpos
  · subst h0
    have hc0 : c = 0 := le_antisymm (by simpa using hcd) hc
    subst hc0
    nlinarith [mul_nonneg hs (sq_nonneg a), sq_nonneg b]
  · have hsq : (a * c) * (a * c) ≤ (b * d) * (b * d) :=
      mul_self_le_mul_self (mul_nonneg ha hc) hle
    have hdc : 0 ≤ d - c := by nlinarith
    have hsdc : 0 ≤ s * d - c := by linarith
    have e1 : 0 ≤ (s * d ^ 2 + c ^ 2) * (a - d) ^ 2 :=
      mul_nonneg (add_nonneg (mul_nonneg hs (sq_nonneg d)) (sq_nonneg c)) (sq_nonneg _)
    have e2 : 0 ≤ 2 * a * d * ((d - c) * (s * d - c)) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two ha) hd) (mul_nonneg hdc hsdc)
    have hd2 : 0 < d ^ 2 := pow_pos hdpos 2
    by_contra hneg
    push_neg at hneg
    have e3 := mul_lt_mul_of_pos_left hneg hd2
    nlinarith

theorem sb_real_bounds (a b c d s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hs1 : s < 1) (hba : b ≤ s * a) (hcd : c ≤ s * d) (h1 : |t| ≤ a * c)
    (h2 : |t| ≤ b * d) :
    0 ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 + 2 * (1 + s) * t ∧
      0 ≤ s * (a ^ 2 + d ^ 2) - (b ^ 2 + c ^ 2) - 2 * (1 - s) * t := by
  have hTc : |t| ≤ a * c := h1
  have hTad : |t| ≤ s * a * d := by
    have := mul_le_mul_of_nonneg_left hcd ha
    nlinarith
  have hs0 : 0 ≤ 1 - s := by linarith
  have key : 2 * (1 + s) * |t| ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
    rcases le_total (a * c) (b * d) with hle | hle
    · have e := two_mul_one_add_mul_le_of_le_mul a b c d s ha hc hd hs hcd hs1 hle
      have e' := mul_le_mul_of_nonneg_left hTc (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
    · have e := two_mul_one_add_mul_le_of_le_mul d c b a s hd hb ha hs hba hs1
        (by rw [mul_comm d b, mul_comm c a]; exact hle)
      have e' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
  have htl : 0 ≤ t + |t| := by linarith [neg_abs_le t]
  have htu : t ≤ |t| := le_abs_self t
  have hb2 : b * b ≤ (s * a) * (s * a) := mul_self_le_mul_self hb hba
  have hc2 : c * c ≤ (s * d) * (s * d) := mul_self_le_mul_self hc hcd
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + s)) htl]
  · nlinarith [mul_nonneg (mul_nonneg hs hs0) (sq_nonneg (a - d)),
      mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ s * a * d - t)]

end ReciprocityTheory.MultiplicativeHeights

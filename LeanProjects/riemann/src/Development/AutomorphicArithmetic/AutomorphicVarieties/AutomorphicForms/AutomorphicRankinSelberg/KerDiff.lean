import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperHalfPlane Set

namespace UpperTheory.V.Af.Rs

private lemma kd_pow {a b t m : ℝ} (hm : 1 ≤ m) (hb : m / 2 ≤ b) (hab : b ≤ a) (ht : 2 ≤ t) (ht' : t ≤ 4) :
    |a ^ (-t) - b ^ (-t)| ≤ 128 * (a - b) * m ^ (-3 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  set A := a ^ t with hA
  set B := b ^ t with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos ha0 t
  have hBpos : 0 < B := Real.rpow_pos_of_pos hb0 t
  have hneg_a : a ^ (-t) = A⁻¹ := Real.rpow_neg ha0.le t
  have hneg_b : b ^ (-t) = B⁻¹ := Real.rpow_neg hb0.le t
  have hBA : B ≤ A := Real.rpow_le_rpow hb0.le hab (by linarith)
  have hbern : 1 + t * (b / a - 1) ≤ B / A := by
    have h := one_add_mul_self_le_rpow_one_add (s := b / a - 1)
      (by have := div_nonneg hb0.le ha0.le; linarith) (p := t) (by linarith)
    rw [show 1 + (b / a - 1) = b / a by ring, Real.div_rpow hb0.le ha0.le] at h
    exact h
  have hsub : |a ^ (-t) - b ^ (-t)| = B⁻¹ - A⁻¹ := by
    rw [hneg_a, hneg_b, abs_sub_comm, abs_of_nonneg]
    rw [sub_nonneg]
    exact inv_anti₀ hBpos hBA
  have hkey : B⁻¹ - A⁻¹ ≤ t * (a - b) / b / B := by
    have h1 : B⁻¹ - A⁻¹ = (1 - B / A) / B := by field_simp
    have h2 : 1 - B / A ≤ t * (a - b) / b := by
      have h3 : t * (1 - b / a) ≤ t * (a - b) / b := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [one_sub_div ha0.ne']
        exact div_le_div_of_nonneg_left (by linarith) hb0 hab
      nlinarith
    rw [h1]
    exact div_le_div_of_nonneg_right h2 hBpos.le
  have hbB : m ^ 3 / 32 ≤ b * B := by
    have e1 : (m / 2) ^ (t + 1) ≤ b ^ (t + 1) := Real.rpow_le_rpow (by positivity) hb (by linarith)
    have e2 : b ^ (t + 1) = b * B := by rw [Real.rpow_add_one hb0.ne']; ring
    have e3 : (m / 2) ^ (t + 1) = m ^ (t + 1) / 2 ^ (t + 1) := Real.div_rpow hm0.le (by norm_num) _
    have e4 : m ^ (3 : ℝ) ≤ m ^ (t + 1) := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
    have e5 : (2 : ℝ) ^ (t + 1) ≤ 2 ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have e6 : (2 : ℝ) ^ (5 : ℝ) = 32 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have e7 : m ^ (3 : ℝ) = m ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2pos : 0 < (2 : ℝ) ^ (t + 1) := by positivity
    have h8 : m ^ 3 / 32 ≤ m ^ (t + 1) / 2 ^ (t + 1) := by
      rw [div_le_div_iff₀ (by norm_num) h2pos]
      have hm3 : 0 ≤ m ^ 3 := by positivity
      rw [← e7] at hm3 ⊢
      rw [e6] at e5
      nlinarith
    linarith
  have hm3pos : 0 < m ^ 3 := by positivity
  have hmneg : m ^ (-3 : ℝ) = (m ^ 3)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hsub, hmneg]
  refine hkey.trans ?_
  rw [div_div]
  have hbBpos : 0 < b * B := by positivity
  rw [div_le_iff₀ hbBpos]
  have hab' : 0 ≤ a - b := by linarith
  have : t * (a - b) ≤ 4 * (a - b) := by nlinarith
  have h32 : 128 * (a - b) * (m ^ 3)⁻¹ * (m ^ 3 / 32) = 4 * (a - b) := by
    field_simp
    ring
  have hc : 0 ≤ 128 * (a - b) * (m ^ 3)⁻¹ := by positivity
  calc t * (a - b) ≤ 4 * (a - b) := this
    _ = 128 * (a - b) * (m ^ 3)⁻¹ * (m ^ 3 / 32) := h32.symm
    _ ≤ 128 * (a - b) * (m ^ 3)⁻¹ * (b * B) := mul_le_mul_of_nonneg_left hbB hc

private lemma kd_abs (x : Fin 2 → ℤ) (i : Fin 2) : |(x i : ℝ)| ≤ ‖x‖ := by
  have := norm_le_pi_norm x i
  rwa [Int.norm_eq_abs] at this

private lemma kd_one {x : Fin 2 → ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (kd_abs x i)

private lemma kd_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    1 ≤ z.re ^ 2 + z.im ^ 2 ∧ -(1 / 2) ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 1 / 2 ≤ z.im := by
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy := z.im_pos
  obtain ⟨h1, h2⟩ := hz
  rw [Complex.normSq_apply] at h1
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1 h2
  rw [abs_le] at h2
  refine ⟨by nlinarith, h2.1, h2.2, by nlinarith⟩

private lemma kd_low (x : Fin 2 → ℤ) {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    ‖x‖ / 2 ≤ ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := kd_fd hz
  set c : ℝ := (x 0 : ℝ)
  set d : ℝ := (x 1 : ℝ)
  have hsq : ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ 2 = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [c, d]
    ring
  have hmax : ‖x‖ ≤ max |c| |d| := by
    rw [pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))]
    intro i
    rw [Int.norm_eq_abs]
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hN : ‖x‖ ^ 2 ≤ c ^ 2 + d ^ 2 := by
    have hN0 := norm_nonneg x
    rcases le_max_iff.mp hmax with h | h
    · have : ‖x‖ ^ 2 ≤ |c| ^ 2 := pow_le_pow_left₀ hN0 h 2
      rw [sq_abs] at this
      nlinarith
    · have : ‖x‖ ^ 2 ≤ |d| ^ 2 := pow_le_pow_left₀ hN0 h 2
      rw [sq_abs] at this
      nlinarith
  have hcd : |2 * c * d * z.re| ≤ |c * d| := by
    rw [show 2 * c * d * z.re = (c * d) * (2 * z.re) by ring, abs_mul]
    have : |2 * z.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc |c * d| * |2 * z.re| ≤ |c * d| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |c * d| := mul_one _
  have hcd2 : 2 * |c * d| ≤ c ^ 2 + d ^ 2 := by
    rw [abs_mul]
    have := sq_nonneg (|c| - |d|)
    nlinarith [sq_abs c, sq_abs d]
  have hlow : (‖x‖ / 2) ^ 2 ≤ ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ 2 := by
    rw [hsq]
    have e : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 = c ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * c * d * z.re + d ^ 2 := by ring
    rw [e]
    have := neg_abs_le (2 * c * d * z.re)
    have hc2 : c ^ 2 ≤ c ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
      nlinarith [sq_nonneg c]
    nlinarith
  have hw0 := norm_nonneg ((x 0 : ℂ) * z + (x 1 : ℂ))
  nlinarith [norm_nonneg x]

private lemma kd_up (x : Fin 2 → ℤ) {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ≤ 4 * ‖x‖ * z.im := by
  obtain ⟨h1, h2, h3, h4⟩ := kd_fd hz
  have hz' : ‖(z : ℂ)‖ ≤ 1 / 2 + z.im := by
    have := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    rw [abs_of_pos z.im_pos] at this
    have : |z.re| ≤ 1 / 2 := abs_le.mpr ⟨h2, h3⟩
    linarith
  have hN0 := norm_nonneg x
  calc ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ≤ ‖(x 0 : ℂ)‖ * ‖(z : ℂ)‖ + ‖(x 1 : ℂ)‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ ‖x‖ * (1 / 2 + z.im) + ‖x‖ := by
        rw [Complex.norm_intCast, Complex.norm_intCast]
        have a0 := kd_abs x 0
        have a1 := kd_abs x 1
        have := norm_nonneg (z : ℂ)
        nlinarith [abs_nonneg ((x 0 : ℤ) : ℝ)]
    _ ≤ 4 * ‖x‖ * z.im := by nlinarith

private lemma kd_ker (s : ℝ) (x : Fin 2 → ℤ) (z : ℍ) :
    ker s x z = z.im ^ s * ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ (-(2 * s)) := by
  unfold ker
  have hy := z.im_pos
  rw [Complex.normSq_eq_norm_sq, Real.div_rpow hy.le (by positivity),
    Real.rpow_neg (norm_nonneg _), Real.rpow_mul (norm_nonneg _), div_eq_mul_inv]
  norm_num

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.kerDiff :
    UpperTheory.V.Af.Rs.KerDiff := by
  refine ⟨1024, by norm_num, ?_⟩
  intro s hs x x' hx hx' z hz
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨-, -, -, hy2⟩ := kd_fd hz
  have hy : 0 < z.im := z.im_pos
  rw [kd_ker, kd_ker]
  set w : ℂ := (x 0 : ℂ) * z + (x 1 : ℂ) with hw
  set w' : ℂ := (x' 0 : ℂ) * z + (x' 1 : ℂ) with hw'
  set S : ℝ := ‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ) with hS
  have hS1 : 0 ≤ ‖x‖ ^ (-3 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hS2 : 0 ≤ ‖x'‖ ^ (-3 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hS0 : 0 ≤ S := by positivity
  have hdiff : ‖w‖ - ‖w'‖ ≤ 4 * ‖x - x'‖ * z.im ∧ ‖w'‖ - ‖w‖ ≤ 4 * ‖x - x'‖ * z.im := by
    have e : w - w' = (((x - x') 0 : ℤ) : ℂ) * z + (((x - x') 1 : ℤ) : ℂ) := by
      simp only [hw, hw', Pi.sub_apply, Int.cast_sub]
      ring
    have hu := kd_up (x - x') hz
    rw [← e] at hu
    have h1 := abs_norm_sub_norm_le w w'
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hD : |‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s))| ≤ 128 * (4 * ‖x - x'‖ * z.im) * S := by
    rcases le_total ‖w'‖ ‖w‖ with h | h
    · have := kd_pow (kd_one hx') (kd_low x' hz) h (by linarith : (2 : ℝ) ≤ 2 * s) (by linarith)
      calc _ ≤ 128 * (‖w‖ - ‖w'‖) * ‖x'‖ ^ (-3 : ℝ) := this
        _ ≤ 128 * (4 * ‖x - x'‖ * z.im) * ‖x'‖ ^ (-3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hS2
            linarith [hdiff.1]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have := norm_nonneg (x - x')
            positivity
    · rw [abs_sub_comm]
      have := kd_pow (kd_one hx) (kd_low x hz) h (by linarith : (2 : ℝ) ≤ 2 * s) (by linarith)
      calc _ ≤ 128 * (‖w'‖ - ‖w‖) * ‖x‖ ^ (-3 : ℝ) := this
        _ ≤ 128 * (4 * ‖x - x'‖ * z.im) * ‖x‖ ^ (-3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hS1
            linarith [hdiff.2]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have := norm_nonneg (x - x')
            positivity
  have hys : z.im ^ s ≤ 2 * z.im ^ 2 := by
    rcases le_total z.im 1 with h | h
    · have h1 : z.im ^ s ≤ z.im ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy h hs1
      rw [Real.rpow_one] at h1
      nlinarith
    · have h1 : z.im ^ s ≤ z.im ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs2
      rw [Real.rpow_two] at h1
      nlinarith
  have hyspos : 0 ≤ z.im ^ s := Real.rpow_nonneg hy.le _
  rw [← mul_sub, abs_mul, abs_of_nonneg hyspos]
  calc z.im ^ s * |‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s))|
      ≤ (2 * z.im ^ 2) * (128 * (4 * ‖x - x'‖ * z.im) * S) :=
        mul_le_mul hys hD (abs_nonneg _) (by positivity)
    _ = 1024 * ‖x - x'‖ * z.im ^ 3 * S := by ring

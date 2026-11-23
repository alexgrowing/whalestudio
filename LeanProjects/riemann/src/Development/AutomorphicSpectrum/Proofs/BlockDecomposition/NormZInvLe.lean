import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntPR

open Complex
open UpperHalfPlane hiding I

lemma cpow_ne' {x : ℂ} (hx : x ≠ 0) (w : ℂ) : x ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hx]; exact Complex.exp_ne_zero _

lemma normSq_pos' (z : ℍ) : 0 < ‖(z : ℂ)‖ ^ 2 := by
  have : (z : ℂ) ≠ 0 := z.ne_zero
  positivity

lemma im_le_norm (z : ℍ) : z.im ≤ ‖(z : ℂ)‖ := by
  exact (le_abs_self _).trans (Complex.abs_im_le_norm (z : ℂ))

lemma w_im (z : ℍ) : (-1 / (z : ℂ)).im = z.im / ‖(z : ℂ)‖ ^ 2 := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [neg_div, one_div, Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
  simp [neg_div]

lemma w_im_pos (z : ℍ) : 0 < (-1 / (z : ℂ)).im := by
  rw [w_im]; exact div_pos z.im_pos (normSq_pos' z)

lemma u_eq (w : ℂ) : ((w.im : ℂ) - I * (w.re : ℂ)) = -I * w := by
  apply Complex.ext <;> simp

lemma norm_u (w : ℂ) : ‖((w.im : ℂ) - I * (w.re : ℂ))‖ = ‖w‖ := by
  rw [u_eq]; simp

lemma norm_w (z : ℍ) : ‖(-1 / (z : ℂ))‖ = ‖(z : ℂ)‖⁻¹ := by
  simp

lemma re_u (Y T : ℝ) : ((Y : ℂ) - I * (T : ℂ)).re = Y := by simp

lemma u_ne {Y : ℝ} (hY : 0 < Y) (T : ℝ) : ((Y : ℂ) - I * (T : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_u] at this
  simp at this
  exact hY.ne' this

lemma v_eq (Y T : ℝ) : ((Y : ℂ) + I * (T : ℂ)) = (starRingEnd ℂ) ((Y : ℂ) - I * (T : ℂ)) := by
  apply Complex.ext <;> simp

lemma v_ne {Y : ℝ} (hY : 0 < Y) (T : ℝ) : ((Y : ℂ) + I * (T : ℂ)) ≠ 0 := by
  rw [v_eq]; exact (map_ne_zero _).2 (u_ne hY T)

lemma arg_u_ne {Y : ℝ} (hY : 0 < Y) (T : ℝ) : Complex.arg ((Y : ℂ) - I * (T : ℂ)) ≠ Real.pi := by
  intro h
  have := Complex.arg_eq_pi_iff.1 h
  rw [re_u] at this
  linarith [this.1]

lemma norm_KK (α β : ℂ) {Y : ℝ} (hY : 0 < Y) (T : ℝ) (h : α.im = β.im) :
    ‖KK α β Y T‖ = ‖((Y : ℂ) - I * (T : ℂ))‖ ^ (-(α + β).re) := by
  have hr : 0 < ‖((Y : ℂ) - I * (T : ℂ))‖ := norm_pos_iff.2 (u_ne hY T)
  unfold KK
  rw [norm_mul, Complex.norm_cpow_of_ne_zero (u_ne hY T), Complex.norm_cpow_of_ne_zero (v_ne hY T),
    v_eq, Complex.arg_conj, if_neg (arg_u_ne hY T), Complex.norm_conj, Complex.add_re, neg_add,
    Real.rpow_add hr]
  simp only [Complex.neg_re, Complex.neg_im, h]
  rw [div_mul_div_comm, ← Real.exp_add]
  have : Complex.arg ((Y : ℂ) - I * (T : ℂ)) * -β.im + -Complex.arg ((Y : ℂ) - I * (T : ℂ)) * -β.im = 0 := by ring
  rw [this]; simp

lemma one_le_Ht (z : ℍ) : z.im ≤ Ht z ∧ z.im⁻¹ ≤ Ht z ∧ 1 ≤ Ht z := by
  have hy := z.im_pos
  have hn := im_le_norm z
  have hsq : z.im ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by gcongr
  have h1 : z.im ≤ Ht z := by
    unfold Ht
    rw [le_div_iff₀ hy]; nlinarith
  have h2 : z.im⁻¹ ≤ Ht z := by
    unfold Ht
    rw [inv_eq_one_div]
    gcongr
    nlinarith [sq_nonneg ‖(z : ℂ)‖]
  refine ⟨h1, h2, ?_⟩
  rcases le_total 1 z.im with h | h
  · exact h.trans h1
  · exact (one_le_inv₀ hy |>.2 h).trans h2

lemma w_im_le (z : ℍ) : (-1 / (z : ℂ)).im ≤ z.im⁻¹ := by
  have hy := z.im_pos
  have hn := im_le_norm z
  have hsq : z.im ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by gcongr
  rw [w_im, inv_eq_one_div, div_le_div_iff₀ (normSq_pos' z) hy]
  nlinarith

lemma w_im_inv_le (z : ℍ) : (-1 / (z : ℂ)).im⁻¹ ≤ Ht z := by
  have hy := z.im_pos
  rw [w_im, inv_div]
  unfold Ht
  gcongr
  linarith

lemma div_L_im (z : ℍ) (L : ℕ) : (-1 / (z : ℂ) / (L : ℂ)).im = (-1 / (z : ℂ)).im / L := by
  simpa using Complex.div_natCast_im (-1 / (z : ℂ)) L

lemma norm_z_inv_le (z : ℍ) : ‖(z : ℂ)‖⁻¹ ≤ Ht z :=
  (inv_anti₀ z.im_pos (im_le_norm z)).trans (one_le_Ht z).2.1

lemma norm_pref (L k ν : ℕ) (hL : 0 < L) (s : ℂ) (z : ℍ) :
    ‖pref L k ν s z‖ = z.im ^ (om k ν s).re * (L : ℝ) ^ (-(s.re + 1 / 2)) * ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2) := by
  have hα : (al k ν s).im = (be k ν s).im := by simp [al, be]
  have hsum : (al k ν s + be k ν s).re = s.re + 1 / 2 := by
    simp [al, be]; ring
  unfold pref
  rw [norm_div, norm_mul, norm_KK _ _ (w_im_pos z) _ hα, norm_u, norm_w, hsum,
    Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos, Complex.norm_natCast_cpow_of_pos hL,
    Real.rpow_neg (by positivity) (s.re + 1 / 2), div_inv_eq_mul]
  simp

lemma pref_diff (L k ν : ℕ) (hL : 0 < L) (z : ℍ) : Differentiable ℂ fun s => pref L k ν s z := by
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hu := u_ne (w_im_pos z) (-1 / (z : ℂ)).re
  have hv := v_ne (w_im_pos z) (-1 / (z : ℂ)).re
  intro s
  unfold pref KK al be om
  refine DifferentiableAt.div (DifferentiableAt.mul ?_ ?_) (DifferentiableAt.mul ?_ ?_) ?_
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hy)
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hLc)
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hu)
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hv)
  · exact mul_ne_zero (cpow_ne' hu _) (cpow_ne' hv _)

lemma pref_meas (L k ν : ℕ) (s : ℂ) : Measurable (pref L k ν s) := by
  have hc : Measurable (fun z : ℍ => (z : ℂ)) := UpperHalfPlane.continuous_coe.measurable
  have hw : Measurable (fun z : ℍ => -1 / (z : ℂ)) := measurable_const.div hc
  have him : Measurable (fun z : ℍ => (((-1 / (z : ℂ)).im : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Complex.measurable_im.comp hw)
  have hre : Measurable (fun z : ℍ => (((-1 / (z : ℂ)).re : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Complex.measurable_re.comp hw)
  have hy : Measurable (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Complex.measurable_im.comp hc)
  unfold pref KK
  exact ((hy.pow_const _).mul_const _).div
    (((him.sub (measurable_const.mul hre)).pow_const _).mul
      ((him.add (measurable_const.mul hre)).pow_const _))

lemma pref_bound (L k ν : ℕ) (hL : 0 < L) (b : ℝ) :
    ∃ (C : ℝ) (A : ℕ), ∀ (s : ℂ) (z : ℍ), 0 ≤ s.re → s.re ≤ b →
      ‖pref L k ν s z‖ ≤ C * Real.exp (C * s.im ^ 2) * Ht z ^ A := by
  refine ⟨1, ⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊, fun s z h0 hb => ?_⟩
  obtain ⟨h1, -, hH⟩ := one_le_Ht z
  have hH0 : 0 ≤ Ht z := zero_le_one.trans hH
  have hom : (om k ν s).re = (s.re + k + ν + 1) / 2 := by simp [om]
  have e1 : 0 ≤ (om k ν s).re := by rw [hom]; positivity
  have e2 : 0 ≤ s.re + 1 / 2 := by linarith
  have b1 : z.im ^ (om k ν s).re ≤ Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    refine (Real.rpow_le_rpow z.im_pos.le h1 e1).trans (Real.rpow_le_rpow_of_exponent_le hH ?_)
    rw [hom]
    exact le_trans (by linarith) (Nat.le_ceil _)
  have b2 : (L : ℝ) ^ (-(s.re + 1 / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL) (by linarith)
  have b3 : ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2) ≤ Ht z ^ (⌈b + 1 / 2⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    refine (Real.rpow_le_rpow (by positivity) (norm_z_inv_le z) e2).trans
      (Real.rpow_le_rpow_of_exponent_le hH ?_)
    exact le_trans (by linarith) (Nat.le_ceil _)
  have n1 : 0 ≤ z.im ^ (om k ν s).re := Real.rpow_nonneg z.im_pos.le _
  have n2 : 0 ≤ (L : ℝ) ^ (-(s.re + 1 / 2)) := by positivity
  have n3 : 0 ≤ ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2) := by positivity
  have hexp : 1 ≤ Real.exp (1 * s.im ^ 2) := Real.one_le_exp (by positivity)
  have hP : 0 ≤ Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊) := pow_nonneg hH0 _
  rw [norm_pref L k ν hL]
  calc z.im ^ (om k ν s).re * (L : ℝ) ^ (-(s.re + 1 / 2)) * ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2)
      ≤ Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ : ℕ) * 1 * Ht z ^ (⌈b + 1 / 2⌉₊ : ℕ) := by
        gcongr
    _ = Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊) := by rw [mul_one, pow_add]
    _ ≤ 1 * Real.exp (1 * s.im ^ 2) * Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊) := by
        rw [one_mul]
        exact le_mul_of_one_le_left hP hexp

theorem pr : PR := by
  intro L k ν hL
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨pref_diff L k ν hL, pref_meas L k ν, pref_bound L k ν hL, fun z => ?_⟩
  obtain ⟨-, h2, h3⟩ := one_le_Ht z
  have hY := w_im_pos z
  refine ⟨h3, h2, ?_, ?_, ?_⟩
  · rw [div_L_im]; exact div_pos hY hL0
  · rw [div_L_im]
    exact (div_le_self hY.le hLr).trans ((w_im_le z).trans h2)
  · rw [div_L_im, inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (w_im_inv_le z) hL0.le

end GlobalTheory.CompanionTheory.HalfIntPR

end

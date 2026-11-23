import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf

noncomputable section

namespace PI.PC

open Real MeasureTheory Set

def phi (t : ℝ) : ℝ := Chebyshev.theta t / (t * log t ^ 2)

theorem phi_integrableOn {p : ℝ} (q : ℝ) (hp : 2 ≤ p) : IntegrableOn phi (Icc p q) volume := by
  have h : IntegrableOn (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2)) (Icc 2 q) volume :=
    Chebyshev.integrableOn_theta_div_id_mul_log_sq q
  exact h.mono_set (Icc_subset_Icc_left hp)

theorem phi_intervalIntegrable {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    IntervalIntegrable phi volume p q := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mpr (phi_integrableOn q hp)

theorem piece {p q c : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) (hc : 0 < c) (hcp : c ≤ log p) :
    ∫ t in p..q, phi t ≤ log 4 / c ^ 2 * (q - p) := by
  have hconst : ∀ t ∈ Icc p q, phi t ≤ log 4 / c ^ 2 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlogt : c ≤ log t := le_trans hcp (Real.log_le_log (by linarith) ht.1)
    have hlpos : 0 < log t := lt_of_lt_of_le hc hlogt
    have hθ : Chebyshev.theta t ≤ log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
    have hθ0 : 0 ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
    have hl4 : 0 ≤ log 4 := Real.log_nonneg (by norm_num)
    have hc2 : c ^ 2 ≤ log t ^ 2 := pow_le_pow_left₀ hc.le hlogt 2
    unfold phi
    rw [div_le_div_iff₀ (mul_pos ht0 (pow_pos hlpos 2)) (pow_pos hc 2)]
    calc Chebyshev.theta t * c ^ 2 ≤ (log 4 * t) * log t ^ 2 :=
          mul_le_mul hθ hc2 (sq_nonneg c) (mul_nonneg hl4 ht0.le)
      _ = log 4 * (t * log t ^ 2) := by ring
  have hint_r : IntervalIntegrable (fun _ : ℝ => log 4 / c ^ 2) volume p q := intervalIntegrable_const
  calc ∫ t in p..q, phi t ≤ ∫ t in p..q, log 4 / c ^ 2 :=
        intervalIntegral.integral_mono_on hpq (phi_intervalIntegrable hp hpq) hint_r hconst
    _ = log 4 / c ^ 2 * (q - p) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem dyadic (k : ℕ) : ∫ t in (2 : ℝ)..2 ^ (k + 1), phi t ≤
    2 / log 2 * ∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hl2' : log 2 ≠ 0 := hl2.ne'
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have ha : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hb : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (phi_intervalIntegrable (le_refl 2) ha) (phi_intervalIntegrable ha hb)
    have hpiece : ∫ t in (2 : ℝ) ^ (k + 1)..2 ^ (k + 1 + 1), phi t ≤
        log 4 / (((k : ℝ) + 1) * log 2) ^ 2 * (2 ^ (k + 1 + 1) - 2 ^ (k + 1)) :=
      piece ha hb (mul_pos (by positivity) hl2)
        (by rw [Real.log_pow]; norm_num)
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have heq : log 4 / (((k : ℝ) + 1) * log 2) ^ 2 * (2 ^ (k + 1 + 1) - 2 ^ (k + 1)) =
        2 / log 2 * ((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
      rw [h4]; first | (field_simp; ring) | field_simp
    rw [← hsplit, Finset.sum_range_succ, mul_add]
    linarith

theorem int_small : ∫ t in (2 : ℝ)..1024, phi t ≤ 61 := by
  have h := dyadic 9
  have h1024 : (2 : ℝ) ^ (9 + 1) = 1024 := by norm_num
  rw [h1024] at h
  have hs : ∑ i ∈ Finset.range 9, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 ≤ 20.9 := by
    norm_num [Finset.sum_range_succ]
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hb : 2 / log 2 * ∑ i ∈ Finset.range 9, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 ≤ 61 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  linarith

def gg (t : ℝ) : ℝ := 1.56 * (t / log t ^ 2) + 0.7 * log t

def gg' (t : ℝ) : ℝ := 1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t

theorem gg_hasDerivAt {t : ℝ} (ht : 1 < t) : HasDerivAt gg (gg' t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (Real.log_pos ht).ne'
  have hL : HasDerivAt log t⁻¹ t := Real.hasDerivAt_log ht0
  have hsq := hL.mul hL
  have hq := (hasDerivAt_id' t).div hsq (mul_ne_zero hl hl)
  have h := (hq.const_mul (1.56 : ℝ)).add (hL.const_mul (0.7 : ℝ))
  have hfun : gg = fun y => 1.56 * (y / (log y * log y)) + 0.7 * log y := by
    funext y; simp only [gg]; ring
  have hd : 1.56 * ((1 * (log t * log t) - t * (t⁻¹ * log t + log t * t⁻¹)) / (log t * log t) ^ 2)
      + 0.7 * t⁻¹ = gg' t := by
    show _ = 1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t
    first | (field_simp; ring) | field_simp
  rw [hfun]
  exact h.congr_deriv hd

theorem chebyshevPrimeBounds_log_fact : log 1024 = 10 * log 2 := by
  rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num

theorem int_tail (hU : CHUpper) {x : ℝ} (hx : 1024 ≤ x) :
    ∫ t in (1024 : ℝ)..x, phi t ≤ gg x - gg 1024 := by
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hpt : ∀ t ∈ Icc (1024 : ℝ) x, phi t ≤ gg' t := by
    intro t ht
    have ht1 : (1024 : ℝ) ≤ t := ht.1
    have ht0 : 0 < t := by linarith
    have ht0' : t ≠ 0 := ht0.ne'
    have hL : 10 * log 2 ≤ log t := by
      rw [← chebyshevPrimeBounds_log_fact]; exact Real.log_le_log (by norm_num) ht1
    have hLpos : 0 < log t := by linarith
    have hL0 : log t ≠ 0 := hLpos.ne'
    have hψ := hU t (by linarith)
    have hθ := Chebyshev.theta_le_psi t
    unfold phi gg'
    rw [div_le_iff₀ (mul_pos ht0 (pow_pos hLpos 2))]
    have e : (1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t) * (t * log t ^ 2) =
        1.56 * t - 1.56 * 2 * t / log t + 0.7 * log t ^ 2 := by
      first | (field_simp; ring) | field_simp
    rw [e]
    have h3 : 1.56 * 2 * t / log t ≤ 0.4544 * t := by
      rw [div_le_iff₀ hLpos]
      nlinarith [mul_le_mul_of_nonneg_left hL ht0.le, mul_lt_mul_of_pos_left hl2 ht0]
    linarith
  have hderiv : ∀ t ∈ uIcc (1024 : ℝ) x, HasDerivAt gg (gg' t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact gg_hasDerivAt (by linarith [ht.1])
  have hcont : ContinuousOn gg' (uIcc 1024 x) := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hl2' : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    have hl3 : log t ^ 3 ≠ 0 := pow_ne_zero 3 hl
    apply ContinuousAt.continuousWithinAt
    show ContinuousAt (fun s : ℝ => 1.56 * (1 / log s ^ 2 - 2 / log s ^ 3) + 0.7 / s) t
    fun_prop (disch := assumption)
  have hint_r : IntervalIntegrable gg' volume 1024 x := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_r
  have hmono : ∫ t in (1024 : ℝ)..x, phi t ≤ ∫ t in (1024 : ℝ)..x, gg' t :=
    intervalIntegral.integral_mono_on hx (phi_intervalIntegrable (by norm_num) hx) hint_r hpt
  exact hmono.trans_eq hftc

theorem gg_1024_nonneg : 0 ≤ gg 1024 := by
  have hl : 0 < log (1024 : ℝ) := Real.log_pos (by norm_num)
  have h1 : 0 ≤ (1024 : ℝ) / log 1024 ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  unfold gg
  linarith

theorem card_pr (y : ℝ) : (pr y).card = Nat.primeCounting ⌊y⌋₊ := by
  simp only [PI.pr, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  try (congr 1; ext p; simp)

theorem log_131072_eq_seventeen_mul_log_two : log 131072 = 17 * log 2 := by
  rw [show (131072 : ℝ) = 2 ^ 17 by norm_num, Real.log_pow]; norm_num

theorem log_sq_le {x : ℝ} (hx : 131072 ≤ x) : log x ^ 2 ≤ 0.00106 * x := by
  have hq : 1 ≤ x / 131072 := by rw [le_div_iff₀ (by norm_num)]; linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (x / 131072) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (x / 131072) := by
        first | exact Real.sqrt_le_sqrt hq | exact Real.sqrt_le_sqrt (by exact hq) | gcongr
  have hss : s ^ 2 = x / 131072 := by rw [hsdef]; exact Real.sq_sqrt (by linarith)
  have hxs : x = 131072 * s ^ 2 := by rw [hss]; ring
  have hlogs : log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogx : log x = log 131072 + 2 * log s := by
    rw [hxs, Real.log_mul (by norm_num) (pow_pos (by linarith) 2).ne', Real.log_pow]; norm_num
  have hl2 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2' : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hup : log x ≤ 17 * log 2 - 2 + 2 * s := by rw [hlogx, log_131072_eq_seventeen_mul_log_two]; linarith
  have hlow : 0 ≤ log x := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ 17 * log 2 - 2 := by linarith
  have h1 : 17 * log 2 - 2 + 2 * s ≤ (17 * log 2) * s := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hs1)]
  have h2 : 0 ≤ 17 * log 2 - 2 + 2 * s := by linarith
  have hsq2 : log 2 ^ 2 ≤ 0.6931471808 ^ 2 := pow_le_pow_left₀ (by linarith) hl2.le 2
  have h3 : (17 * log 2) ^ 2 ≤ 138.86 := by nlinarith [hsq2]
  calc log x ^ 2 ≤ (17 * log 2 - 2 + 2 * s) ^ 2 := pow_le_pow_left₀ hlow hup 2
    _ ≤ ((17 * log 2) * s) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = (17 * log 2) ^ 2 * s ^ 2 := by ring
    _ ≤ 138.86 * s ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg s)
    _ ≤ 0.00106 * (131072 * s ^ 2) := by nlinarith [sq_nonneg s]
    _ = 0.00106 * x := by rw [← hxs]

theorem pcLarge_of (hU : CHUpper) : PCLarge 131072 := by
  intro y hy
  have hy0 : 0 < y := by linarith
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hL : 17 * log 2 ≤ log y := by
    rw [← log_131072_eq_seventeen_mul_log_two]; exact Real.log_le_log (by norm_num) hy
  have hL' : 11.78 ≤ log y := by linarith
  have hLpos : 0 < log y := by linarith
  have hLne : log y ≠ 0 := hLpos.ne'
  have hL2 := log_sq_le hy
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (phi_intervalIntegrable (le_refl 2) (by norm_num : (2 : ℝ) ≤ 1024))
    (phi_intervalIntegrable (by norm_num) (by linarith : (1024 : ℝ) ≤ y))
  have hI : ∫ t in (2 : ℝ)..y, phi t ≤ 61 + gg y := by
    have h1 := int_small
    have h2 := int_tail hU (by linarith : (1024 : ℝ) ≤ y)
    have h3 := gg_1024_nonneg
    rw [← hsplit]
    linarith
  unfold gg at hI
  have hθ : Chebyshev.theta y ≤ 1.1056 * y + 0.7 * log y ^ 2 :=
    (Chebyshev.theta_le_psi y).trans (hU y (by linarith))
  have hdl : y / log y ^ 2 * log y = y / log y := by
    first | rw [pow_two, div_mul_eq_mul_div, mul_div_mul_right _ _ hLne] | (field_simp; ring) | field_simp
  have e : (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) * log y =
      61 * log y + 1.56 * (y / log y) + 0.7 * log y ^ 2 := by
    rw [← hdl]; ring
  have hv : y / log y ≤ 0.085 * y := by
    rw [div_le_iff₀ hLpos]
    nlinarith [mul_le_mul_of_nonneg_left hL' hy0.le]
  have hLle : log y ≤ 0.00009 * y := by
    nlinarith [mul_le_mul_of_nonneg_left hL' hLpos.le]
  have key : Chebyshev.theta y + (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) * log y < 1.26 * y := by
    nlinarith [e, hθ, hv, hLle, hL2, hy0]
  have hfin : Chebyshev.theta y / log y + (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) < 1.26 * y / log y := by
    rw [div_add' _ _ _ hLne]
    first | exact div_lt_div_of_pos_right key hLpos | exact (div_lt_div_iff_of_pos_right hLpos).mpr key | gcongr
  rw [card_pr, Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith)]
  show Chebyshev.theta y / log y + ∫ t in (2 : ℝ)..y, phi t < 1.26 * y / log y
  linarith

end PI.PC

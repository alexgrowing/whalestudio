import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem norm_root_number_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖eps0 χ‖ ≤ 1 := by
  unfold PI.EF.eps0
  split_ifs <;> simp

theorem norm_character_correction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖del1 χ‖ ≤ 1 := by
  unfold PI.EF.del1
  split_ifs <;> simp

theorem norm_near_sum_le {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      C * Real.log (N * (|s.im| + 2)) / d := by
  have hf := (hC N χ hχ s.im).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  calc ‖∑ ρ ∈ hf.toFinset, (mult χ ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ hf.toFinset, ‖(mult χ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ) / d := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (h ρ ((Set.Finite.mem_toFinset hf).mp hρ))
    _ = (∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ)) / d := by rw [Finset.sum_div]
    _ ≤ C * Real.log (N * (|s.im| + 2)) / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
        exact (hC N χ hχ s.im).2

private lemma norm_le_add_add_four_of_norm_sub_le {a b c e : ℂ} {x y : ℝ} (h1 : ‖a - b - c + e‖ ≤ x) (h2 : ‖b‖ ≤ y)
    (h3 : ‖c‖ ≤ 2) (h4 : ‖e‖ ≤ 2) : ‖a‖ ≤ x + y + 4 := by
  have e1 : a = (a - b - c + e) + b + c - e := by ring
  rw [e1]
  have k1 := norm_sub_le ((a - b - c + e) + b + c) e
  have k2 := norm_add_le ((a - b - c + e) + b) c
  have k3 := norm_add_le (a - b - c + e) b
  linarith

theorem norm_logDeriv_le {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3)
    (h0 : LFunction χ s ≠ 0) (hs0 : 1 / 2 ≤ ‖s‖) (hs1 : 1 / 2 ≤ ‖s - 1‖) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖logDeriv (LFunction χ) s‖ ≤
      Cl * Real.log (N * (|s.im| + 2)) + Cw * Real.log (N * (|s.im| + 2)) / d + 4 := by
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hs1
  have hmain := hL N χ hχ s h1 h2 h0 hs1'
  have hsum := norm_near_sum_le hW χ hχ s hd h
  have hE : ‖eps0 χ / s‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_root_number_le_one χ]
  have hD : ‖del1 χ / (s - 1)‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_character_correction_le χ]
  exact norm_le_add_add_four_of_norm_sub_le hmain hsum hE hD

theorem log_two_le_log {N : ℕ} [NeZero N] {x : ℝ} (hx : 2 ≤ x) : Real.log 2 ≤ Real.log (N * x) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact Real.log_le_log (by norm_num) (by nlinarith)

theorem logDerivLeft_of {Cw Cl : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hW : ZerosWindowWith Cw)
    (hL : LocalLemma Cl) (hZ : ZeroLocus) : LogDerivLeft (Cl + 2 * Cw + 6) := by
  unfold PI.EF.LogDerivLeft PI.EF.ZeroLocus at *
  intro N _ χ hχ t
  have hre : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = -1 / 2 := by norm_num
  have him : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im = t := by norm_num
  have hne1 : ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro a
    have := congrArg Complex.re a
    rw [hre] at this
    norm_num at this
  have hL0 : LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h0
    rcases hZ N χ hχ _ (by rw [hre]; norm_num) hne1 h0 with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · rw [hre] at a
      norm_num at a
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
  have hs0 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ :=
    le_trans (by rw [hre]; norm_num) (Complex.abs_re_le_norm _)
  have hs1 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - 1‖ :=
    le_trans (by rw [Complex.sub_re, hre, Complex.one_re]; norm_num) (Complex.abs_re_le_norm _)
  have hnear : ∀ ρ ∈ ZerosNear χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im,
      1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, -⟩ := hρ
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, hre, abs_of_neg (by linarith)]
    linarith
  have key := norm_logDeriv_le hW hL χ hχ _ hre.symm.le (by rw [hre]; norm_num) hL0 hs0 hs1
    (by norm_num : (0 : ℝ) < 1 / 2) hnear
  rw [him] at key
  have hlog2 : Real.log 2 ≤ Real.log (N * (|t| + 2)) := log_two_le_log (by linarith [abs_nonneg t])
  have hl2 := Real.log_two_gt_d9
  refine le_trans key ?_
  calc Cl * Real.log (N * (|t| + 2)) + Cw * Real.log (N * (|t| + 2)) / (1 / 2) + 4
        = Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) + 4 := by ring
    _ ≤ Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) +
          6 * Real.log (N * (|t| + 2)) := by linarith
    _ = (Cl + 2 * Cw + 6) * Real.log (N * (|t| + 2)) := by ring

theorem norm_logDeriv_horiz {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T' : ℝ} (hT' : 2 ≤ T')
    (hg : GoodHeight χ κ T') (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) (him : |s.im| = T') :
    ‖logDeriv (LFunction χ) s‖ ≤ (4 * Cl + 2 * Cw * κ + 16) * Real.log (N * T') ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓ2 : Real.log 2 ≤ Real.log (N * T') := log_two_le_log hT'
  have hl2 := Real.log_two_gt_d9
  have hlogT2 : Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * T') := by
    have e : 2 * Real.log (N * T') = Real.log ((N * T') ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [e]
    apply Real.log_le_log (by nlinarith)
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hT2 : T' + 2 ≤ T' ^ 2 := by nlinarith
    calc (N : ℝ) * (T' + 2) ≤ N * T' ^ 2 := mul_le_mul_of_nonneg_left hT2 (by linarith)
      _ ≤ N ^ 2 * T' ^ 2 := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = (N * T') ^ 2 := by ring
  have hlogpos2 : 0 ≤ Real.log (N * (T' + 2)) := Real.log_nonneg (by nlinarith)
  unfold PI.EF.GoodHeight at hg
  set ℓ := Real.log (N * T') with hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hd : 0 < 1 / (κ * ℓ) := one_div_pos.mpr (mul_pos hκ hℓpos)
  have hsim : 2 ≤ |s.im| := by rw [him]; exact hT'
  have hs0 : 1 / 2 ≤ ‖s‖ := by linarith [Complex.abs_im_le_norm s]
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hsim
  have hL0 : LFunction χ s ≠ 0 := by
    intro h0
    rcases hZ N χ hχ s (by linarith) hs1' h0 with ⟨a1, a2⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · have := hg s a1 a2 h0
      rw [him, sub_self, abs_zero] at this
      linarith
    · rw [a] at hsim
      norm_num at hsim
    · rw [a] at hsim
      norm_num at hsim
  have hnear : ∀ ρ ∈ ZerosNear χ s.im, 1 / (κ * ℓ) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, a4⟩ := hρ
    have hgρ := hg ρ a1 a2 a4
    have k1 : |(|ρ.im|) - T'| ≤ |s.im - ρ.im| := by
      rw [← him, abs_sub_comm]
      exact abs_abs_sub_abs_le_abs_sub s.im ρ.im
    have k2 : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    linarith
  have key := norm_logDeriv_le hW hL χ hχ s h1 h2 hL0 hs0 hs1 hd hnear
  rw [him, div_div_eq_mul_div, div_one] at key
  refine le_trans key ?_
  have h_a : Cl * Real.log (N * (T' + 2)) ≤ Cl * (2 * ℓ) := mul_le_mul_of_nonneg_left hlogT2 hCl
  have h_b : 2 * ℓ ≤ 4 * ℓ ^ 2 := by nlinarith
  have h_c : Cl * (2 * ℓ) ≤ Cl * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h_b hCl
  have h_d : Cw * Real.log (N * (T' + 2)) * (κ * ℓ) ≤ Cw * (2 * ℓ) * (κ * ℓ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT2 hCw) (mul_pos hκ hℓpos).le
  have h_e : 4 ≤ 16 * ℓ ^ 2 := by nlinarith
  nlinarith [h_a, h_c, h_d, h_e]

theorem logDerivHoriz_of {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) :
    LogDerivHoriz κ (4 * Cl + 2 * Cw * κ + 16) := by
  unfold PI.EF.LogDerivHoriz
  intro N _ χ hχ T' hT' hg σ h1 h2
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  constructor
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])

end PI.EF

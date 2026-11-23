import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumTruncConv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRiemannZetaSubPartialSumLeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroDetect

theorem pole_small : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    (1 + Real.log ((Q ^ 3 : ℕ) : ℝ)) * (((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20))
      ≤ 1 / 4 := by
  have h : Tendsto (fun Q : ℕ => (Q : ℝ) ^ ((1 : ℝ) / 40)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp (h.eventually_ge_atTop 1204)
  refine ⟨max Q₀ 1, fun Q hQ => ?_⟩
  have h1 := hQ₀ Q (le_of_max_le_left hQ)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast le_of_max_le_right hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlog := Real.log_le_rpow_div hQ0.le (show (0 : ℝ) < 1 / 100 by norm_num)
  have hone : (1 : ℝ) ≤ (Q : ℝ) ^ ((1 : ℝ) / 100) := Real.one_le_rpow hQ1 (by norm_num)
  have h2 : 1 + Real.log ((Q ^ 3 : ℕ) : ℝ) ≤ 301 * (Q : ℝ) ^ ((1 : ℝ) / 100) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have h3 : (Q : ℝ) ^ ((1 : ℝ) / 20) = (Q : ℝ) ^ ((1 : ℝ) / 100) *
      ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) * (Q : ℝ) ^ ((1 : ℝ) / 40) := by
    rw [← Real.rpow_natCast (Q : ℝ) 6, ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0,
      ← Real.rpow_add hQ0]
    norm_num
  have ha : 0 < ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) := by positivity
  rw [h3]
  set a := ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400)
  set b := (Q : ℝ) ^ ((1 : ℝ) / 100)
  set c := (Q : ℝ) ^ ((1 : ℝ) / 40)
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  calc _ ≤ 301 * b * (a / (b * a * c)) := by gcongr
    _ = 301 / c := by field_simp
    _ ≤ 1 / 4 := by rw [div_le_iff₀ hc]; linarith

theorem zeta_zero_detect : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → ∀ ρ : ℂ, 1 - 1 / 400 ≤ ρ.re → ρ.re < 1 → (Q : ℝ) ^ ((1 : ℝ) / 20) ≤ |ρ.im| → |ρ.im| ≤ Q → riemannZeta ρ = 0 → (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * (1 : ℂ) * (n : ℂ) ^ (-ρ)‖ := by
  obtain ⟨Q₀, hQ₀⟩ := pole_small
  refine ⟨max Q₀ 1024, fun Q hQ' ρ hre hre1 hlow him hL => ?_⟩
  have hpole := hQ₀ Q (le_of_max_le_left hQ')
  have hQ : 1024 ≤ Q := le_of_max_le_right hQ'
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-ρ) with hfdef
  have hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n := by
    intro m n _ _
    simp only [hfdef, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hQ1 : 1 ≤ Q := by omega
  have hQr : (1024 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hD1 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ1
  have hD2 : 2 ≤ Q ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) Q)
  have hX : Q ^ 6 = Q ^ 3 * Q ^ 3 := by ring
  have hDX : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right hQ1 (by norm_num)
  have hσ : 0 < ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at hre1; simp at hre1
  have hρ : ‖ρ‖ / ρ.re ≤ 4 * Q := by
    have h1 : ‖ρ‖ ≤ ρ.re + Q := by
      have := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_pos hσ] at this; linarith
    rw [div_le_iff₀ hσ]; nlinarith
  have hG : 0 < (Q : ℝ) ^ ((1 : ℝ) / 20) := by positivity
  have hden : (Q : ℝ) ^ ((1 : ℝ) / 20) ≤ ‖ρ - 1‖ := by
    have := Complex.abs_im_le_norm (ρ - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  set B : ℝ := ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20) with hB
  have hB0 : 0 ≤ B := by positivity
  have hconv := sum_trunc_conv (fun d => ((moebius d : ℤ) : ℂ)) f hf (Q ^ 3) (Q ^ 6)
  have hinit := sum_initial f (Q ^ 3) hD1
  have hbound : ‖∑ d ∈ Finset.Icc 1 (Q ^ 3), ((moebius d : ℤ) : ℂ) * f d *
      ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ 1 / 2 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun d : ℕ => 1 / (4 * (Q : ℝ) ^ 3) + (d : ℝ)⁻¹ * B) ?_).trans ?_
    · intro d hd
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
      have hN : 1 ≤ Q ^ 6 / d := Nat.div_pos (hdD.trans hDX) hd1
      have ht := GlobalTheory.T.norm_riemannZeta_sub_partial_sum_le ρ hσ hρ1 _ hN
      have hy : Q ^ 6 ≤ 2 * (d * (Q ^ 6 / d)) := by
        have h1 := Nat.div_add_mod (Q ^ 6) d
        have h2 := Nat.mod_lt (Q ^ 6) hd1
        have h3 : 2 * Q ^ 3 ≤ Q ^ 6 := by rw [hX]; exact Nat.mul_le_mul_right _ hD2
        omega
      have hy2 : d * (Q ^ 6 / d) ≤ Q ^ 6 := Nat.mul_div_le _ _
      generalize Q ^ 6 / d = M at *
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hM0 : (0 : ℝ) < M := by exact_mod_cast hN
      rw [hL, zero_sub, ← neg_add', norm_neg] at ht
      have hμ : ‖((moebius d : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
      have hfd : ‖f d‖ = (d : ℝ) ^ (-ρ.re) := by
        simp only [hfdef]
        rw [Complex.norm_natCast_cpow_of_pos hd1, Complex.neg_re]
      have hr := rpow_bound (y := (d : ℝ) * (M : ℝ)) (σ := ρ.re) hQr
        (by exact_mod_cast hy) (by linarith)
      rw [Real.mul_rpow (by positivity) (by positivity)] at hr
      have hp : ‖(M : ℂ) ^ (1 - ρ) / (ρ - 1)‖ ≤ (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by
        rw [norm_div, Complex.norm_natCast_cpow_of_pos hN]
        simp only [sub_re, one_re]
        gcongr
      have ht2 : ‖∑ m ∈ Finset.Icc 1 M, f m‖
          ≤ 4 * Q * (M : ℝ) ^ (-ρ.re) + (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by
        have h1 := norm_sub_le (∑ m ∈ Finset.Icc 1 M, f m + (M : ℂ) ^ (1 - ρ) / (ρ - 1))
          ((M : ℂ) ^ (1 - ρ) / (ρ - 1))
        rw [add_sub_cancel_right] at h1
        have h2 : ‖ρ‖ / ρ.re * (M : ℝ) ^ (-ρ.re) ≤ 4 * Q * (M : ℝ) ^ (-ρ.re) := by gcongr
        simp only [hfdef] at h1 ⊢
        linarith
      have hq : (d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (1 - ρ.re)
          ≤ (d : ℝ)⁻¹ * ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) := by
        have h1 : (d : ℝ) ^ (-ρ.re) = (d : ℝ)⁻¹ * (d : ℝ) ^ (1 - ρ.re) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hd0]; congr 1; ring
        rw [h1, mul_assoc, ← Real.mul_rpow hd0.le hM0.le]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h2 : (d : ℝ) * M ≤ (Q : ℝ) ^ 6 := by exact_mod_cast hy2
        refine (Real.rpow_le_rpow (by positivity) h2 (by linarith)).trans ?_
        exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by linarith)) (by linarith)
      have h3 : 4 * (Q : ℝ) * (16 * (Q : ℝ) ^ 5)⁻¹ ≤ 1 / (4 * (Q : ℝ) ^ 3) := by
        have : 4 * (Q : ℝ) * (16 * (Q : ℝ) ^ 5)⁻¹ = 1 / (4 * (Q : ℝ) ^ 4) := by
          field_simp; norm_num
        rw [this]
        gcongr
        · linarith
        · norm_num
      rw [norm_mul, norm_mul, hfd]
      calc _ ≤ 1 * (d : ℝ) ^ (-ρ.re) *
              (4 * Q * (M : ℝ) ^ (-ρ.re) + (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20)) := by
            gcongr
        _ = 4 * Q * ((d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (-ρ.re)) +
              (d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by ring
        _ ≤ 4 * Q * (16 * (Q : ℝ) ^ 5)⁻¹ +
              (d : ℝ)⁻¹ * ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by gcongr
        _ ≤ _ := by rw [hB, mul_div_assoc]; linarith
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const]
      have hh : ∑ d ∈ Finset.Icc 1 (Q ^ 3), (d : ℝ)⁻¹ ≤ 1 + Real.log ((Q ^ 3 : ℕ) : ℝ) := by
        have := harmonic_le_one_add_log (Q ^ 3)
        rw [harmonic_eq_sum_Icc] at this
        push_cast at this ⊢
        exact this
      have h1 : (Finset.Icc 1 (Q ^ 3)).card • (1 / (4 * (Q : ℝ) ^ 3)) = 1 / 4 := by
        simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_pow]
        field_simp
      have h2 := mul_le_mul_of_nonneg_right hh hB0
      linarith
  rw [← hconv, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hDX] at hbound
  simp only [Int.cast_sum] at hinit
  rw [hinit, hf1] at hbound
  simp only [Int.cast_sum, mul_one]
  have := norm_sub_le (1 + ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
    (∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), ((moebius d : ℤ) : ℂ)) * f n)
    (∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
    (∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), ((moebius d : ℤ) : ℂ)) * f n)
  rw [add_sub_cancel_right, norm_one] at this
  simp only [hfdef] at this hbound
  linarith

end GlobalTheory.ZeroDetect

import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionEqTsumOfOneLt
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZeroDetect

open Complex DirichletCharacter ArithmeticFunction MeasureTheory in

theorem _root_.GlobalTheory.ZeroDetect.sum_trunc_conv (a f : ℕ → ℂ)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (D X : ℕ) :
    ∑ n ∈ Finset.Ioc 0 X, (∑ d ∈ n.divisors.filter (fun d => d ≤ D), a d) * f n
      = ∑ d ∈ Finset.Icc 1 D, a d * f d * ∑ m ∈ Finset.Icc 1 (X / d), f m := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 D)
    (s' := fun d => (Finset.Ioc 0 X).filter (fun n => d ∣ n))]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 0 < d := (Finset.mem_Icc.1 hd).1
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun n _ => n / d) (fun m _ => d * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h0, hX⟩, k, rfl⟩ := hn
      have hk : 0 < k := Nat.pos_of_mul_pos_left h0
      rw [Nat.mul_div_cancel_left k hd1, Finset.mem_Icc]
      exact ⟨hk, (Nat.le_div_iff_mul_le hd1).2 (by rw [mul_comm]; exact hX)⟩
    · intro m hm
      rw [Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd1).1 hm.2
      rw [mul_comm]; exact this
    · intro n hn
      simp only [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      exact Nat.mul_div_cancel_left m hd1
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h0, _⟩, k, rfl⟩ := hn
      have hk : 0 < k := Nat.pos_of_mul_pos_left h0
      rw [Nat.mul_div_cancel_left k hd1, hf d k hd1 hk]
      ring
  · intro n d
    simp only [Finset.mem_Ioc, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hX⟩, ⟨hdn, -⟩, hdD⟩
      exact ⟨⟨⟨h0, hX⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn h0, hdD⟩
    · rintro ⟨⟨⟨h0, hX⟩, hdn⟩, -, hdD⟩
      exact ⟨⟨h0, hX⟩, ⟨hdn, h0.ne'⟩, hdD⟩

open Complex DirichletCharacter ArithmeticFunction MeasureTheory in

theorem _root_.GlobalTheory.ZeroDetect.sum_initial (f : ℕ → ℂ) (D : ℕ) (hD : 1 ≤ D) :
    ∑ n ∈ Finset.Ioc 0 D,
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ D), (moebius d : ℤ) : ℤ) : ℂ) * f n = f 1 := by
  have hsum : ∀ n, ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    intro n
    rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
  rw [Finset.sum_eq_single 1]
  · simp [Finset.filter_singleton, hD]
  · intro n hn hn1
    have hfil : n.divisors.filter (fun d => d ≤ D) = n.divisors := by
      apply Finset.filter_true_of_mem
      intro d hd
      exact (Nat.divisor_le hd).trans (Finset.mem_Ioc.1 hn).2
    rw [hfil, hsum, if_neg hn1]
    simp
  · intro h
    exact absurd (Finset.mem_Ioc.2 ⟨zero_lt_one, hD⟩) h

open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.ZeroDetect.rpow_bound {Q y σ : ℝ} (hQ : 1024 ≤ Q) (hy : Q ^ 6 ≤ 2 * y)
    (hσ : 11 / 12 ≤ σ) :
    y ^ (-σ) ≤ (16 * Q ^ 5)⁻¹ := by
  have hQ0 : 0 < Q := by linarith
  have hQ6 : (2:ℝ) ^ 60 ≤ Q ^ 6 := by
    calc (2:ℝ) ^ 60 = 1024 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := pow_le_pow_left₀ (by norm_num) hQ 6
  have hy1 : 1 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  have h5 : 0 < 16 * Q ^ 5 := by positivity
  have key : 16 * Q ^ 5 ≤ y ^ ((11:ℝ) / 12) := by
    have hpow : (y ^ ((11:ℝ) / 12)) ^ 12 = y ^ 11 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      norm_num
    have h12 : (16 * Q ^ 5) ^ 12 ≤ (y ^ ((11:ℝ) / 12)) ^ 12 := by
      rw [hpow]
      have hyQ : Q ^ 6 / 2 ≤ y := by linarith
      calc (16 * Q ^ 5) ^ 12 = 2 ^ 48 * Q ^ 60 := by ring
        _ ≤ (Q ^ 6) ^ 11 / 2 ^ 11 := by
          have : (Q ^ 6) ^ 11 = Q ^ 6 * Q ^ 60 := by ring
          rw [this]
          have hQ60 : 0 < Q ^ 60 := by positivity
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        _ = (Q ^ 6 / 2) ^ 11 := by ring
        _ ≤ y ^ 11 := pow_le_pow_left₀ (by positivity) hyQ 11
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h12
  rw [Real.rpow_neg hy0.le]
  apply inv_anti₀ h5
  calc 16 * Q ^ 5 ≤ y ^ ((11:ℝ) / 12) := key
    _ ≤ y ^ σ := Real.rpow_le_rpow_of_exponent_le hy1 hσ

open Complex DirichletCharacter ArithmeticFunction MeasureTheory in

theorem _root_.GlobalTheory.ZeroDetect.zero_detect : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → q ≤ Q → ∀ ρ : ℂ,
    1 - 1 / 400 ≤ ρ.re → |ρ.im| ≤ Q → LFunction χ ρ = 0 →
    (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ)‖ := by
  refine ⟨1024, fun Q hQ q _ χ hχ hqQ ρ hre him hL => ?_⟩
  have hσ : (11 / 12 : ℝ) ≤ ρ.re := by norm_num at hre; linarith
  have hσ0 : 0 < ρ.re := by linarith
  have hQR : (1024 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hD : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hQ3 : 2 ≤ Q ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) Q)
  have hD2 : 2 * Q ^ 3 ≤ Q ^ 6 := by
    calc 2 * Q ^ 3 ≤ Q ^ 3 * Q ^ 3 := Nat.mul_le_mul_right _ hQ3
      _ = Q ^ 6 := by ring
  set f : ℕ → ℂ := fun n => χ (n : ZMod q) * (n : ℂ) ^ (-ρ) with hfdef
  set a : ℕ → ℂ := fun d => ((moebius d : ℤ) : ℂ) with hadef
  have hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n := by
    intro m n _ _
    simp only [f, Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hS : ∀ Y : ℕ, ∑ n ∈ Finset.Ioc 0 Y,
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      ∑ n ∈ Finset.Ioc 0 Y, (∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), a d) * f n := by
    intro Y
    apply Finset.sum_congr rfl
    intro n _
    simp only [a, f]
    push_cast
    ring
  have hsplit := Finset.sum_Ioc_consecutive (fun n =>
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) (Nat.zero_le (Q ^ 3)) hD
  have hinit : ∑ n ∈ Finset.Ioc 0 (Q ^ 3),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) = 1 := by
    calc _ = ∑ n ∈ Finset.Ioc 0 (Q ^ 3),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * f n :=
          Finset.sum_congr rfl (fun n _ => mul_assoc _ _ _)
      _ = f 1 := _root_.GlobalTheory.ZeroDetect.sum_initial f (Q ^ 3) (by omega)
      _ = 1 := by simp [f]
  have hmain : ∑ n ∈ Finset.Ioc 0 (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      ∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m := by
    rw [hS]
    exact _root_.GlobalTheory.ZeroDetect.sum_trunc_conv a f hf _ _
  have hnorm : ‖ρ‖ / ρ.re ≤ 1 + 2 * Q := by
    have h1 := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_pos hσ0] at h1
    rw [div_le_iff₀ hσ0]
    nlinarith
  set C : ℝ := 2 * (q : ℝ) * (1 + ‖ρ‖ / ρ.re) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hCle : C ≤ 8 * (Q : ℝ) ^ 2 := by
    have h4 : 1 + ‖ρ‖ / ρ.re ≤ 4 * Q := by linarith
    calc C ≤ 2 * (Q : ℝ) * (4 * Q) := by
          apply mul_le_mul (by linarith) h4 (by positivity) (by positivity)
      _ = 8 * (Q : ℝ) ^ 2 := by ring
  have hterm : ∀ d ∈ Finset.Icc 1 (Q ^ 3),
      ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ C * (16 * (Q : ℝ) ^ 5)⁻¹ := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.1 hd
    have hN : 1 ≤ Q ^ 6 / d := (Nat.le_div_iff_mul_le hd1).2 (by omega)
    have hP : ‖∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ C * ((Q ^ 6 / d : ℕ) : ℝ) ^ (-ρ.re) := by
      have := _root_.GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le q χ hχ ρ hσ0 (Q ^ 6 / d) hN
      rw [hL, zero_sub, norm_neg] at this
      exact this
    have ha : ‖a d‖ ≤ 1 := by
      simp only [a]
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one
    have hfd : ‖f d‖ ≤ (d : ℝ) ^ (-ρ.re) := by
      simp only [f]
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hd1, Complex.neg_re]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
    have hyN : Q ^ 6 ≤ 2 * (d * (Q ^ 6 / d)) := by
      have h1 := Nat.div_add_mod (Q ^ 6) d
      have h2 := Nat.mod_lt (Q ^ 6) hd1
      omega
    have hy : (Q : ℝ) ^ 6 ≤ 2 * ((d : ℝ) * ((Q ^ 6 / d : ℕ) : ℝ)) := by exact_mod_cast hyN
    have hrp := _root_.GlobalTheory.ZeroDetect.rpow_bound hQR hy hσ
    calc ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖
        = ‖a d‖ * ‖f d‖ * ‖∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * (d : ℝ) ^ (-ρ.re) * (C * ((Q ^ 6 / d : ℕ) : ℝ) ^ (-ρ.re)) := by gcongr
      _ = C * ((d : ℝ) * ((Q ^ 6 / d : ℕ) : ℝ)) ^ (-ρ.re) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ C * (16 * (Q : ℝ) ^ 5)⁻¹ := by gcongr
  have hsum : ‖∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖
      ≤ 1 / 2 := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 (Q ^ 3), ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 (Q ^ 3), C * (16 * (Q : ℝ) ^ 5)⁻¹ := Finset.sum_le_sum hterm
      _ = (Q : ℝ) ^ 3 * (C * (16 * (Q : ℝ) ^ 5)⁻¹) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          push_cast
          simp
      _ = C / (16 * (Q : ℝ) ^ 2) := by field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
  have hT : ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      (∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m) - 1 := by
    rw [← hmain, ← hsplit, hinit]
    ring
  rw [hT, norm_sub_rev]
  have h1 := norm_sub_norm_le (1 : ℂ)
    (∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m)
  rw [norm_one] at h1
  linarith

end GlobalTheory.ZeroDetect

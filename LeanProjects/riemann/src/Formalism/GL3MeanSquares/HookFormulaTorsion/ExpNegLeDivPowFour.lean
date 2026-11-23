import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

open Finset Filter Topology

namespace Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion

lemma tele (g H : ℕ → ℝ) (M : ℕ) (h : ∀ n, M ≤ n → g (n + 1) ≤ H n - H (n + 1)) :
    ∀ N, M ≤ N → ∑ n ∈ Ioc M N, g n ≤ H M - H N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN]
    have := h N hN
    linarith

lemma abel (a : ℕ → ℂ) (M : ℕ) : ∀ N, M ≤ N →
    ∑ n ∈ Icc 1 N, a n / (n : ℂ) - ∑ n ∈ Icc 1 M, a n / (n : ℂ) =
      (∑ k ∈ Icc 1 N, a k) / ((N : ℂ) + 1) - (∑ k ∈ Icc 1 M, a k) / ((M : ℂ) + 1) +
        ∑ n ∈ Ioc M N, (∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h1 : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have h2 : ((N : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
    have e : ∑ n ∈ Icc 1 N, a n / (n : ℂ) = ∑ n ∈ Icc 1 M, a n / (n : ℂ) + ((∑ k ∈ Icc 1 N, a k) / ((N : ℂ) + 1) - (∑ k ∈ Icc 1 M, a k) / ((M : ℂ) + 1) +
        ∑ n ∈ Ioc M N, (∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))) := by
      rw [← ih]; ring
    rw [e]
    push_cast
    field_simp
    ring

lemma tail_abs (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (M : ℕ) (hM : 1 ≤ M) (β : ℕ → ℝ) (B₀ B₁ : ℝ)
    (hβ : ∀ n, M ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤ n * β n)
    (h0 : ∀ n, M ≤ n → β n ≤ B₀)
    (h1 : ∀ N, M ≤ N → ∑ n ∈ Ioc M N, β n / n ≤ B₁) :
    ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤ 2 * B₀ + B₁ := by
  have hpos : ∀ n, M ≤ n → 0 ≤ β n := by
    intro n hn
    have h := (norm_nonneg _).trans (hβ n hn)
    have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    exact nonneg_of_mul_nonneg_right h hn'
  have hb : ∀ n, M ≤ n → ‖(∑ k ∈ Icc 1 n, a k) / ((n : ℂ) + 1)‖ ≤ β n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have e : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_div, e, div_le_iff₀ (by positivity)]
    have := hβ n hn
    have := hpos n hn
    nlinarith
  have hc : ∀ n, M ≤ n → ‖(∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))‖ ≤ β n / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have e : (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn'.ne'
      have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      push_cast
      field_simp
      ring
    rw [norm_mul, e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h3 := hβ n hn
    have h4 := hpos n hn
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hn']
    nlinarith [mul_nonneg hn'.le h4, mul_nonneg (mul_nonneg hn'.le hn'.le) h4]
  refine le_of_tendsto ((hS.sub_const _).norm) ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  rw [abel a M N hN]
  calc _ ≤ ‖(∑ k ∈ Icc 1 N, a k) / ((N : ℂ) + 1)‖ + ‖(∑ k ∈ Icc 1 M, a k) / ((M : ℂ) + 1)‖ +
        ‖∑ n ∈ Ioc M N, (∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ B₀ + B₀ + ∑ n ∈ Ioc M N, β n / n := by
        refine add_le_add (add_le_add ((hb N hN).trans (h0 N hN)) ((hb M le_rfl).trans (h0 M le_rfl))) ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        exact hc n (Finset.mem_Ioc.mp hn).1.le
    _ ≤ 2 * B₀ + B₁ := by have := h1 N hN; linarith

lemma log_step (n : ℕ) (hn : 1 ≤ n) :
    1 / (((n + 1 : ℕ) : ℝ)) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn' hn1)
  rw [Real.log_div hn'.ne' hn1.ne'] at h
  have e : (n : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = - (1 / ((n + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [e] at h
  linarith

lemma sum_pow (δ : ℝ) (hδ : 0 < δ) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, (n : ℝ) ^ (-δ) / n ≤ (M : ℝ) ^ (-δ) / δ := by
  have h := tele (fun n : ℕ => (n : ℝ) ^ (-δ) / n) (fun n : ℕ => (n : ℝ) ^ (-δ) / δ) M ?_ N hN
  · have : 0 ≤ (N : ℝ) ^ (-δ) / δ := by positivity
    linarith
  · intro n hn
    have hn1 : 1 ≤ n := hM.trans hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn2 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hs := log_step n hn1
    rw [Real.rpow_def_of_pos hn', Real.rpow_def_of_pos hn2]
    set s := Real.log (n : ℝ)
    set t := Real.log ((n + 1 : ℕ) : ℝ)
    have e1 : Real.exp (s * -δ) = Real.exp (t * -δ) * Real.exp (δ * (t - s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : δ * (t - s) + 1 ≤ Real.exp (δ * (t - s)) := Real.add_one_le_exp _
    have e3 : 0 < Real.exp (t * -δ) := Real.exp_pos _
    rw [e1, ← sub_div, le_div_iff₀ hδ, div_eq_mul_one_div]
    have e4 : Real.exp (t * -δ) * (1 / ((n + 1 : ℕ) : ℝ)) ≤ Real.exp (t * -δ) * (t - s) :=
      mul_le_mul_of_nonneg_left hs e3.le
    have e5 : Real.exp (t * -δ) * (δ * (t - s) + 1) ≤ Real.exp (t * -δ) * Real.exp (δ * (t - s)) :=
      mul_le_mul_of_nonneg_left e2 e3.le
    nlinarith

lemma sum_log (M : ℕ) (hM : 2 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, 1 / Real.log (n : ℝ) ^ 2 / n ≤ 1 / Real.log (M : ℝ) := by
  have h := tele (fun n : ℕ => 1 / Real.log (n : ℝ) ^ 2 / n) (fun n : ℕ => 1 / Real.log (n : ℝ)) M ?_ N hN
  · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by omega) (hM.trans hN))
    have : 0 ≤ 1 / Real.log (N : ℝ) := by
      have := Real.log_nonneg hN'
      positivity
    linarith
  · intro n hn
    have hn1 : 2 ≤ n := hM.trans hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn1
    have hs := log_step n (by omega)
    have hs0 : 0 < Real.log (n : ℝ) := Real.log_pos hn'
    set s := Real.log (n : ℝ)
    set t := Real.log ((n + 1 : ℕ) : ℝ)
    have hn2 : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    have hst : s < t := by linarith
    have ht0 : 0 < t := hs0.trans hst
    have e : 1 / s - 1 / t = (t - s) / (s * t) := by field_simp
    rw [e, div_div, one_div]
    rw [one_div] at hs
    have h1 : (t ^ 2 * ((n + 1 : ℕ) : ℝ))⁻¹ = (t ^ 2)⁻¹ * (((n + 1 : ℕ) : ℝ))⁻¹ := by
      rw [mul_inv]
    rw [h1]
    calc (t ^ 2)⁻¹ * (((n + 1 : ℕ) : ℝ))⁻¹ ≤ (t ^ 2)⁻¹ * (t - s) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (t - s) / (t * t) := by rw [div_eq_mul_inv, sq]; ring
      _ ≤ (t - s) / (s * t) := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right hst.le ht0.le

lemma rpow_neg_k (y : ℝ) (hy : 0 < y) (k : ℕ) (e : ℝ) (he : e = -((k : ℝ) / 1600)) :
    y ^ e = ((y ^ ((1 : ℝ) / 1600)) ^ k)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le, he]
  congr 1
  ring

lemma w_bound (M n : ℕ) (hM : 1 ≤ M) (hn : M ≤ n) (Q : ℝ) (hQ : 1 ≤ Q) :
    (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 ≤
      2 * Real.log (M * Q) ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) +
        2 * 1600 ^ 2 * (M : ℝ) ^ (-((1 : ℝ) / 800)) * (n : ℝ) ^ (-((1 : ℝ) / 800)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
  have hQ' : 0 < Q := by linarith
  have hr0 : 0 ≤ Real.log ((n : ℝ) / M) := Real.log_nonneg (by rw [le_div_iff₀ hM']; linarith)
  have hr1 : Real.log ((n : ℝ) / M) ≤ ((n : ℝ) / M) ^ ((1 : ℝ) / 1600) / (1 / 1600) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have hl0 : 0 ≤ Real.log (M * Q) := Real.log_nonneg (by nlinarith)
  have e : Real.log (n * Q) = Real.log (M * Q) + Real.log ((n : ℝ) / M) := by
    rw [Real.log_mul hn'.ne' hQ'.ne', Real.log_mul hM'.ne' hQ'.ne', Real.log_div hn'.ne' hM'.ne']
    ring
  rw [Real.div_rpow hn'.le hM'.le] at hr1
  rw [e, rpow_neg_k n hn' 4 (-((1 : ℝ) / 400)) (by norm_num), rpow_neg_k n hn' 2 (-((1 : ℝ) / 800)) (by norm_num),
    rpow_neg_k M hM' 2 (-((1 : ℝ) / 800)) (by norm_num)]
  set p := (n : ℝ) ^ ((1 : ℝ) / 1600)
  set q := (M : ℝ) ^ ((1 : ℝ) / 1600)
  set l := Real.log (M * Q)
  set r := Real.log ((n : ℝ) / M)
  have hp : 0 < p := Real.rpow_pos_of_pos hn' _
  have hq : 0 < q := Real.rpow_pos_of_pos hM' _
  have hr2 : r ≤ 1600 * (p / q) := by
    have : p / q / (1 / 1600) = 1600 * (p / q) := by ring
    linarith
  have hr3 : r ^ 2 ≤ 1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹) := by
    have : r ^ 2 ≤ (1600 * (p / q)) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
    have e2 : (1600 * (p / q)) ^ 2 = 1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹) := by
      field_simp
    linarith
  have h4 : (l + r) ^ 2 ≤ 2 * l ^ 2 + 2 * (1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹)) := by
    nlinarith [sq_nonneg (l - r)]
  have h5 : (p ^ 4)⁻¹ * (l + r) ^ 2 ≤ (p ^ 4)⁻¹ * (2 * l ^ 2 + 2 * (1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹))) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

lemma one_le_log_nat (n : ℕ) (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_three
  linarith

lemma tail_main (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (M : ℕ) (hM : 3 ≤ M) (Q : ℝ) (hQ : 1 ≤ Q) (P E : ℝ) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hβ : ∀ n : ℕ, M ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (P * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2))) :
    ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤
      P * ((804 * Real.log (M * Q) ^ 2 + 5000000000) * (M : ℝ) ^ (-((1 : ℝ) / 400))) + 3 * E := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  set l := Real.log (M * Q) with hl
  set m4 := (M : ℝ) ^ (-((1 : ℝ) / 400)) with hm4
  set m8 := (M : ℝ) ^ (-((1 : ℝ) / 800)) with hm8
  have hm4p : 0 < m4 := Real.rpow_pos_of_pos hM' _
  have hm8p : 0 < m8 := Real.rpow_pos_of_pos hM' _
  have hm88 : m8 * m8 = m4 := by
    rw [hm8, hm4, ← Real.rpow_add hM']; congr 1; norm_num
  have hw : ∀ n : ℕ, M ≤ n → (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 ≤
      2 * l ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) + 2 * 1600 ^ 2 * m8 * (n : ℝ) ^ (-((1 : ℝ) / 800)) :=
    fun n hn => w_bound M n (by omega) hn Q hQ
  have h0 : ∀ n : ℕ, M ≤ n →
      P * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2) ≤
        P * ((2 * l ^ 2 + 2 * 1600 ^ 2) * m4) + E := by
    intro n hn
    have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
    have a4 : (n : ℝ) ^ (-((1 : ℝ) / 400)) ≤ m4 :=
      Real.rpow_le_rpow_of_nonpos hM' hMn (by norm_num)
    have a8 : (n : ℝ) ^ (-((1 : ℝ) / 800)) ≤ m8 :=
      Real.rpow_le_rpow_of_nonpos hM' hMn (by norm_num)
    have hlog := one_le_log_nat n (hM.trans hn)
    have b1 : 1 / Real.log (n : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ hlog
    have b2 : 2 * l ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 2 * l ^ 2 * m4 :=
      mul_le_mul_of_nonneg_left a4 (by positivity)
    have b3 : 2 * 1600 ^ 2 * m8 * (n : ℝ) ^ (-((1 : ℝ) / 800)) ≤ 2 * 1600 ^ 2 * m8 * m8 :=
      mul_le_mul_of_nonneg_left a8 (by positivity)
    have b4 : (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 ≤ (2 * l ^ 2 + 2 * 1600 ^ 2) * m4 := by
      have := hw n hn
      have e : 2 * 1600 ^ 2 * m8 * m8 = 2 * 1600 ^ 2 * m4 := by rw [mul_assoc, hm88]
      linarith
    have b5 := mul_le_mul_of_nonneg_left b4 hP
    have b6 := mul_le_mul_of_nonneg_left b1 hE
    linarith
  have h1 : ∀ N : ℕ, M ≤ N → ∑ n ∈ Ioc M N,
      (P * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2)) / n ≤
        P * ((800 * l ^ 2 + 1600 ^ 3) * m4) + E := by
    intro N hN
    have s4 := sum_pow ((1 : ℝ) / 400) (by norm_num) M (by omega) N hN
    have s8 := sum_pow ((1 : ℝ) / 800) (by norm_num) M (by omega) N hN
    have sl := sum_log M (by omega) N hN
    have hlogM := one_le_log_nat M hM
    have sl' : 1 / Real.log (M : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hlogM
    calc _ ≤ ∑ n ∈ Ioc M N, (P * (2 * l ^ 2) * ((n : ℝ) ^ (-((1 : ℝ) / 400)) / n) +
          P * (2 * 1600 ^ 2 * m8) * ((n : ℝ) ^ (-((1 : ℝ) / 800)) / n) +
          E * (1 / Real.log (n : ℝ) ^ 2 / n)) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn1 : M ≤ n := (Finset.mem_Ioc.mp hn).1.le
          have hn' : (0 : ℝ) < n := lt_of_lt_of_le hM' (by exact_mod_cast hn1)
          have c1 := mul_le_mul_of_nonneg_left (hw n hn1) hP
          rw [div_le_iff₀ hn']
          have e : (P * (2 * l ^ 2) * ((n : ℝ) ^ (-((1 : ℝ) / 400)) / n) +
            P * (2 * 1600 ^ 2 * m8) * ((n : ℝ) ^ (-((1 : ℝ) / 800)) / n) +
            E * (1 / Real.log (n : ℝ) ^ 2 / n)) * n =
            P * (2 * l ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) + 2 * 1600 ^ 2 * m8 * (n : ℝ) ^ (-((1 : ℝ) / 800)))
             + E * (1 / Real.log (n : ℝ) ^ 2) := by
            field_simp
          rw [e]
          linarith
      _ = P * (2 * l ^ 2) * ∑ n ∈ Ioc M N, ((n : ℝ) ^ (-((1 : ℝ) / 400)) / n) +
          P * (2 * 1600 ^ 2 * m8) * ∑ n ∈ Ioc M N, ((n : ℝ) ^ (-((1 : ℝ) / 800)) / n) +
          E * ∑ n ∈ Ioc M N, (1 / Real.log (n : ℝ) ^ 2 / n) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ ≤ P * (2 * l ^ 2) * (m4 / (1 / 400)) + P * (2 * 1600 ^ 2 * m8) * (m8 / (1 / 800)) + E * 1 := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul_of_nonneg_left s4 (by positivity)
          · exact mul_le_mul_of_nonneg_left s8 (by positivity)
          · exact mul_le_mul_of_nonneg_left (sl.trans sl') hE
      _ = P * ((800 * l ^ 2 + 1600 ^ 3) * m4) + E := by
          rw [← hm88]; ring
  have key := tail_abs a S hS M (by omega) _ _ _ hβ h0 h1
  have : 0 ≤ P * m4 := by positivity
  nlinarith

lemma exp_neg_le_div_pow_four (y : ℝ) (hy : 0 < y) : Real.exp (-y) ≤ 24 / y ^ 4 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 4
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  rw [div_le_iff₀ (by norm_num)] at h
  linarith

lemma pointwise (a : ℕ → ℂ) (Q C₁ c₁ : ℝ) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hQ : 0 < Q)
    (hL : 1 ≤ Real.log Q)
    (H1 : ∀ u : ℝ, 2 ≤ u → ‖psum a u‖ ≤
          C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2))
    (H2 : ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
          ‖psum a u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)))
    (n : ℕ) (hn : 3 ≤ n) :
    ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (C₁ * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) +
        (C₁ * (4 * Real.log Q ^ 8 * Real.exp (-Real.log Q) +
          384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * Real.log Q)))) * (1 / Real.log (n : ℝ) ^ 2)) := by
  have hps : psum a (n : ℝ) = ∑ k ∈ Icc 1 n, a k := by simp [psum]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith
  have hlog := one_le_log_nat n hn
  set L := Real.log Q with hLdef
  set t := Real.log (n : ℝ) with ht
  have hw : 0 ≤ (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 := by positivity
  have hE1 : 0 ≤ 4 * L ^ 8 * Real.exp (-L) := by positivity
  have hE2 : 0 ≤ 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L)) := by positivity
  have ht2 : 0 < t ^ 2 := by positivity
  rw [← hps]
  by_cases h : Real.exp (L ^ 2) ≤ n
  · refine (H2 n h).trans ?_
    rw [← ht]
    set s := Real.sqrt t with hs
    have hss : s ^ 2 = t := Real.sq_sqrt (by linarith)
    have hLt : L ^ 2 ≤ t := by rw [ht, Real.le_log_iff_exp_le hn']; exact h
    have hLs : L ≤ s := by rw [hs, Real.le_sqrt' (by linarith)]; exact hLt
    have hs0 : 0 < s := by linarith
    have e1 : Real.exp (-c₁ * s) = Real.exp (-(c₁ / 2 * s)) * Real.exp (-(c₁ / 2 * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(c₁ / 2 * s)) ≤ Real.exp (-(c₁ / 2 * L)) := by
      apply Real.exp_le_exp.mpr
      have : c₁ / 2 * L ≤ c₁ / 2 * s := mul_le_mul_of_nonneg_left hLs (by positivity)
      linarith
    have e3 : Real.exp (-(c₁ / 2 * s)) ≤ 24 / (c₁ / 2 * s) ^ 4 := exp_neg_le_div_pow_four _ (by positivity)
    have e4 : 24 / (c₁ / 2 * s) ^ 4 = 384 / c₁ ^ 4 * (1 / t ^ 2) := by
      rw [← hss]; field_simp; ring
    have e5 : Real.exp (-c₁ * s) ≤ 384 / c₁ ^ 4 * (1 / t ^ 2) * Real.exp (-(c₁ / 2 * L)) := by
      rw [e1, ← e4]
      exact mul_le_mul e3 e2 (Real.exp_pos _).le (by positivity)
    have e6 : 0 ≤ 4 * L ^ 8 * Real.exp (-L) * (1 / t ^ 2) := by positivity
    have e7 : Real.exp (-c₁ * s) ≤ ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) +
        (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L))) * (1 / t ^ 2) := by
      nlinarith
    have e8 := mul_le_mul_of_nonneg_left e7 (mul_nonneg hC₁.le hn'.le)
    refine e8.trans (le_of_eq ?_)
    ring
  · rw [not_le] at h
    have htL : t < L ^ 2 := by rw [ht, Real.log_lt_iff_lt_exp hn']; exact h
    refine (H1 n (by linarith)).trans ?_
    have e1 : (n : ℝ) ^ (1 - (1 : ℝ) / 400) = n * (n : ℝ) ^ (-((1 : ℝ) / 400)) := by
      rw [sub_eq_add_neg, Real.rpow_add hn', Real.rpow_one]
    have e2 : Real.log (n * Q) = t + L := Real.log_mul hn'.ne' hQ.ne'
    have e3 : (1 : ℝ) / Q = Real.exp (-L) := by
      rw [Real.exp_neg, hLdef, Real.exp_log hQ, one_div]
    have hLL : L ≤ L ^ 2 := by nlinarith
    have e4 : (t + L) ^ 2 ≤ 4 * L ^ 4 := by
      have h1 : t + L ≤ 2 * L ^ 2 := by linarith
      have h2 : (t + L) ^ 2 ≤ (2 * L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      have : (2 * L ^ 2) ^ 2 = 4 * L ^ 4 := by ring
      linarith
    have e5 : 1 ≤ L ^ 4 * (1 / t ^ 2) := by
      rw [mul_one_div, le_div_iff₀ ht2, one_mul]
      have h2 : t ^ 2 ≤ (L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) htL.le 2
      have : (L ^ 2) ^ 2 = L ^ 4 := by ring
      linarith
    have e6 : (t + L) ^ 2 ≤ 4 * L ^ 8 * (1 / t ^ 2) := by
      have h1 : 4 * L ^ 4 * 1 ≤ 4 * L ^ 4 * (L ^ 4 * (1 / t ^ 2)) :=
        mul_le_mul_of_nonneg_left e5 (by positivity)
      have : 4 * L ^ 4 * (L ^ 4 * (1 / t ^ 2)) = 4 * L ^ 8 * (1 / t ^ 2) := by ring
      linarith
    have e7 : Real.exp (-L) * (t + L) ^ 2 ≤ Real.exp (-L) * (4 * L ^ 8 * (1 / t ^ 2)) :=
      mul_le_mul_of_nonneg_left e6 (Real.exp_pos _).le
    have e8 : 0 ≤ 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L)) * (1 / t ^ 2) := by positivity
    rw [e1, e2, div_eq_mul_one_div (n : ℝ) Q, e3]
    have e9 : (n : ℝ) ^ (-((1 : ℝ) / 400)) * (t + L) ^ 2 + Real.exp (-L) * (t + L) ^ 2 ≤
        (n : ℝ) ^ (-((1 : ℝ) / 400)) * (t + L) ^ 2 +
        (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L))) * (1 / t ^ 2) := by
      nlinarith
    have e10 := mul_le_mul_of_nonneg_left e9 (mul_nonneg hC₁.le hn'.le)
    refine le_trans (le_of_eq ?_) (e10.trans (le_of_eq ?_)) <;> ring

lemma bound1 (x Q : ℝ) (hx : 3 ≤ x) (hQ : 1 ≤ Q) :
    3 ≤ ⌊x ^ (400 : ℝ)⌋₊ ∧ ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 2 / x ∧
      0 ≤ Real.log ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) * Q) ∧
      Real.log ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) * Q) ≤ 400 * Real.log x + Real.log Q := by
  have hx0 : 0 < x := by linarith
  set X := x ^ (400 : ℝ) with hX
  have hX3 : 3 ≤ X := by
    have : x ^ (1 : ℝ) ≤ x ^ (400 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hM3 : 3 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX3)
  have hMle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hMgt : X < ((⌊X⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one X
  set M := ⌊X⌋₊
  have hM3' : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) < M := by linarith
  refine ⟨hM3, ?_, ?_, ?_⟩
  · have h1 : X / 2 ≤ M := by linarith
    have h2 : (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤ (X / 2) ^ (-((1 : ℝ) / 400)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by norm_num)
    have h3 : (X / 2) ^ (-((1 : ℝ) / 400)) = X ^ (-((1 : ℝ) / 400)) / (2 : ℝ) ^ (-((1 : ℝ) / 400)) :=
      Real.div_rpow (by linarith) (by norm_num) _
    have h4 : X ^ (-((1 : ℝ) / 400)) = x⁻¹ := by
      rw [hX, ← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
      congr 1
      norm_num
    have h5 : (2 : ℝ)⁻¹ ≤ (2 : ℝ) ^ (-((1 : ℝ) / 400)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [h3, h4] at h2
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by positivity) hx0]
    have : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
    rw [this]
    linarith
  · apply Real.log_nonneg
    nlinarith
  · rw [Real.log_mul hM0.ne' (by linarith)]
    have h1 : Real.log (M : ℝ) ≤ Real.log X := Real.log_le_log hM0 hMle
    have h2 : Real.log X = 400 * Real.log x := by rw [hX, Real.log_rpow hx0]
    linarith

lemma bound2 (L : ℝ) (hL : 3 ≤ L) :
    3 ≤ ⌈L ^ 800⌉₊ ∧ ((⌈L ^ 800⌉₊ : ℕ) : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 1 / L ^ 2 ∧
      Real.log ((⌈L ^ 800⌉₊ : ℕ) : ℝ) ≤ 1 + 800 * Real.log L := by
  have hL0 : 0 < L := by linarith
  have hY : 3 ≤ L ^ 800 := by
    have : L ^ 1 ≤ L ^ 800 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [pow_one] at this
    linarith
  have h1 : L ^ 800 ≤ ((⌈L ^ 800⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈L ^ 800⌉₊ : ℕ) : ℝ) < L ^ 800 + 1 := Nat.ceil_lt_add_one (by positivity)
  set M := ⌈L ^ 800⌉₊
  have hM3' : (3 : ℝ) ≤ M := by linarith
  refine ⟨by exact_mod_cast hM3', ?_, ?_⟩
  · have h3 : (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤ (L ^ 800) ^ (-((1 : ℝ) / 400)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    have h4 : (L ^ 800) ^ (-((1 : ℝ) / 400)) = 1 / L ^ 2 := by
      rw [one_div (L ^ 2), ← Real.rpow_natCast L 800, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 2,
        ← Real.rpow_neg hL0.le]
      congr 1
      norm_num
    linarith
  · have h3 : (M : ℝ) ≤ 2 * L ^ 800 := by linarith
    have h4 : Real.log (M : ℝ) ≤ Real.log (2 * L ^ 800) := Real.log_le_log (by linarith) h3
    have h5 : Real.log (2 * L ^ 800) = Real.log 2 + 800 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    have h6 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith

lemma ev_small (p C₁ c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      L ^ p * (C₁ * (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L)))) ≤ 1 / 6 := by
  have T1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 8) 1 one_pos
  have T2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (c₁ / 2) (by positivity)
  have T := ((T1.const_mul 4).add (T2.const_mul (384 / c₁ ^ 4))).const_mul C₁
  simp only [mul_zero, add_zero] at T
  have E := T.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 6)
  have E2 := E.and (eventually_gt_atTop (0 : ℝ))
  obtain ⟨L₀, h⟩ := eventually_atTop.mp E2
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨h1, h2⟩ := h L hL
  refine le_trans (le_of_eq ?_) h1
  rw [Real.rpow_add h2, show ((8 : ℝ)) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : -1 * L = -L := by ring
  have e2 : -(c₁ / 2) * L = -(c₁ / 2 * L) := by ring
  rw [e1, e2]
  ring

end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion

namespace Formalism.HermitianLattices.GL2PrimeSums

open TailSumsHookFormulaTorsion in

theorem tail_bound_joint : TailSumBound := by
  intro ε hε hε1 C₁ c₁ CM hC₁ hc₁ hCM
  obtain ⟨L₀, hL₀⟩ := ev_small (6 / ε) C₁ c₁ hc₁
  set κ : ℝ := 1600 / ε + 1 with hκ
  set K₂ : ℝ := 4 * C₁ * (804 * κ ^ 2 + 5000000000) with hK₂
  have ev1 : ∀ᶠ x : ℝ in atTop, max L₀ 3 ≤ x ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have ev2 : ∀ᶠ x : ℝ in atTop, K₂ ≤ x ^ (ε / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((ev1.and ev2).and (eventually_ge_atTop (3 : ℝ)))
  refine ⟨x₀, C₁ * (804 * 802 ^ 2 + 5000000000) + 2 + CM + 200, ?_⟩
  intro x hx Q hQ hLlo hLhi a S hS hMert H1 H2
  obtain ⟨⟨h1, h2⟩, hx3⟩ := hx₀ x hx
  set L := Real.log Q with hLdef
  have hx0 : 0 < x := by linarith
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans (h1.trans hLlo)
  have hL3 : 3 ≤ L := (le_max_right _ _).trans (h1.trans hLlo)
  have hL0 : 0 < L := by linarith
  have hQ1 : 1 ≤ Q := by
    by_contra h
    rw [not_le] at h
    have := Real.log_nonpos hQ.le h.le
    linarith
  set E := C₁ * (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L))) with hE
  have hE0 : 0 ≤ E := by positivity
  have hxL : x ≤ L ^ (6 / ε) := by
    have h : (x ^ (ε / 6)) ^ (6 / ε) ≤ L ^ (6 / ε) :=
      Real.rpow_le_rpow (by positivity) hLlo (by positivity)
    rwa [← Real.rpow_mul hx0.le, show ε / 6 * (6 / ε) = 1 by field_simp, Real.rpow_one] at h
  have hxE : x * E ≤ 1 / 6 := (mul_le_mul_of_nonneg_right hxL hE0).trans (hL₀ L hLL₀)
  have hE6 : E ≤ 1 / 6 := by
    have h : 1 * E ≤ x * E := mul_le_mul_of_nonneg_right (by linarith) hE0
    linarith
  have hpw : ∀ n : ℕ, 3 ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (C₁ * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2)) :=
    fun n hn => pointwise a Q C₁ c₁ hC₁ hc₁ hQ (by linarith) H1 H2 n hn
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_three]
  constructor
  · obtain ⟨hM3, hMp, hl0, hl1⟩ := bound1 x Q hx3 hQ1
    have T := tail_main a S hS _ hM3 Q hQ1 C₁ E hC₁.le hE0 (fun n hn => hpw n (hM3.trans hn))
    set M := ⌊x ^ (400 : ℝ)⌋₊
    set y := x ^ (ε / 4) with hy
    have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by positivity)
    have hy2 : y ^ 2 = x ^ (ε / 2) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have hy4 : y ^ 4 = x ^ ε := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have hlx : Real.log x ≤ y / (ε / 4) := Real.log_le_rpow_div hx0.le (by positivity)
    have hl2 : Real.log (M * Q) ≤ κ * y := by
      have e : 400 * (y / (ε / 4)) + y = κ * y := by rw [hκ]; field_simp; ring
      linarith
    have hl3 : Real.log (M * Q) ^ 2 ≤ κ ^ 2 * y ^ 2 := by
      have h := pow_le_pow_left₀ hl0 hl2 2
      rwa [mul_pow] at h
    have hyy : 1 ≤ y ^ 2 := one_le_pow₀ hy1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le, ← hy4]
    have s1 : (804 * Real.log (M * Q) ^ 2 + 5000000000) * (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤
        ((804 * κ ^ 2 + 5000000000) * y ^ 2) * (2 / x) := by
      apply mul_le_mul _ hMp (by positivity) (by positivity)
      linarith
    have s2 : x * ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤
        x * (C₁ * (((804 * κ ^ 2 + 5000000000) * y ^ 2) * (2 / x)) + 3 * E) := by
      apply mul_le_mul_of_nonneg_left _ hx0.le
      have := mul_le_mul_of_nonneg_left s1 hC₁.le
      linarith
    have s3 : x * (C₁ * (((804 * κ ^ 2 + 5000000000) * y ^ 2) * (2 / x)) + 3 * E) =
        K₂ / 2 * y ^ 2 + 3 * (x * E) := by
      rw [hK₂]; field_simp; ring
    have s4 : K₂ * y ^ 2 ≤ y ^ 2 * y ^ 2 := by
      rw [← hy2] at h2
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have s5 : 1 ≤ y ^ 2 * y ^ 2 := one_le_mul_of_one_le_of_one_le hyy hyy
    have s6 : y ^ 4 = y ^ 2 * y ^ 2 := by ring
    rw [s6]
    linarith
  · obtain ⟨hM3, hMp, hlM⟩ := bound2 L hL3
    have T := tail_main a S hS _ hM3 Q hQ1 C₁ E hC₁.le hE0 (fun n hn => hpw n (hM3.trans hn))
    set M := ⌈L ^ 800⌉₊
    have hM3' : (3 : ℝ) ≤ M := by exact_mod_cast hM3
    have hM0 : (0 : ℝ) < M := by linarith
    have hlogL : Real.log L ≤ L := by
      have := Real.log_le_sub_one_of_pos hL0
      linarith
    have hl : Real.log (M * Q) = Real.log (M : ℝ) + L := Real.log_mul hM0.ne' hQ.ne'
    have hl0 : 0 ≤ Real.log (M * Q) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) hQ1)
    have hl2 : Real.log (M * Q) ≤ 802 * L := by linarith
    have hl3 : Real.log (M * Q) ^ 2 ≤ 802 ^ 2 * L ^ 2 := by
      have h := pow_le_pow_left₀ hl0 hl2 2
      rwa [mul_pow] at h
    have hLL : 1 ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have s1 : (804 * Real.log (M * Q) ^ 2 + 5000000000) * (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤
        804 * 802 ^ 2 + 5000000000 := by
      calc _ ≤ ((804 * 802 ^ 2 + 5000000000) * L ^ 2) * (1 / L ^ 2) := by
            apply mul_le_mul _ hMp (by positivity) (by positivity)
            linarith
        _ = _ := by field_simp
    have s2 : ‖∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤ Real.log (M : ℝ) + CM := by
      have h := hMert M (by linarith)
      rw [Nat.floor_natCast] at h
      refine (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) h)
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [norm_div, Complex.norm_natCast]
    have s3 : Real.log L ≤ ε / 4 * Real.log x := by
      have h := Real.log_le_log hL0 hLhi
      rwa [Real.log_rpow hx0] at h
    have s4 : ‖S‖ ≤ ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ + ‖∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ := by
      have h := norm_add_le (S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)) (∑ n ∈ Icc 1 M, a n / (n : ℂ))
      simpa using h
    have s5 : ε * Real.log x ≤ Real.log x := by
      have h := mul_le_mul_of_nonneg_right hε1.le (by linarith : 0 ≤ Real.log x)
      linarith
    have s6 := mul_le_mul_of_nonneg_left s1 hC₁.le
    have s7 : (C₁ * (804 * 802 ^ 2 + 5000000000) + 2 + CM) * 1 ≤
        (C₁ * (804 * 802 ^ 2 + 5000000000) + 2 + CM) * Real.log x :=
      mul_le_mul_of_nonneg_left hlogx (by positivity)
    linarith

end Formalism.HermitianLattices.GL2PrimeSums

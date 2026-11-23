import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBoundStatement

open Finset ArithmeticFunction Filter Topology

noncomputable section

namespace GlobalTheory.MangoldtSeries

theorem abel (a f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n * f n = (∑ n ∈ Icc 1 N, a n) * f (N + 1) +
      ∑ n ∈ range N, (∑ k ∈ Icc 1 (n + 1), a k) * (f (n + 1) - f (n + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show N + 1 + 1 = N + 2 from rfl, Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), ih,
      Finset.sum_range_succ, Finset.sum_Icc_succ_top (Nat.le_add_left 1 N)]
    ring

theorem rpow_diff_le (x s : ℝ) (hx : 1 ≤ x) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    |x ^ (-s) - (x + 1) ^ (-s)| ≤ 2 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hsplit : (x + 1) ^ (-s) = x ^ (-s) * (x / (x + 1)) ^ s := by
    rw [Real.div_rpow hx0.le hx1.le, Real.rpow_neg hx0.le, Real.rpow_neg hx1.le]
    have : 0 < x ^ s := Real.rpow_pos_of_pos hx0 s
    have : 0 < (x + 1) ^ s := Real.rpow_pos_of_pos hx1 s
    field_simp
  have ht1 : (x / (x + 1)) ^ s ≤ 1 :=
    Real.rpow_le_one (by positivity) (by rw [div_le_one hx1]; linarith) (by linarith)
  have hu : -1 ≤ -1 / (x + 1) := by
    rw [neg_div, neg_le_neg_iff, div_le_one hx1]; linarith
  have hb := one_add_mul_self_le_rpow_one_add hu h1
  have he : 1 + -1 / (x + 1) = x / (x + 1) := by field_simp; ring
  rw [he] at hb
  have htb : 1 - s / (x + 1) ≤ (x / (x + 1)) ^ s := by
    have : s * (-1 / (x + 1)) = -(s / (x + 1)) := by ring
    linarith
  have ha : 0 < x ^ (-s) := Real.rpow_pos_of_pos hx0 _
  have ha1 : x ^ (-s) ≤ 1 / x := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rw [hsplit]
  have hnn : 0 ≤ x ^ (-s) - x ^ (-s) * (x / (x + 1)) ^ s := by nlinarith
  rw [abs_of_nonneg hnn]
  have h3 : s / (x + 1) ≤ 2 / x := by
    rw [div_le_div_iff₀ hx1 hx0]; nlinarith
  calc x ^ (-s) - x ^ (-s) * (x / (x + 1)) ^ s = x ^ (-s) * (1 - (x / (x + 1)) ^ s) := by ring
    _ ≤ (1 / x) * (s / (x + 1)) :=
        mul_le_mul ha1 (by linarith) (by linarith) (by positivity)
    _ ≤ (1 / x) * (2 / x) := by gcongr
    _ = 2 / x ^ 2 := by ring

private lemma sum_Ico_sub_succ_eq_telescope (n : ℕ) :
    1 / (((n + 3 : ℕ) : ℝ) * Real.log ((n + 3 : ℕ) : ℝ) ^ 2) ≤
      1 / Real.log ((n + 2 : ℕ) : ℝ) - 1 / Real.log ((n + 3 : ℕ) : ℝ) := by
  push_cast
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have ha : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hab : Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have hb : 0 < Real.log ((n : ℝ) + 3) := by linarith
  have hd : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 3) ≤ -1 / ((n : ℝ) + 3) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 2) / ((n : ℝ) + 3) by positivity)
    have e : ((n : ℝ) + 2) / ((n : ℝ) + 3) - 1 = -1 / ((n : ℝ) + 3) := by field_simp; ring
    linarith
  have h : 1 ≤ (Real.log ((n : ℝ) + 3) - Real.log ((n : ℝ) + 2)) * ((n : ℝ) + 3) := by
    have := mul_le_mul_of_nonneg_right hd (show (0 : ℝ) ≤ (n : ℝ) + 3 by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    linarith
  rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg (Real.log ((n : ℝ) + 3))),
    mul_le_mul_of_nonneg_right hab hb.le]

theorem summable_inv_mul_log_sq :
    Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log n ^ 2)) := by
  set f := fun n : ℕ => 1 / ((n : ℝ) * Real.log n ^ 2) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; positivity
  have key : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 3), f i ≤
      f 2 + 1 / Real.log 2 - 1 / Real.log ((n + 2 : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero => norm_num [Finset.sum_range_succ, hf]
    | succ n ih =>
      rw [show n + 1 + 3 = (n + 3) + 1 from rfl, Finset.sum_range_succ,
        show n + 1 + 2 = n + 3 from rfl]
      have ht : f (n + 3) ≤ 1 / Real.log ((n + 2 : ℕ) : ℝ) - 1 / Real.log ((n + 3 : ℕ) : ℝ) :=
        sum_Ico_sub_succ_eq_telescope n
      linarith
  refine summable_of_sum_range_le hf0 (c := f 2 + 1 / Real.log 2) (fun m => ?_)
  have hlog : 0 ≤ 1 / Real.log ((m + 2 : ℕ) : ℝ) :=
    div_nonneg zero_le_one (Real.log_nonneg (by norm_cast; omega))
  calc ∑ i ∈ Finset.range m, f i ≤ ∑ i ∈ Finset.range (m + 3), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ => hf0 i)
    _ ≤ _ := key m
    _ ≤ _ := by linarith

private lemma conv_eq_coeff_alg_mul (a : ℕ → ℂ) (s : ℝ) (n : ℕ) :
    a n / (n : ℂ) ^ (s : ℂ) = a n * ((((n : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, div_eq_mul_inv]

private lemma sum_div_cpow_eq_abel_summation (a : ℕ → ℂ) (s : ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n / (n : ℂ) ^ (s : ℂ) =
      (∑ n ∈ Icc 1 N, a n) * ((((N + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) +
      ∑ n ∈ range N, (∑ k ∈ Icc 1 (n + 1), a k) *
        (((((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) - ((((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
  rw [Finset.sum_congr rfl (fun n _ => conv_eq_coeff_alg_mul a s n)]
  exact abel a (fun m => ((((m : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) N

private lemma sum_range_lseries_term_eq_sum_Icc_div_cpow (a : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    ∑ n ∈ range (N + 1), LSeries.term a s n = ∑ n ∈ Icc 1 N, a n / (n : ℂ) ^ s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (Nat.le_add_left 1 N),
      LSeries.term_of_ne_zero (Nat.succ_ne_zero N)]

private lemma tendsto_sum_Icc_mul_rpow_zero_of_bound_log_sq (a : ℕ → ℂ) (K : ℝ)
    (hA : ∀ N : ℕ, 2 ≤ N → ‖∑ n ∈ Icc 1 N, a n‖ ≤ K * N / Real.log N ^ 2) (s : ℝ) (hs : 1 ≤ s) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n) * ((((N + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => |K| / Real.log N ^ 2) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact (tendsto_pow_atTop two_ne_zero).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNne := hN0.ne'
  have hLne := hL.ne'
  have hp : 0 < (((N + 1 : ℕ) : ℝ) ^ (-s) : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hle : (((N + 1 : ℕ) : ℝ) ^ (-s) : ℝ) ≤ 1 / N := by
    calc (((N + 1 : ℕ) : ℝ) ^ (-s) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (by linarith)
      _ = 1 / ((N + 1 : ℕ) : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / N := by
          apply one_div_le_one_div_of_le hN0
          push_cast
          linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have hAN : ‖∑ n ∈ Icc 1 N, a n‖ ≤ |K| * N / Real.log N ^ 2 :=
    (hA N hN).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K) hN0.le) (sq_nonneg _))
  calc ‖∑ n ∈ Icc 1 N, a n‖ * (((N + 1 : ℕ) : ℝ) ^ (-s)) ≤
        (|K| * N / Real.log N ^ 2) * (1 / N) := mul_le_mul hAN hle hp.le (by positivity)
    _ = |K| / Real.log N ^ 2 := by field_simp

private lemma summable_indicator_add_inv_mul_log_sq (a : ℕ → ℂ) (K : ℝ) :
    Summable (fun n : ℕ => 2 * ‖a 1‖ * (if n = 0 then 1 else 0) +
      2 * |K| * (1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2))) := by
  refine Summable.add ?_ ?_
  · exact ((hasSum_ite_eq 0 (1 : ℝ)).summable).mul_left _
  · exact ((summable_nat_add_iff 1).2 summable_inv_mul_log_sq).mul_left _

private lemma norm_sum_Icc_mul_rpow_sub_rpow_le (a : ℕ → ℂ) (K : ℝ)
    (hA : ∀ N : ℕ, 2 ≤ N → ‖∑ n ∈ Icc 1 N, a n‖ ≤ K * N / Real.log N ^ 2)
    (s : ℝ) (h1 : 1 ≤ s) (h2 : s ≤ 2) (n : ℕ) :
    ‖(∑ k ∈ Icc 1 (n + 1), a k) *
        (((((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) - ((((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))‖ ≤
      2 * ‖a 1‖ * (if n = 0 then 1 else 0) +
        2 * |K| * (1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hx1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hx0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hd := rpow_diff_le ((n + 1 : ℕ) : ℝ) s hx1 h1 h2
  have e2 : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, e2]
  have hK0 : 0 ≤ 2 * |K| * (1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    mul_nonneg (by positivity) (one_div_nonneg.2 (mul_nonneg hx0.le (sq_nonneg _)))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hA1 : ∑ k ∈ Icc 1 (0 + 1), a k = a 1 := by simp
    rw [hA1, if_pos rfl]
    have hd' : |((0 + 1 : ℕ) : ℝ) ^ (-s) - (((0 + 1 : ℕ) : ℝ) + 1) ^ (-s)| ≤ 2 := by
      calc _ ≤ 2 / ((0 + 1 : ℕ) : ℝ) ^ 2 := hd
        _ = 2 := by norm_num
    calc ‖a 1‖ * |((0 + 1 : ℕ) : ℝ) ^ (-s) - (((0 + 1 : ℕ) : ℝ) + 1) ^ (-s)| ≤ ‖a 1‖ * 2 :=
          mul_le_mul_of_nonneg_left hd' (norm_nonneg _)
      _ ≤ _ := by linarith
  · rw [if_neg (by omega), mul_zero, zero_add]
    have hL : 0 < Real.log ((n + 1 : ℕ) : ℝ) := Real.log_pos (by norm_cast; omega)
    have hxne := hx0.ne'
    have hLne := hL.ne'
    have hAn : ‖∑ k ∈ Icc 1 (n + 1), a k‖ ≤
        |K| * ((n + 1 : ℕ) : ℝ) / Real.log ((n + 1 : ℕ) : ℝ) ^ 2 :=
      (hA (n + 1) (by omega)).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K) hx0.le) (sq_nonneg _))
    calc _ ≤ (|K| * ((n + 1 : ℕ) : ℝ) / Real.log ((n + 1 : ℕ) : ℝ) ^ 2) *
          (2 / ((n + 1 : ℕ) : ℝ) ^ 2) := mul_le_mul hAn hd (abs_nonneg _) (by positivity)
      _ = _ := by field_simp

private lemma tendsto_mul_rpow_sub_rpow_nhdsGT_one (c : ℂ) (n : ℕ) :
    Tendsto (fun s : ℝ => c * (((((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) -
        ((((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))) (𝓝[>] 1)
      (𝓝 (c * (((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) -
        ((((n + 2 : ℕ) : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)))) := by
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  have h1 : Continuous (fun s : ℝ => (((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ)) :=
    continuous_const.rpow continuous_neg (fun _ => Or.inl (by positivity))
  have h2 : Continuous (fun s : ℝ => (((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ)) :=
    continuous_const.rpow continuous_neg (fun _ => Or.inl (by positivity))
  exact (continuous_const.mul ((Complex.continuous_ofReal.comp h1).sub
    (Complex.continuous_ofReal.comp h2))).tendsto 1

theorem tendsto_of_partial_sums (a : ℕ → ℂ) (K : ℝ) (G : ℝ → ℂ)
    (hA : ∀ N : ℕ, 2 ≤ N → ‖∑ n ∈ Icc 1 N, a n‖ ≤ K * N / Real.log N ^ 2)
    (hG : ContinuousAt G 1)
    (hL : ∀ s : ℝ, 1 < s → LSeriesHasSum a s (G s)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 (G 1)) := by
  have hB := summable_indicator_add_inv_mul_log_sq a K
  have hg := norm_sum_Icc_mul_rpow_sub_rpow_le a K hA
  have hsum : ∀ s : ℝ, 1 ≤ s → s ≤ 2 →
      Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ) ^ (s : ℂ)) atTop
        (𝓝 (∑' n : ℕ, (∑ k ∈ Icc 1 (n + 1), a k) *
          (((((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) - ((((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)))) := by
    intro s h1 h2
    have hS := (hB.of_norm_bounded (hg s h1 h2)).hasSum.tendsto_sum_nat
    have h := (tendsto_sum_Icc_mul_rpow_zero_of_bound_log_sq a K hA s h1).add hS
    rw [zero_add] at h
    refine h.congr (fun N => ?_)
    rw [sum_div_cpow_eq_abel_summation]
  have hF : Tendsto (fun s : ℝ => ∑' n : ℕ, (∑ k ∈ Icc 1 (n + 1), a k) *
        (((((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) - ((((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))) (𝓝[>] 1)
      (𝓝 (∑' n : ℕ, (∑ k ∈ Icc 1 (n + 1), a k) *
        (((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) -
          ((((n + 2 : ℕ) : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)))) := by
    refine tendsto_tsum_of_dominated_convergence hB (fun n => tendsto_mul_rpow_sub_rpow_nhdsGT_one _ n) ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with s hs1 hs2
    exact hg s (le_of_lt hs1) (le_of_lt hs2)
  have hGs : ∀ s : ℝ, 1 < s → s ≤ 2 → G s = ∑' n : ℕ, (∑ k ∈ Icc 1 (n + 1), a k) *
      (((((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) - ((((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
    intro s h1 h2
    have h1' : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ) ^ (s : ℂ)) atTop (𝓝 (G s)) := by
      have h := (HasSum.tendsto_sum_nat (hL s h1)).comp (tendsto_add_atTop_nat 1)
      refine h.congr (fun N => ?_)
      exact sum_range_lseries_term_eq_sum_Icc_div_cpow a s N
    exact tendsto_nhds_unique h1' (hsum s h1.le h2)
  have hG1 : G 1 = ∑' n : ℕ, (∑ k ∈ Icc 1 (n + 1), a k) *
      (((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) - ((((n + 2 : ℕ) : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)) := by
    have hGt : Tendsto G (𝓝[>] 1) (𝓝 (G 1)) := hG.tendsto.mono_left nhdsWithin_le_nhds
    have hev : G =ᶠ[𝓝[>] 1] (fun s : ℝ => ∑' n : ℕ, (∑ k ∈ Icc 1 (n + 1), a k) *
        (((((n + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) - ((((n + 2 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with s hs1 hs2
      exact hGs s hs1 (le_of_lt hs2)
    exact tendsto_nhds_unique (hGt.congr' hev) hF
  rw [hG1]
  refine (hsum 1 le_rfl (by norm_num)).congr (fun N => Finset.sum_congr rfl (fun n _ => ?_))
  rw [Complex.ofReal_one, Complex.cpow_one]

theorem sum_not_coprime_le (q N : ℕ) (hq : q ≠ 0) :
    ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n ≤ Nat.log 2 N * Real.log q := by
  classical
  set S := (Icc 1 N).filter (fun n => ¬ n.Coprime q) with hS
  set L := Nat.log 2 N with hL
  have hT0 : ∀ p n : ℕ, 0 ≤ (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro p n; split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_rfl
  have hpt : ∀ n ∈ S, Λ n ≤ ∑ p ∈ q.primeFactors,
      (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hnc⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with hpp
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      have hmin : (p ^ k).minFac = p := by rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
      have hpq : p ∣ q := by
        by_contra h
        exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
      have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, hq⟩
      have hkL : k ∈ Icc 1 L := by
        rw [Finset.mem_Icc]
        refine ⟨hk, Nat.le_log_of_pow_le (by norm_num) ?_⟩
        exact (Nat.pow_le_pow_left hp.two_le k).trans hnN
      have hTp : (if p ^ k ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) = Real.log p :=
        if_pos (Finset.mem_image.2 ⟨k, hkL, rfl⟩)
      rw [hmin, ← hTp]
      exact Finset.single_le_sum (f := fun p' : ℕ => if p ^ k ∈ (Icc 1 L).image (p' ^ ·) then Real.log p' else 0)
        (fun p' _ => hT0 p' (p ^ k)) hpmem
    · exact Finset.sum_nonneg (fun p _ => hT0 p n)
  have hcard : ∀ p : ℕ, ((S ∩ (Icc 1 L).image (p ^ ·)).card : ℝ) ≤ L := by
    intro p
    have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := (Icc 1 L).image (p ^ ·)))
    have h2 := Finset.card_image_le (s := Icc 1 L) (f := (p ^ ·))
    have h3 : (Icc 1 L).card = L := by simp
    exact_mod_cast (h1.trans h2).trans h3.le
  calc ∑ n ∈ S, Λ n ≤ ∑ n ∈ S, ∑ p ∈ q.primeFactors,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ S,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, (L : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p _
        rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcard p) (Real.log_natCast_nonneg p)
    _ = (L : ℝ) * Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [← Finset.mul_sum, Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ (L : ℝ) * Real.log q := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.log_le_log
        · apply Finset.prod_pos
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q))

theorem norm_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
      ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
      Nat.log 2 N * Real.log q := by
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => ¬ n.Coprime q)]
  rw [Finset.sum_eq_zero (s := (Icc 1 N).filter (fun n => ¬¬ n.Coprime q)) ?_, add_zero]
  · calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q),
          ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
            ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter] at hn
          have hχ0 : χ (n : ZMod q) = 0 := by
            apply MulChar.map_nonunit
            rw [ZMod.isUnit_iff_coprime]
            exact hn.2
          rw [hχ0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          calc Λ n * ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ Λ n * 1 :=
                mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
                  ArithmeticFunction.vonMangoldt_nonneg
            _ = Λ n := mul_one _
      _ ≤ _ := sum_not_coprime_le q N (NeZero.ne q)
  · intro n hn
    rw [Finset.mem_filter, not_not] at hn
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn.2)
    push_cast at h
    rw [h, sub_self]

theorem exp_neg_sqrt_le (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    Real.exp (-c * Real.sqrt L) ≤ 24 / c ^ 4 / L ^ 2 := by
  have hy : 0 ≤ c * Real.sqrt L := by positivity
  have h4 := Real.pow_div_factorial_le_exp (c * Real.sqrt L) hy 4
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have hpow : (c * Real.sqrt L) ^ 4 = c ^ 4 * L ^ 2 := by
    rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul (Real.sqrt L), hs]
  have hE : c ^ 4 * L ^ 2 / 24 ≤ Real.exp (c * Real.sqrt L) := by
    calc c ^ 4 * L ^ 2 / 24 = (c * Real.sqrt L) ^ 4 / ((4 : ℕ).factorial : ℝ) := by
          rw [hpow]; norm_num [Nat.factorial]
      _ ≤ _ := h4
  rw [neg_mul, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  calc (24 / c ^ 4 / L ^ 2)⁻¹ = c ^ 4 * L ^ 2 / 24 := by field_simp
    _ ≤ _ := hE

theorem natLog_le (N : ℕ) (hN : 2 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ 6 / Real.log 2 * N / Real.log N ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hk : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    have h := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h' : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rwa [Real.log_pow] at this
  have hc : Real.log N ^ 3 ≤ 6 * N := by
    have h := Real.pow_div_factorial_le_exp (Real.log N) hlN.le 3
    rw [Real.exp_log hN0] at h
    norm_num [Nat.factorial] at h
    linarith
  rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ hl2]
  have := mul_le_mul_of_nonneg_right hk (sq_nonneg (Real.log N))
  nlinarith

theorem logDerivSeries : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount →
    Formalism.ZeroFreeDirichlet.ZFRDirichlet → Formalism.HermitianLattices.GL2a2.LogDerivSeries := by
  intro hZ hX hD hC hZF
  unfold Formalism.HermitianLattices.GL2a2.LogDerivSeries
  intro q _ χ hχ
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨C, c, hc, hψ⟩ :=
    GlobalTheory.T.exists_norm_psi0_le_exp_sqrt_log hZ hX hD hC hZF χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  have hχ1 : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  have hA : ∀ N : ℕ, 2 ≤ N →
      ‖∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
        (|C| * 24 / c ^ 4 + 6 / Real.log 2 * Real.log q) * N / Real.log N ^ 2 := by
    intro N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlog : 0 < Real.log N := Real.log_pos hN1
    have h1 := norm_sub_primitive_le χ N
    have h2 : ‖∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
        C * N * Real.exp (-c * Real.sqrt (Real.log N)) := by
      have h := hψ N (by exact_mod_cast hN)
      unfold Formalism.MainNotions.GlobalTheoryTheory.psi0 at h
      rw [if_neg hχ1, sub_zero, Nat.floor_natCast] at h
      exact h
    have h3 := exp_neg_sqrt_le c (Real.log N) hc hlog
    have h4 := natLog_le N hN
    have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have e1 : (Nat.log 2 N : ℝ) * Real.log q ≤ (6 / Real.log 2 * N / Real.log N ^ 2) * Real.log q :=
      mul_le_mul_of_nonneg_right h4 hlq
    have e2 : C * N * Real.exp (-c * Real.sqrt (Real.log N)) ≤
        |C| * N * (24 / c ^ 4 / Real.log N ^ 2) := by
      calc C * N * Real.exp (-c * Real.sqrt (Real.log N)) ≤
            |C| * N * Real.exp (-c * Real.sqrt (Real.log N)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg N))
              (Real.exp_pos _).le
        _ ≤ |C| * N * (24 / c ^ 4 / Real.log N ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hfin : (|C| * 24 / c ^ 4 + 6 / Real.log 2 * Real.log q) * N / Real.log N ^ 2 =
        (6 / Real.log 2 * N / Real.log N ^ 2) * Real.log q + |C| * N * (24 / c ^ 4 / Real.log N ^ 2) := by
      ring
    have htri := norm_add_le
      (∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
        ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor))
      (∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor))
    rw [sub_add_cancel] at htri
    linarith
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hne : DirichletCharacter.LFunction χ 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hG : ContinuousAt (fun s : ℝ => -(deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
      DirichletCharacter.LFunction χ (s : ℂ))) 1 := by
    have hcont : ContinuousAt (fun z : ℂ => -(deriv (DirichletCharacter.LFunction χ) z /
        DirichletCharacter.LFunction χ z)) ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_one]
      exact ((hdiff.deriv.continuous.continuousAt).div hdiff.continuous.continuousAt hne).neg
    exact hcont.comp Complex.continuous_ofReal.continuousAt
  have hL : ∀ s : ℝ, 1 < s → LSeriesHasSum (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (s : ℂ)
      (-(deriv (DirichletCharacter.LFunction χ) (s : ℂ) / DirichletCharacter.LFunction χ (s : ℂ))) := by
    intro s hs
    have hre : 1 < (s : ℂ).re := by simpa using hs
    have hfun : (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) =
        ((fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => ((Λ n : ℝ) : ℂ))) := by
      ext n
      simp [mul_comm]
    rw [hfun, LSeriesHasSum_iff]
    refine ⟨DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hre, ?_⟩
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre]
    have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (s : ℂ)] LSeries (fun n : ℕ => χ (n : ZMod q)) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
      exact DirichletCharacter.LFunction_eq_LSeries χ hz
    rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hre, neg_div]
  have h := tendsto_of_partial_sums (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q))
    (|C| * 24 / c ^ 4 + 6 / Real.log 2 * Real.log q)
    (fun s : ℝ => -(deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
      DirichletCharacter.LFunction χ (s : ℂ))) hA hG hL
  simp only [Complex.ofReal_one] at h
  exact h

end GlobalTheory.MangoldtSeries

import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionEqTsumOfOneLt
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.DirichletDeriv

theorem rpow_neg_le {q n : ℕ} (hn : 1 ≤ n) (hnq : n ≤ q) {x : ℝ}
    (hx : 1 - 2 / Real.log (3 * q) ≤ x) : (n : ℝ) ^ (-x) ≤ Real.exp 2 * (n : ℝ)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnq' : (n : ℝ) ≤ q := by exact_mod_cast hnq
  have hL : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hl : Real.log n ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have h1 : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (2 / Real.log (3 * q) + (-1)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  refine h1.trans ?_
  rw [Real.rpow_add (by linarith), Real.rpow_neg_one]
  gcongr
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc, div_le_iff₀ hL]
  linarith

theorem norm_LFunction_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (h1 : 1 - 2 / Real.log (3 * q) ≤ s.re) (h2 : 1 / 20 ≤ s.re) (h3 : ‖s‖ ≤ 2) :
    ‖LFunction χ s‖ ≤ 84 * Real.exp 2 * Real.log (3 * q) := by
  have hq : 1 ≤ q := NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 0 < s.re := by linarith
  have hL : 1 ≤ Real.log (3 * q) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl : Real.log q ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hE : 0 < Real.exp 2 := Real.exp_pos 2
  have ht := GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le q χ hχ s hs q hq
  have hd : ‖s‖ / s.re ≤ 40 := by rw [div_le_iff₀ hs]; linarith
  have ht2 : 2 * q * (1 + ‖s‖ / s.re) * (q : ℝ) ^ (-s.re) ≤ 82 * Real.exp 2 := by
    calc 2 * q * (1 + ‖s‖ / s.re) * (q : ℝ) ^ (-s.re)
        ≤ 2 * q * (1 + 40) * (Real.exp 2 * (q : ℝ)⁻¹) := by
          gcongr
          exact rpow_neg_le hq le_rfl h1
      _ = 82 * Real.exp 2 := by field_simp; ring
  have hsum : ‖∑ n ∈ Finset.Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
      ≤ Real.exp 2 * (1 + Real.log q) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 q, Real.exp 2 * (n : ℝ)⁻¹ := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_Icc] at hn
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
          exact (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans
            (rpow_neg_le hn.1 hn.2 h1)
      _ = Real.exp 2 * (harmonic q : ℝ) := by
          rw [← Finset.mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ Real.exp 2 * (1 + Real.log q) := by
          gcongr
          exact harmonic_le_one_add_log q
  have h4 := norm_le_norm_sub_add (LFunction χ s)
    (∑ n ∈ Finset.Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s))
  nlinarith

theorem exists_norm_deriv_LFunction_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ : ℝ,
      1 - 1 / Real.log (3 * q) ≤ σ → σ ≤ 1 →
        ‖deriv (LFunction χ) σ‖ ≤ C * Real.log (3 * q) ^ 2 := by
  refine ⟨336 * Real.exp 2, by positivity, fun q _ χ hχ σ h1 h2 => ?_⟩
  have hq : 2 ≤ q := by
    have h0 := NeZero.pos q
    by_contra h
    obtain rfl : q = 1 := by omega
    exact hχ (DirichletCharacter.level_one χ)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : 1.38 ≤ Real.log (3 * q) := by
    have h4 : Real.log (2 ^ 2) ≤ Real.log (3 * q) := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h4
    push_cast at h4
    linarith [Real.log_two_gt_d9]
  set L := Real.log (3 * q) with hLdef
  have hL0 : 0 < L := by linarith
  have hinv : 1 / L ≤ 3 / 4 := by rw [div_le_iff₀ hL0]; linarith
  have hinv0 : 0 < 1 / L := by positivity
  have hr : 0 < 1 / L / 4 := by positivity
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := LFunction χ) (c := (σ : ℂ))
    (C := 84 * Real.exp 2 * L) hr (differentiable_LFunction hχ).diffContOnCl (fun z hz => by
      rw [mem_sphere_iff_norm] at hz
      have hre := Complex.abs_re_le_norm (z - σ)
      rw [hz, Complex.sub_re, Complex.ofReal_re, abs_le] at hre
      have h2L : 2 / L = 2 * (1 / L) := by ring
      refine norm_LFunction_le χ hχ (by rw [← hLdef, h2L]; linarith [hre.1]) (by linarith [hre.1]) ?_
      have h5 := norm_le_norm_sub_add z (σ : ℂ)
      rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h5
      linarith)
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

end GlobalTheory.DirichletDeriv

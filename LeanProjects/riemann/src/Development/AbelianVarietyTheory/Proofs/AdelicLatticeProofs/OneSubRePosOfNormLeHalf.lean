import Mathlib

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem eulerTerm_norm_le_rpow (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  have hn0 : 0 < n := by omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  have : (0 : ℝ) ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc ‖c‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) := by gcongr
    _ = (n : ℝ) ^ (-s.re) := one_mul _

theorem eulerTerm_norm_le_half (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 1 < s.re) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  refine (eulerTerm_norm_le_rpow n hn c s hc).trans ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem one_sub_re_pos_of_norm_le_half (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : 0 < (1 - z).re := by
  rw [Complex.sub_re, Complex.one_re]
  have := Complex.re_le_norm z
  linarith

theorem eulerProduct_eq_exp_and_pos :
    ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → (∀ s : ℂ, 1 < s.re → Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) ∧ HasProd (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))))) ∧ ∀ e : ι ≃ ι, (∀ i, N (e i) = N i) → (∀ i, c (e i) = starRingEnd ℂ (c i)) → ∀ s : ℂ, 1 < s.re → s.im = 0 → (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).im = 0 ∧ 0 < (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).re := by
  intro ι N c hN hc hsum
  have hsmall : ∀ s : ℂ, 1 < s.re → ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    fun s hs i => eulerTerm_norm_le_half (N i) (hN i) (c i) s (hc i) hs
  have hne : ∀ s : ℂ, 1 < s.re → ∀ i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
    intro s hs i h
    have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hsummable : ∀ s : ℂ, 1 < s.re →
      Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    refine Summable.of_norm_bounded ((hsum s.re hs).mul_left (3 / 2)) (fun i => ?_)
    rw [norm_neg, sub_eq_add_neg]
    refine (Complex.norm_log_one_add_half_le_self (by rw [norm_neg]; exact hsmall s hs i)).trans ?_
    rw [norm_neg]
    gcongr
    exact eulerTerm_norm_le_rpow (N i) (hN i) (c i) s (hc i)
  refine ⟨fun s hs => ⟨hsummable s hs, ?_⟩, ?_⟩
  · convert (hsummable s hs).hasSum.cexp using 1
    funext i
    simp only [Function.comp, Complex.exp_neg, Complex.exp_log (hne s hs i)]
  · intro e hNe hce s hs him
    have hsre : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hreal : ∀ i, starRingEnd ℂ (((N i : ℕ) : ℂ) ^ (-s)) = ((N i : ℕ) : ℂ) ^ (-s) := by
      intro i
      rw [hsre, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]
    have hterm : ∀ i, starRingEnd ℂ (-Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) =
        -Complex.log (1 - c (e i) * ((N (e i) : ℕ) : ℂ) ^ (-s)) := by
      intro i
      have harg : (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)).arg ≠ Real.pi := by
        rw [Ne, Complex.arg_eq_pi_iff]
        have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
        intro h
        linarith [h.1]
      rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hreal, hce, hNe]
    set S := ∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) with hS
    have hconj : starRingEnd ℂ S = S := by
      rw [hS, Complex.conj_tsum]
      simp_rw [hterm]
      exact Equiv.tsum_eq e (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
    have hSim : S.im = 0 := Complex.conj_eq_iff_im.mp hconj
    rw [Complex.exp_im, Complex.exp_re, hSim, Real.sin_zero, Real.cos_zero, mul_zero, mul_one]
    exact ⟨rfl, Real.exp_pos _⟩

end GlobalTheory

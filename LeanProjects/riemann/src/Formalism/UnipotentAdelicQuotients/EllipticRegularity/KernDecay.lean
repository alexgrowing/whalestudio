import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def derivL1Norm (f : V → ℂ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖

lemma derivL1Norm_nonneg (f : V → ℂ) (n : ℕ) : 0 ≤ derivL1Norm f n :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

lemma integrable_iteratedFDeriv {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) := by
  have hcont : Continuous (fun v => iteratedFDeriv ℝ n f v) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hc : Continuous (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    (continuous_norm.pow k).mul hcont.norm
  have hs : HasCompactSupport (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    ((hfc.iteratedFDeriv n).comp_left norm_zero).mul_left
  exact hc.integrable_of_hasCompactSupport hs

lemma pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖w‖ ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * derivL1Norm f n := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := n)
    (hf.of_le (by exact_mod_cast le_top))
    (fun k j _ _ => integrable_iteratedFDeriv hf hfc k j) (k := 0) (n := n) (by simp) le_rfl w
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
    Finset.sum_product, Finset.sum_range_one] at h
  unfold derivL1Norm
  exact h

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have htn : 0 ≤ t ^ n := pow_nonneg ht n
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n ≤ 2 ^ n * (1 + t ^ n) := le_mul_of_one_le_right h2 (by linarith)
    linarith
  · have h1 : (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n * t ^ n ≤ 2 ^ n * (1 + t ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2
    rw [mul_pow] at h1
    linarith

lemma one_add_pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (n : ℕ) (w : V) :
    (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by
  have hL := pow_mul_norm_fourier_le hf hfc n w
  have h0 := pow_mul_norm_fourier_le hf hfc 0 w
  simp only [pow_zero, one_mul] at h0
  have hmono : derivL1Norm f 0 ≤ derivL1Norm f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => integral_nonneg fun _ => norm_nonneg _)
  have hpos : 0 ≤ ‖𝓕 f w‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hb := one_add_pow_le ‖w‖ (norm_nonneg w) n
  calc (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖𝓕 f w‖ := mul_le_mul_of_nonneg_right hb hpos
    _ = 2 ^ n * (‖𝓕 f w‖ + ‖w‖ ^ n * ‖𝓕 f w‖) := by ring
    _ ≤ 2 ^ n * (derivL1Norm f n + 2 ^ n * derivL1Norm f n) := by
        refine mul_le_mul_of_nonneg_left ?_ h2
        linarith
    _ = 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by ring

lemma norm_fourier_le_rpow {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n * (1 + ‖w‖) ^ (-(n : ℝ)) := by
  have h5 := one_add_pow_mul_norm_fourier_le hf hfc n w
  have hp : 0 < 1 + ‖w‖ := by positivity
  have hpn : 0 < (1 + ‖w‖) ^ n := pow_pos hp n
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpn]
  linarith [h5, mul_comm ((1 + ‖w‖) ^ n) ‖𝓕 f w‖]

lemma lintegral_weight_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) ≤
      ENNReal.ofReal (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1))) *
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  dsimp only
  have hp : 0 < 1 + ‖w‖ := by positivity
  have h6 := norm_fourier_le_rpow hf hfc (m + (Module.finrank ℝ V + 1)) w
  have hA : 0 ≤ (1 + ‖w‖) ^ m := by positivity
  have hC : 0 ≤ 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
      derivL1Norm f (m + (Module.finrank ℝ V + 1)) :=
    mul_nonneg (by positivity) (derivL1Norm_nonneg f _)
  have hexp : (1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ)) =
      (1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  calc (1 + ‖w‖) ^ m * ‖𝓕 f w‖
      ≤ (1 + ‖w‖) ^ m * (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h6 hA
    _ = 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        ((1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hexp]

lemma lintegral_weight_fourier_lt_top {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_weight_fourier_le hf hfc m)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm ?_))
  push_cast
  linarith

end

end ZetaZeros.D.EllReg

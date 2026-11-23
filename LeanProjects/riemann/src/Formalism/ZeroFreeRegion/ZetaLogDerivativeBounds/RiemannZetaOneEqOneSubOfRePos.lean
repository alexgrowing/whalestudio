import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

lemma partial_dz (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, dz s i =
      1 - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) -
        (s - 1) * ∑ i ∈ Finset.range N, ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [dz]
    push_cast
    ring

lemma one_lt_identity {s : ℂ} (hs : 1 < s.re) : (s - 1) * riemannZeta s = s - Dz s := by
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable (dz s) := (summable_norm_dz hs0).of_norm
  have hf : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hf.hasSum
  have hG : HasSum (fun i : ℕ => ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)) (riemannZeta s - 1) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hz
    have e : ∀ i : ℕ, ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) = 1 / (((i + 1 : ℕ) : ℂ) + 1) ^ s := by
      intro i
      have : ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) = (((i + 1 : ℕ) : ℂ) + 1) := by push_cast; ring
      rw [this, cpow_neg, one_div]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_cpow, div_one] at h1
    have hfun : (fun i : ℕ => ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)) =
        (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s) := funext e
    rw [hfun]
    exact h1
  have hc : Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hp : 0 < s.re - 1 := by linarith
    have := (tendsto_rpow_neg_atTop hp).comp hN
    refine this.congr (fun N => ?_)
    simp only [Function.comp]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    rw [Complex.sub_re, Complex.one_re]
    ring
  have hD : Tendsto (fun N => ∑ i ∈ Finset.range N, dz s i) atTop
      (𝓝 (Dz s)) :=
    hsum.hasSum.tendsto_sum_nat
  have hR : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, dz s i) atTop
      (𝓝 (1 - 0 - (s - 1) * (riemannZeta s - 1))) := by
    have := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hc).sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => s - 1) atTop (𝓝 (s - 1))).mul hG.tendsto_sum_nat)
    refine this.congr (fun N => ?_)
    exact (partial_dz s N).symm
  have hlim := tendsto_nhds_unique hD hR
  rw [hlim]
  ring

lemma riemannZetaOne_eq_one_sub_of_re_pos {s : ℂ} (hs : 0 < s.re) : riemannZeta₁ s = s - Dz s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ (fun z => z - Dz z) {z : ℂ | 0 < z.re} :=
    (differentiableOn_id.sub Dz_differentiableOn).analyticOnNhd hU
  have heq : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun z => z - Dz z) := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    rw [← one_lt_identity hz]
    unfold riemannZeta₁ riemannZeta₀
    rw [if_neg hz1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.mpr hz1)]
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) heq hs

end ComplexPowerDifferenceIntegral

end Formalism.ZF

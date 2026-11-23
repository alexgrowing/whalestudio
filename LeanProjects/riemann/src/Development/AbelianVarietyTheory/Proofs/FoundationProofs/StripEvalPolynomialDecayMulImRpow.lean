import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

open Filter Topology

private lemma norm_eval_add_C_le_of_coeff_le (w : ℕ) (a z : ℂ) (p : ℂ[X]) (K e : ℝ) (hK : 0 ≤ K)
    (he : 0 ≤ e) (hp : p ∈ degreeLT ℂ (w + 1))
    (hc : ∀ j ≤ w, ‖p.coeff j‖ ≤ K * e * (1 + ‖z‖) ^ w) :
    ‖(p + C a).eval z‖ ≤ ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by
  have hdeg : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  rw [eval_add, eval_C, eval_eq_sum_range' hdeg]
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hterm : ∀ j ∈ Finset.range (w + 1),
      ‖p.coeff j * z ^ j‖ ≤ K * e * (1 + ‖z‖) ^ (2 * w) := by
    intro j hj
    have hjw : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [norm_mul, norm_pow]
    have h1 : ‖z‖ ^ j ≤ (1 + ‖z‖) ^ w :=
      (pow_le_pow_left₀ (norm_nonneg z) (by linarith) j).trans (pow_le_pow_right₀ hz1 hjw)
    calc ‖p.coeff j‖ * ‖z‖ ^ j ≤ (K * e * (1 + ‖z‖) ^ w) * (1 + ‖z‖) ^ w :=
          mul_le_mul (hc j hjw) h1 (by positivity) (by positivity)
      _ = K * e * (1 + ‖z‖) ^ (2 * w) := by ring
  calc ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j + a‖
      ≤ ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j * z ^ j‖ + ‖a‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), K * e * (1 + ‖z‖) ^ (2 * w) + ‖a‖ := by
        gcongr with j hj; exact hterm j hj
    _ = ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by simp; ring

theorem strip_eval_decay : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n →
      ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  intro w n a V C' c hw hc hV hcoef ε hε
  set K := max C' 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hwpos : (0 : ℝ) < (w : ℝ) / 2 := by
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h1 : Tendsto (fun y : ℝ => ‖a‖ * y ^ (-(w : ℝ) / 2)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hwpos).const_mul ‖a‖
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun y => ?_)
    simp only [neg_div]
  have h2 : Tendsto (fun y : ℝ => (w + 1) * (K * 4 ^ w) * (y ^ (2 * w) / Real.exp (c * y)))
      atTop (𝓝 0) := by
    have := ((isLittleO_pow_exp_pos_mul_atTop (2 * w) hc).tendsto_div_nhds_zero).const_mul
      ((w + 1) * (K * 4 ^ w))
    rwa [mul_zero] at this
  have e1 := h1.eventually (gt_mem_nhds (half_pos hε))
  have e2 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨A0, hA0⟩ := eventually_atTop.1 (e1.and e2)
  refine ⟨max A0 (1 + n), fun τ hA hre hren => ?_⟩
  have hpos : 0 < τ.im := τ.im_pos
  have hy0 : A0 ≤ τ.im := le_trans (le_max_left _ _) hA
  have hyn : 1 + (n : ℝ) ≤ τ.im := le_trans (le_max_right _ _) hA
  have hy1 : 1 ≤ τ.im := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hf1, hf2⟩ := hA0 τ.im hy0
  have hz : ‖(τ : ℂ)‖ ≤ n + τ.im := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hr : |(τ : ℂ).re| ≤ n := by
      rw [UpperHalfPlane.coe_re, abs_of_nonneg hre]; exact hren
    have hi : |(τ : ℂ).im| = τ.im := by
      rw [UpperHalfPlane.coe_im, abs_of_pos hpos]
    linarith
  have hcb : ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
    intro j hj
    refine (hcoef τ hy1 j hj).trans ?_
    gcongr
    exact le_max_left _ _
  have hmem : V τ - C a ∈ degreeLT ℂ (w + 1) :=
    Submodule.sub_mem _ (hV τ)
      (mem_degreeLT.2 (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos w)))
  have hmain := norm_eval_add_C_le_of_coeff_le w a (τ : ℂ) (V τ - C a) K (Real.exp (-c * τ.im)) hK
    (Real.exp_pos _).le hmem hcb
  rw [sub_add_cancel] at hmain
  have hnz : 1 + ‖(τ : ℂ)‖ ≤ 2 * τ.im := by linarith
  have hpow : (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ 4 ^ w * τ.im ^ (2 * w) := by
    calc (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ (2 * τ.im) ^ (2 * w) :=
          pow_le_pow_left₀ (by positivity) hnz _
      _ = 4 ^ w * τ.im ^ (2 * w) := by rw [mul_pow, pow_mul]; norm_num
  have hT : (w + 1) * (K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
      ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
    rw [neg_mul, Real.exp_neg]
    calc (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
        ≤ (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (4 ^ w * τ.im ^ (2 * w))) := by gcongr
      _ = (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        rw [div_eq_mul_inv]; ring
  have hT0 : 0 ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by positivity
  have hr0 : 0 ≤ τ.im ^ (-(w : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  have hr1 : τ.im ^ (-(w : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hy1 ?_
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    linarith
  calc ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2)
      ≤ (‖a‖ + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)))
          * τ.im ^ (-(w : ℝ) / 2) := by gcongr; linarith
    _ = ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im))
            * τ.im ^ (-(w : ℝ) / 2) := by ring
    _ ≤ ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        exact add_le_add le_rfl (mul_le_of_le_one_right hT0 hr1)
    _ < ε / 2 + ε / 2 := add_lt_add hf1 hf2
    _ = ε := add_halves ε

end GlobalTheory.HeckeFamilyMatrices

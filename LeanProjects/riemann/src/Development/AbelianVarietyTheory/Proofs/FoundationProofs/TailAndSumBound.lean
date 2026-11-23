import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gl2L2IntegralityStatement

open Finset Filter Topology

namespace GlobalTheory.GoodCharacterTail

open Formalism.HermitianLattices.GL2PrimeSums

theorem tail_le (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (Z B : ℝ) (hZ : 1 ≤ Z)
    (hB : ∀ U : ℝ, Z ≤ U → ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2) ≤ B) :
    ‖S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)‖ ≤ B := by
  obtain ⟨I, hI, hG⟩ := GlobalTheory.TailIntegralOfSummatory.tail_integral a S hS Z hZ
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  have h1 : Gchi a S Z = Z * (∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)) - psum a Z - Z * S := by
    unfold Gchi psum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have h2 : S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ) = I - psum a Z / Z := by
    rw [h1] at hG
    field_simp
    linear_combination -hG
  have h3 : ‖I‖ ≤ B - ‖psum a Z‖ / Z := by
    refine le_of_tendsto hI.norm ?_
    filter_upwards [eventually_ge_atTop Z] with U hU
    have h4 := intervalIntegral.norm_integral_le_integral_norm
      (f := fun u : ℝ => psum a u / (u : ℂ) ^ 2) (μ := MeasureTheory.volume) hU
    have h5 : (fun u : ℝ => ‖psum a u / (u : ℂ) ^ 2‖) = fun u : ℝ => ‖psum a u‖ / u ^ 2 := by
      funext u
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h5] at h4
    have := hB U hU
    linarith
  rw [h2]
  have h6 := norm_sub_le I (psum a Z / Z)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ0] at h6
  linarith

theorem eventually_log_le (k δ : ℝ) (hk : 0 < k) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ k * x ^ δ := by
  have h := (isLittleO_log_rpow_atTop hδ).bound hk
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
  exact (le_abs_self _).trans hx

theorem tail_and_sum_bound : Formalism.HermitianLattices.GL2PrimeSums.TailSumBound := by
  intro ε hε hε1 C₁ c₁ CM hC₁ hc₁ hCM
  obtain ⟨C, c, hC, hc, hZ⟩ := GlobalTheory.T.gl2a2_integral_bound_of_sums C₁ c₁ hC₁ hc₁
  have e1 := eventually_log_le (1 / 400) (ε / 4) (by norm_num) (by linarith)
  have e2 := eventually_log_le c (ε / 6) hc (by linarith)
  have e3 := (tendsto_rpow_atTop (show 0 < ε / 2 by linarith)).eventually_ge_atTop (5 * C)
  have e4 := (tendsto_rpow_atTop (show 0 < ε / 6 by linarith)).eventually_ge_atTop 2
  have e5 := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e6 := eventually_ge_atTop (2 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨x₀, 400 + CM + 1, ?_⟩
  intro x hx Q hQ hQ1 hQ2 a S hS hM H1 H2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hQ3 : 3 ≤ Q := by
    have h := Real.add_one_le_exp (Real.log Q)
    rw [Real.exp_log hQ] at h
    linarith
  have hz2 : 2 ≤ x ^ (400 : ℝ) := by
    have : x ^ (1 : ℝ) ≤ x ^ (400 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hlz : Real.log (x ^ (400 : ℝ)) = 400 * Real.log x := Real.log_rpow hx0 _
  have ht := tail_le a S hS (x ^ (400 : ℝ)) _ (by linarith)
    (fun U hU => hZ Q a hQ3 H1 H2 _ U hz2 hU)
  have hp : (x ^ (400 : ℝ)) ^ (-(1 : ℝ) / 400) = x⁻¹ := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
    norm_num
  have hl : Real.log (x ^ (400 : ℝ) * Q) = 400 * Real.log x + Real.log Q := by
    rw [Real.log_mul (by positivity) hQ.ne', hlz]
  rw [hp, hl] at ht
  have hsq : x ^ (ε / 4) * x ^ (ε / 4) = x ^ (ε / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hsq2 : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hL : (400 * Real.log x + Real.log Q) ^ 2 ≤ 4 * x ^ (ε / 2) := by
    have a1 : 0 ≤ 400 * Real.log x + Real.log Q := by linarith
    have a2 : 400 * Real.log x + Real.log Q ≤ 2 * x ^ (ε / 4) := by linarith
    have := pow_le_pow_left₀ a1 a2 2
    nlinarith
  have hQc : x * Q ^ (-c) ≤ 1 := by
    rw [Real.rpow_def_of_pos hQ]
    nth_rewrite 1 [← Real.exp_log hx0]
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have := mul_le_mul_of_nonneg_left hQ1 hc.le
    linarith
  have h1e : 1 ≤ x ^ (ε / 2) := Real.one_le_rpow hx1 (by linarith)
  have key : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x ^ ε := by
    have b1 := mul_le_mul_of_nonneg_left ht hx0.le
    have b2 : x * (C * (x⁻¹ * (400 * Real.log x + Real.log Q) ^ 2 + Q ^ (-c))) =
        C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) := by
      field_simp
    rw [b2] at b1
    have b3 : C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) ≤ C * (5 * x ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    have b4 : 5 * C * x ^ (ε / 2) ≤ x ^ (ε / 2) * x ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right f3 (by linarith)
    linarith
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact key
  · have c1 : x ^ ε ≤ x := by
      have : x ^ ε ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hε1.le
      rwa [Real.rpow_one] at this
    have c2 : ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 1 := by
      have : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x * 1 := by linarith
      exact le_of_mul_le_mul_left this hx0
    have c3 : ‖∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 400 * Real.log x + CM := by
      rw [← hlz]
      refine le_trans ((norm_sum_le _ _).trans (le_of_eq ?_)) (hM _ (by linarith))
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_div, Complex.norm_natCast]
    have c4 := norm_add_le (S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
      (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
    rw [sub_add_cancel] at c4
    nlinarith

end GlobalTheory.GoodCharacterTail

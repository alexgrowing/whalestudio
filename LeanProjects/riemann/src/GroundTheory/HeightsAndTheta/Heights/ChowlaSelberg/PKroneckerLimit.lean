import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.KroneckerSplitStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PowerIntegralStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.ShiftedSumIntegralStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.CotangentSumStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LogEtaStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.GammaZetaLimitStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology Set
open scoped Real UpperHalfPlane ModularForm

noncomputable section

theorem kroneckerLimit_rpow_neg_le {X s : ℝ} (hX : 0 < X) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    X ^ (-s) ≤ X ^ (-1 : ℝ) + X ^ (-2 : ℝ) := by
  rcases le_total 1 X with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (show -s ≤ -1 by linarith)
    have := Real.rpow_nonneg hX.le (-2 : ℝ)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hX h (show (-2 : ℝ) ≤ -s by linarith)
    have := Real.rpow_nonneg hX.le (-1 : ℝ)
    linarith

theorem kroneckerLimit_tendsto_shiftedSum (hT : ShiftedSumIntegral.Statement) {a : ℝ} (ha : 0 < a)
    (u : ℝ) :
    Tendsto (fun s : ℝ ↦ ∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s)) (𝓝[>] 1)
      (𝓝 (∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ))) := by
  have hX : ∀ n : ℤ, 0 < ((n : ℝ) + u) ^ 2 + a ^ 2 := fun n ↦ by positivity
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℤ ↦ (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) +
      (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-2 : ℝ))
    ((hT a u 1 ha (by norm_num)).1.add (hT a u 2 ha (by norm_num)).1) (fun n ↦ ?_) ?_
  · have : ContinuousAt (fun s : ℝ ↦ (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s)) 1 :=
      continuousAt_const.rpow continuousAt_neg (Or.inl (hX n).ne')
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs n
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hX n).le _)]
    exact kroneckerLimit_rpow_neg_le (hX n) hs.1.le hs.2.le

theorem kroneckerLimit_tendsto_zeta_two :
    Tendsto (fun s : ℝ ↦ ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s))) (𝓝[>] 1) (𝓝 (π ^ 2 / 6)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n ↦ by positivity
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ (2 : ℝ))) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (show (1 : ℝ) < 2 by norm_num))
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hval : ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * 1 : ℝ)) = π ^ 2 / 6 := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, sub_zero] at h
    rw [← h.tsum_eq]
    refine tsum_congr fun n ↦ ?_
    rw [mul_one, Real.rpow_two]
    push_cast
    ring
  rw [← hval]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ (2 : ℝ)))
    hsum (fun n ↦ ?_) ?_
  · have : ContinuousAt (fun s : ℝ ↦ 1 / ((n + 1 : ℝ) ^ (2 * s))) 1 :=
      continuousAt_const.div
        (continuousAt_const.rpow (continuousAt_const.mul continuousAt_id) (Or.inl (hpos n).ne'))
        (Real.rpow_pos_of_pos (hpos n) _).ne'
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) n
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := Real.rpow_pos_of_pos (hpos n) (2 * s); positivity)]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hpos n) _)
      (Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        (by linarith))

theorem kroneckerLimit_tendsto_gammaRatio :
    Tendsto (fun s : ℝ ↦ √π * Real.Gamma (s - 1 / 2) / Real.Gamma s) (𝓝[>] 1) (𝓝 π) := by
  have hG12 : ContinuousAt Real.Gamma (1 - 1 / 2) :=
    (Real.differentiableAt_Gamma fun m h ↦ by
      have := (m.cast_nonneg : (0 : ℝ) ≤ m); linarith).continuousAt
  have hG1 : ContinuousAt Real.Gamma 1 :=
    (Real.differentiableAt_Gamma fun m h ↦ by
      have := (m.cast_nonneg : (0 : ℝ) ≤ m); linarith).continuousAt
  have hnum : ContinuousAt (fun s : ℝ ↦ √π * Real.Gamma (s - 1 / 2)) 1 :=
    continuousAt_const.mul (hG12.comp_of_eq (continuousAt_id.sub continuousAt_const) rfl)
  have hcont : ContinuousAt (fun s : ℝ ↦ √π * Real.Gamma (s - 1 / 2) / Real.Gamma s) 1 :=
    hnum.div hG1 (by rw [Real.Gamma_one]; norm_num)
  have hval : √π * Real.Gamma (1 - 1 / 2) / Real.Gamma 1 = π := by
    rw [Real.Gamma_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq, div_one,
      Real.mul_self_sqrt Real.pi_pos.le]
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
  beta_reduce at h
  rwa [hval] at h

theorem kroneckerLimit_term_bound (hI : PowerIntegral.Statement) (hT : ShiftedSumIntegral.Statement)
    {y : ℝ} (hy : 0 < y) (x : ℝ) (m : ℕ) {s : ℝ} (h1 : 1 < s) (h2 : s < 2) :
    ‖y ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * x) ^ 2 + ((m + 1) * y) ^ 2) ^ (-s)) -
        √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * ((m + 1) * y) ^ (1 - 2 * s))‖ ≤
      (y ^ (-1 : ℝ) + y ^ (-2 : ℝ)) * ((m : ℝ) + 1) ^ (-2 : ℝ) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hA : 0 < ((m : ℝ) + 1) * y := by positivity
  have hb := (hT _ ((m + 1) * x) s hA (by linarith)).2
  rw [hI _ s hA (by linarith)] at hb
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy s)]
  calc y ^ s * |_| ≤ y ^ s * (((m : ℝ) + 1) * y) ^ (-2 * s) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy.le _)
    _ = ((m : ℝ) + 1) ^ (-2 * s) * y ^ (-s) := by
        rw [Real.mul_rpow hm.le hy.le, show -s = s + -2 * s by ring, Real.rpow_add hy]; ring
    _ ≤ ((m : ℝ) + 1) ^ (-2 : ℝ) * (y ^ (-1 : ℝ) + y ^ (-2 : ℝ)) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le
            (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]) (by linarith))
          (kroneckerLimit_rpow_neg_le hy h1.le h2.le)
          (Real.rpow_nonneg hy.le _)
          (Real.rpow_nonneg hm.le _)
    _ = _ := by ring

theorem kroneckerLimit_main_term {y : ℝ} (hy : 0 < y) (c s : ℝ) (m : ℕ) :
    y ^ s * (c * (((m : ℝ) + 1) * y) ^ (1 - 2 * s)) =
      c * y ^ (1 - s) * (1 / (((m : ℝ) + 1) ^ (2 * s - 1))) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [Real.mul_rpow hm.le hy.le, show (1 - 2 * s) = -(2 * s - 1) by ring, Real.rpow_neg hm.le,
    show (1 - s) = s + -(2 * s - 1) by ring, Real.rpow_add hy]
  ring

theorem KroneckerLimit.proof (hS : KroneckerSplit.Statement) (hI : PowerIntegral.Statement)
    (hT : ShiftedSumIntegral.Statement) (hC : CotangentSum.Statement) (hE : LogEta.Statement)
    (hG : GammaZetaLimit.Statement) : KroneckerLimit.Statement := by
  intro τ
  have hy : 0 < τ.im := τ.im_pos
  have hA : ∀ m : ℕ, 0 < ((m : ℝ) + 1) * τ.im := fun m ↦ by positivity
  have hsum2 : Summable (fun m : ℕ ↦
      (τ.im ^ (-1 : ℝ) + τ.im ^ (-2 : ℝ)) * ((m : ℝ) + 1) ^ (-2 : ℝ)) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num))
    exact (by simpa [Nat.cast_add, Nat.cast_one] using this :
      Summable (fun m : ℕ ↦ ((m : ℝ) + 1) ^ (-2 : ℝ))).mul_left _
  have hys : Tendsto (fun s : ℝ ↦ τ.im ^ s) (𝓝[>] 1) (𝓝 τ.im) := by
    have := ((Real.continuousAt_const_rpow (b := 1) hy.ne').tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simpa using this

  have hD : Tendsto (fun s : ℝ ↦ ∑' m : ℕ, τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) -
          √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * ((m + 1) * τ.im) ^ (1 - 2 * s)))
      (𝓝[>] 1) (𝓝 (∑' m : ℕ, τ.im * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-1 : ℝ)) - π * ((m + 1) * τ.im) ^ (-1 : ℝ)))) := by
    refine tendsto_tsum_of_dominated_convergence hsum2 (fun m ↦ ?_) ?_
    · have h2 : Tendsto (fun s : ℝ ↦ (((m : ℝ) + 1) * τ.im) ^ (1 - 2 * s)) (𝓝[>] 1)
          (𝓝 ((((m : ℝ) + 1) * τ.im) ^ (-1 : ℝ))) := by
        have : ContinuousAt (fun s : ℝ ↦ (((m : ℝ) + 1) * τ.im) ^ (1 - 2 * s)) 1 :=
          continuousAt_const.rpow (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
            (Or.inl (hA m).ne')
        have h := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
        beta_reduce at h
        rwa [show (1 : ℝ) - 2 * 1 = -1 by norm_num] at h
      exact hys.mul ((kroneckerLimit_tendsto_shiftedSum hT (hA m) _).sub
        (kroneckerLimit_tendsto_gammaRatio.mul h2))
    · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs m
      exact kroneckerLimit_term_bound hI hT hy τ.re m hs.1 hs.2

  have hEq : ∀ s : ℝ, 1 < s → s < 2 →
      kroneckerSum τ s - π / (s - 1) =
        2 * τ.im ^ s * (∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s))) +
        2 * (∑' m : ℕ, τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) -
          √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * ((m + 1) * τ.im) ^ (1 - 2 * s))) +
        (2 * (√π * Real.Gamma (s - 1 / 2) / Real.Gamma s) * τ.im ^ (1 - s) *
          (∑' m : ℕ, 1 / ((m + 1 : ℝ) ^ (2 * s - 1))) - π / (s - 1)) := by
    intro s h1 h2
    set c := √π * Real.Gamma (s - 1 / 2) / Real.Gamma s with hc
    have hDs : Summable (fun m : ℕ ↦ τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) - c * ((m + 1) * τ.im) ^ (1 - 2 * s))) :=
      Summable.of_norm_bounded hsum2 (fun m ↦ kroneckerLimit_term_bound hI hT hy τ.re m h1 h2)
    have hM : ∑' m : ℕ, τ.im ^ s * (c * ((m + 1) * τ.im) ^ (1 - 2 * s)) =
        c * τ.im ^ (1 - s) * ∑' m : ℕ, 1 / ((m + 1 : ℝ) ^ (2 * s - 1)) := by
      simp_rw [kroneckerLimit_main_term hy]
      exact tsum_mul_left
    have hMs : Summable (fun m : ℕ ↦ τ.im ^ s * (c * ((m + 1) * τ.im) ^ (1 - 2 * s))) := by
      simp_rw [kroneckerLimit_main_term hy]
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_rpow.mpr (show 1 < 2 * s - 1 by linarith))
      simpa [Nat.cast_add, Nat.cast_one] using this
    have hsplit : ∑' m : ℕ, τ.im ^ s * (∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) =
        (∑' m : ℕ, τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) - c * ((m + 1) * τ.im) ^ (1 - 2 * s))) +
        ∑' m : ℕ, τ.im ^ s * (c * ((m + 1) * τ.im) ^ (1 - 2 * s)) := by
      rw [← hDs.tsum_add hMs]
      exact tsum_congr fun m ↦ by ring
    rw [hS τ s h1, hsplit, hM]
    ring

  have hD' : ∑' m : ℕ, τ.im * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-1 : ℝ)) - π * ((m + 1) * τ.im) ^ (-1 : ℝ)) =
      2 * π * (-(π * τ.im / 12) - Real.log ‖η (τ : ℂ)‖) := by
    rw [← (hE τ).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun m ↦ ?_
    rw [hC _ _ (hA m)]
    have hq : Complex.exp (2 * π * Complex.I *
        ((((m + 1) * τ.re : ℝ) : ℂ) + (((m + 1) * τ.im : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (2 * π * Complex.I * (τ : ℂ)) ^ (m + 1) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      conv_rhs => rw [← Complex.re_add_im (τ : ℂ)]
      push_cast
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [hq]
    simp_rw [← pow_mul]
    rw [Real.rpow_neg_one]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    have := hy.ne'
    field_simp
    ring
  have hη : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hval : 2 * τ.im * (π ^ 2 / 6) +
      2 * (∑' m : ℕ, τ.im * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-1 : ℝ)) - π * ((m + 1) * τ.im) ^ (-1 : ℝ))) +
      (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log τ.im) =
      2 * π * (Real.eulerMascheroniConstant - Real.log 2 -
        Real.log (Real.sqrt τ.im * ‖η (τ : ℂ)‖ ^ 2)) := by
    rw [hD', Real.log_mul (Real.sqrt_pos.mpr hy).ne' (pow_pos (norm_pos_iff.mpr hη) 2).ne',
      Real.log_sqrt hy.le, Real.log_pow]
    push_cast
    ring
  rw [← hval]
  refine Tendsto.congr' ?_ (((((tendsto_const_nhds (x := (2 : ℝ))).mul hys).mul
    kroneckerLimit_tendsto_zeta_two).add (tendsto_const_nhds.mul hD)).add (hG τ.im hy))
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs
  exact (hEq s hs.1 hs.2).symm

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg

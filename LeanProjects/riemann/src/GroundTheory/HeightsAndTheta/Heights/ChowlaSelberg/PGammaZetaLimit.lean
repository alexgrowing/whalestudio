import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.GammaZetaLimitStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real

noncomputable section

theorem tendsto_tsum_one_div_rpow_sub_one_div :
    Tendsto (fun w : ℝ ↦ (∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ w)) - 1 / (w - 1)) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
  have h := (Complex.continuous_re.tendsto _).comp
    ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : (1 : ℝ) < w := hw
  simp only [Function.comp_apply]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hw')]
  have : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (w : ℂ)) = ((∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ w) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1 with n
    rw [Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring
  rw [this]
  have h1 : ((1 : ℂ) / ((w : ℂ) - 1)) = (((1 : ℝ) / (w - 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_sub, Complex.ofReal_re]

theorem GammaZetaLimit.proof : GammaZetaLimit.Statement := by
  intro y hy
  set F : ℝ → ℝ := fun s ↦ √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * y ^ (1 - s) with hF
  have hs2 : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have h12 : Real.Gamma (1 - 1 / 2) = √π := by norm_num [Real.Gamma_one_half_eq]

  have hG12 : HasDerivAt (fun s : ℝ ↦ Real.Gamma (s - 1 / 2))
      (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2)) 1 := by
    have h : HasDerivAt Real.Gamma (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2))
        ((1 : ℝ) - 1 / 2) := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      exact Real.hasDerivAt_Gamma_one_half
    exact h.comp_sub_const 1 (1 / 2)
  have hY : HasDerivAt (fun s : ℝ ↦ y ^ (1 - s)) (-Real.log y) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 1).const_rpow hy
  have hΓ1 : Real.Gamma 1 ≠ 0 := by simp
  have hFd : HasDerivAt F (-2 * π * Real.log 2 - π * Real.log y) 1 := by
    have h := ((hG12.div Real.hasDerivAt_Gamma_one hΓ1).const_mul √π).mul hY
    have e1 : ((fun t : ℝ ↦ √π * ((fun s : ℝ ↦ Real.Gamma (s - 1 / 2)) / Real.Gamma) t) *
        fun s : ℝ ↦ y ^ (1 - s)) = F := by
      funext s
      simp only [hF, Pi.mul_apply, Pi.div_apply]
      ring
    rw [e1] at h
    refine h.congr_deriv ?_
    simp only [h12, Real.Gamma_one, Pi.div_apply, one_pow, div_one, mul_one, sub_self,
      Real.rpow_zero]
    linear_combination (-(2 * Real.log 2 + Real.log y)) * hs2
  have hF1 : F 1 = π := by
    simp only [hF, h12, Real.Gamma_one, sub_self, Real.rpow_zero, div_one, mul_one]
    exact hs2

  have hslope : Tendsto (fun s ↦ (F s - π) / (s - 1)) (𝓝[>] 1)
      (𝓝 (-2 * π * Real.log 2 - π * Real.log y)) := by
    have := (hasDerivAt_iff_tendsto_slope.mp hFd).mono_left
      (nhdsWithin_mono _ (fun x (hx : (1 : ℝ) < x) ↦ hx.ne'))
    refine this.congr' (Eventually.of_forall fun s ↦ ?_)
    rw [slope_def_field, hF1]
  have hFc : Tendsto F (𝓝[>] 1) (𝓝 π) :=
    hF1 ▸ hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝 1) (𝓝 (2 * 1 - 1)) :=
        ((continuous_const.mul continuous_id).sub continuous_const).tendsto 1
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : (1 : ℝ) < s)
      show (1 : ℝ) < 2 * s - 1
      linarith
  have hZ := tendsto_tsum_one_div_rpow_sub_one_div.comp hmap
  have hlim := hslope.add ((hFc.const_mul 2).mul hZ)
  have hval : -2 * π * Real.log 2 - π * Real.log y + 2 * π * Real.eulerMascheroniConstant =
      2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : (1 : ℝ) < s)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  have key : ∀ A Z : ℝ, (A - π) / (s - 1) + 2 * A * (Z - 1 / (2 * s - 1 - 1)) =
      2 * A * Z - π / (s - 1) := by
    intro A Z
    rw [show 2 * s - 1 - 1 = 2 * (s - 1) by ring]
    field_simp
    ring
  simp only [Function.comp_apply]
  rw [key]
  simp only [hF]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg

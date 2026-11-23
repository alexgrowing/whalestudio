import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

open Filter Topology

namespace GlobalTheory.CompanionTheory.RankinSelberg

theorem eq_of_punctured {f g : ℂ → ℂ} {a : ℂ} (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h : f =ᶠ[𝓝[≠] a] g) : f a = g a :=
  tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) h

theorem differentiable_euler_two : Differentiable ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) := by
  intro s
  have h : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl two_ne_zero)
  exact (differentiableAt_const _).sub h

theorem dslope_euler_two_ne_zero : dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 1 ≠ 0 := by
  have hd : HasDerivAt (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s))
      (-((2 : ℂ) ^ ((1 : ℂ) - 1) * Complex.log 2 * (-1))) 1 := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).const_sub 1
    exact (h1.const_cpow (Or.inl two_ne_zero)).const_sub 1
  have hlog : Complex.log 2 ≠ 0 := by
    have h2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; simp
    rw [h2]
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [dslope_same, hd.deriv]
  simpa using hlog

theorem x1a : Ad3.R.HalfPlaneAnalyticIdentities := by
  intro E Λ L Z P Q hE hΛ hL hZ hid
  have hUo : IsOpen {s : ℂ | 1 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected {s : ℂ | 1 / 4 < s.re} :=
    (convex_halfSpace_re_gt (1 / 4)).isPreconnected
  have hsub : {s : ℂ | 1 / 4 < s.re} ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have h : (1 / 4 : ℝ) < s.re := hs
    show 0 < s.re
    linarith
  have hH := differentiable_euler_two
  have hf : DifferentiableOn ℂ (fun s : ℂ => (s - 1) ^ 2 * E s) {s : ℂ | 1 / 4 < s.re} :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => (s - 1) ^ 2).differentiableOn.mul (hE.mono hsub)
  have hg : DifferentiableOn ℂ (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * Z s * Λ s * L s)
      {s : ℂ | 1 / 4 < s.re} :=
    ((hH.differentiableOn.mul (hZ.mono hsub)).mul hΛ).mul hL.differentiableOn
  have hev : (fun s : ℂ => (s - 1) ^ 2 * E s) =ᶠ[𝓝 (2 : ℂ)]
      fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * Z s * Λ s * L s := by
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with s hs
    obtain ⟨h1, h2, h3⟩ := hid s hs
    rw [h1, h2, h3]
    ring
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 4 < s.re} := by
    show (1 / 4 : ℝ) < (2 : ℂ).re
    norm_num
  have heq := (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hUo) hUc h2U hev
  refine ⟨fun s hs => heq hs, ?_⟩
  intro hZ1
  have h1U : (1 : ℂ) ∈ {s : ℂ | 1 / 4 < s.re} := by
    show (1 / 4 : ℝ) < (1 : ℂ).re
    norm_num
  have hUn : {s : ℂ | 1 / 4 < s.re} ∈ 𝓝 (1 : ℂ) := hUo.mem_nhds h1U
  have hEc : ContinuousAt E 1 :=
    (hE.differentiableAt (mem_of_superset hUn hsub)).continuousAt
  have hZc : ContinuousAt Z 1 :=
    (hZ.differentiableAt (mem_of_superset hUn hsub)).continuousAt
  have hΛc : ContinuousAt Λ 1 := (hΛ.differentiableAt hUn).continuousAt
  have hLc : ContinuousAt L 1 := (hL 1).continuousAt
  have hgc : ContinuousAt (dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1) 1 :=
    continuousAt_dslope_same.2 (hH 1)
  have hg1 := dslope_euler_two_ne_zero
  have hfac : ∀ s : ℂ, 1 - (2 : ℂ) ^ (1 - s) =
      (s - 1) * dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s := by
    intro s
    have h := sub_smul_dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s
    simp only [smul_eq_mul, sub_self, Complex.cpow_zero] at h
    rw [h]
    ring

  have hpunct : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 1 ∧ (s - 1) * E s =
      dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s * Z s * Λ s * L s := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hUn] with s hs hsU
    refine ⟨hs, ?_⟩
    have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs
    have h := heq hsU
    simp only at h
    rw [hfac s] at h
    apply mul_left_cancel₀ hne
    linear_combination h
  constructor
  · intro hL1
    have h := eq_of_punctured (f := fun s : ℂ => (s - 1) * E s)
      (g := fun s : ℂ => dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s * Z s * Λ s * L s)
      ((by fun_prop : ContinuousAt (fun s : ℂ => s - 1) 1).mul hEc)
      (((hgc.mul hZc).mul hΛc).mul hLc) (hpunct.mono fun s hs => hs.2)
    have h' : dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 1 * Z 1 * Λ 1 * L 1 = 0 :=
      h.symm.trans (by simp)
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hL1)).resolve_left
      (mul_ne_zero hg1 hZ1)
  · intro hL1 hdL hE1
    have hLfac : ∀ s : ℂ, L s = (s - 1) * dslope L 1 s := by
      intro s
      have h := sub_smul_dslope L 1 s
      simp only [smul_eq_mul, hL1, sub_zero] at h
      exact h.symm
    have hlc : ContinuousAt (dslope L 1) 1 := continuousAt_dslope_same.2 (hL 1)
    have hl1 : dslope L 1 1 ≠ 0 := by rwa [dslope_same]
    have h := eq_of_punctured (f := E)
      (g := fun s : ℂ => dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s * Z s * Λ s * dslope L 1 s)
      hEc (((hgc.mul hZc).mul hΛc).mul hlc) (hpunct.mono fun s hs => by
        have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs.1
        have h2 := hs.2
        rw [hLfac s] at h2
        apply mul_left_cancel₀ hne
        linear_combination h2)
    have h' : dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 1 * Z 1 * Λ 1 * dslope L 1 1 = 0 :=
      h.symm.trans hE1
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hl1)).resolve_left
      (mul_ne_zero hg1 hZ1)

end GlobalTheory.CompanionTheory.RankinSelberg

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
open scoped ContDiff
open Complex Filter Topology ComplexConjugate

namespace GlobalTheory

theorem re_leviForm_apply_smul_self (u : ℂ → ℝ) (z a : ℂ) :
    (leviForm u z a a).re = Complex.normSq a * (leviForm u z 1 1).re := by
  have : a = a • (1:ℂ) := by simp
  rw [this]
  simp only [map_smul, map_smulₛₗ, ContinuousLinearMap.smul_apply]
  simp [smul_eq_mul, Complex.mul_re, Complex.normSq_apply]
  ring

theorem del_mul_dbar_re_one (ζ : ℂ) :
    del (fun x : ℂ => (x.re : ℂ)) ζ 1 * dbar (fun x : ℂ => (x.re : ℂ)) ζ 1 = 1 / 4 := by
  have h : HasFDerivAt (fun x : ℂ => (x.re : ℂ)) (ofRealCLM.comp reCLM) ζ :=
    (ofRealCLM.comp reCLM).hasFDerivAt
  rw [del_apply, dbar_apply, h.fderiv]
  simp; ring

theorem deriv_deriv_comp_exp_ge (g : ℝ → ℝ) (δ c : ℝ) (hδ : 0 < δ)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 δ))
    (hL : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → -c ≤ (GlobalTheory.leviForm (fun z : ℂ => g ‖z‖) w 1 1).re)
    (s : ℝ) (hs : s < Real.log δ) :
    -(4 * c * Real.exp s ^ 2) ≤ deriv (deriv (fun r => g (Real.exp r))) s := by
  have hes : Real.exp s < δ := by
    rw [← Real.exp_log hδ]; exact Real.exp_lt_exp.mpr hs
  have hep := Real.exp_pos s
  have hgA : ContDiffAt ℝ 2 g (Real.exp s) := hg.contDiffAt (isOpen_Ioo.mem_nhds ⟨hep, hes⟩)
  set ζ : ℂ := (s : ℂ)
  have hnorm : ‖Complex.exp ζ‖ = Real.exp s := by simp [ζ, Complex.norm_exp]
  have hu : ContDiffAt ℝ 2 (fun z : ℂ => g ‖z‖) (Complex.exp ζ) := by
    have hne : Complex.exp ζ ≠ 0 := Complex.exp_ne_zero _
    have : ContDiffAt ℝ 2 g ‖Complex.exp ζ‖ := by rw [hnorm]; exact hgA
    exact this.comp _ (contDiffAt_norm ℝ hne)
  have hφ : ContDiffAt ℂ 2 Complex.exp ζ := Complex.contDiff_exp.contDiffAt
  have L1 := leviForm_comp_holo hu hφ 1 1
  have hfd : fderiv ℂ Complex.exp ζ 1 = Complex.exp ζ := by
    rw [(Complex.hasDerivAt_exp _).hasFDerivAt.fderiv]; simp
  rw [hfd] at L1
  have hfun : (fun x : ℂ => g ‖Complex.exp x‖) = fun x : ℂ => (fun r => g (Real.exp r)) x.re := by
    funext x; simp [Complex.norm_exp]
  rw [hfun] at L1
  have hk : ContDiffAt ℝ 2 (fun r => g (Real.exp r)) ((fun x : ℂ => x.re) ζ) := by
    show ContDiffAt ℝ 2 (fun r => g (Real.exp r)) s
    exact hgA.comp s Real.contDiff_exp.contDiffAt
  have hre : ContDiffAt ℝ 2 (fun x : ℂ => x.re) ζ := reCLM.contDiff.contDiffAt
  have L2 := leviForm_real_comp hk hre 1 1
  rw [leviForm_re_eq_zero (f := fun x : ℂ => x) contDiffAt_id, del_mul_dbar_re_one] at L2
  have hζre : ζ.re = s := by simp [ζ]
  rw [hζre, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, mul_zero, zero_add] at L2
  have key := congrArg Complex.re (L1.symm.trans L2)
  rw [re_leviForm_apply_smul_self] at key
  simp at key
  have hL' := hL (Complex.exp ζ) (by rw [hnorm]; exact hep) (by rw [hnorm]; exact hes)
  have hns : Complex.normSq (Complex.exp ζ) = Real.exp s ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
  rw [hns] at key
  nlinarith [sq_nonneg (Real.exp s), mul_le_mul_of_nonneg_left hL' (sq_nonneg (Real.exp s))]

end GlobalTheory

namespace GlobalTheory

theorem slope_le_of_leviForm_radial_ge (g : ℝ → ℝ) (δ c : ℝ) (hδ : 0 < δ)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 δ))
    (hL : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → -c ≤ (GlobalTheory.leviForm (fun z : ℂ => g ‖z‖) w 1 1).re)
    (t t₁ : ℝ) (ht : 0 < t) (htt : t < t₁) (ht₁ : t₁ < δ) :
    t * deriv g t + 2 * c * t ^ 2 ≤ (g t₁ + c * t₁ ^ 2 - (g t + c * t ^ 2)) / Real.log (t₁ / t) := by
  set k : ℝ → ℝ := fun r => g (Real.exp r) with hkdef
  set U : Set ℝ := Set.Iio (Real.log δ)
  have hexpU : ∀ s ∈ U, Real.exp s ∈ Set.Ioo 0 δ := fun s hs =>
    ⟨Real.exp_pos s, by rw [← Real.exp_log hδ]; exact Real.exp_lt_exp.mpr hs⟩
  have hkC : ∀ s ∈ U, ContDiffAt ℝ 2 k s := fun s hs =>
    (hg.contDiffAt (isOpen_Ioo.mem_nhds (hexpU s hs))).comp s Real.contDiff_exp.contDiffAt
  have hkD : ∀ s ∈ U, DifferentiableAt ℝ (deriv k) s := by
    intro s hs
    have := (((hkC s hs).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const (1 : ℝ))
    simpa only [fderiv_apply_one_eq_deriv] using this
  set D : ℝ → ℝ := fun s => deriv k s + 2 * c * Real.exp s ^ 2 with hDdef
  set m : ℝ → ℝ := fun s => k s + c * Real.exp s ^ 2 with hmdef
  have hm : ∀ s ∈ U, HasDerivAt m (D s) s := by
    intro s hs
    have h1 : HasDerivAt k (deriv k s) s :=
      ((hkC s hs).differentiableAt two_ne_zero).hasDerivAt
    have h2 : HasDerivAt (fun s => c * Real.exp s ^ 2) (2 * c * Real.exp s ^ 2) s := by
      have := ((Real.hasDerivAt_exp s).mul (Real.hasDerivAt_exp s)).const_mul c
      have e : (fun s => c * Real.exp s ^ 2) = fun y => c * (Real.exp y * Real.exp y) := by
        funext y; ring
      rw [e]; exact this.congr_deriv (by ring)
    exact h1.add h2
  have hDd : ∀ s ∈ U, HasDerivAt D (deriv (deriv k) s + 4 * c * Real.exp s ^ 2) s := by
    intro s hs
    have h1 : HasDerivAt (deriv k) (deriv (deriv k) s) s := (hkD s hs).hasDerivAt
    have h2 : HasDerivAt (fun s => 2 * c * Real.exp s ^ 2) (4 * c * Real.exp s ^ 2) s := by
      have := ((Real.hasDerivAt_exp s).mul (Real.hasDerivAt_exp s)).const_mul (2 * c)
      have e : (fun s => 2 * c * Real.exp s ^ 2) = fun y => 2 * c * (Real.exp y * Real.exp y) := by
        funext y; ring
      rw [e]; exact this.congr_deriv (by ring)
    exact h1.add h2
  have hUo : IsOpen U := isOpen_Iio
  have hDmono : MonotoneOn D U := by
    apply monotoneOn_of_deriv_nonneg (convex_Iio _)
    · exact fun s hs => (hDd s hs).continuousAt.continuousWithinAt
    · rw [hUo.interior_eq]; exact fun s hs => (hDd s hs).differentiableAt.differentiableWithinAt
    · rw [hUo.interior_eq]
      intro s hs
      rw [(hDd s hs).deriv]
      have := deriv_deriv_comp_exp_ge g δ c hδ hg hL s hs
      linarith
  set a := Real.log t
  set b := Real.log t₁
  have hab : a < b := Real.log_lt_log ht htt
  have hbU : b ∈ U := Real.log_lt_log (ht.trans htt) ht₁
  have hIcc : Set.Icc a b ⊆ U := fun x hx => lt_of_le_of_lt hx.2 hbU
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope m hab
    (fun x hx => (hm x (hIcc hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hm x (hIcc (Set.Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
  rw [(hm ξ (hIcc (Set.Ioo_subset_Icc_self hξ))).deriv] at hξeq
  have haU : a ∈ U := hIcc ⟨le_rfl, hab.le⟩
  have hDa : D a ≤ D ξ := hDmono haU (hIcc (Set.Ioo_subset_Icc_self hξ)) hξ.1.le
  have hka : deriv k a = deriv g t * t := by
    have hgA : DifferentiableAt ℝ g (Real.exp a) :=
      (hg.contDiffAt (isOpen_Ioo.mem_nhds (hexpU a haU))).differentiableAt two_ne_zero
    have := hgA.hasDerivAt.comp a (Real.hasDerivAt_exp a)
    have hk' : HasDerivAt k (deriv g (Real.exp a) * Real.exp a) a := this
    rw [hk'.deriv, Real.exp_log ht]
  have hDa' : D a = t * deriv g t + 2 * c * t ^ 2 := by
    simp only [hDdef, hka, a, Real.exp_log ht]; ring
  have hma : m a = g t + c * t ^ 2 := by simp [hmdef, hkdef, a, Real.exp_log ht]
  have hmb : m b = g t₁ + c * t₁ ^ 2 := by simp [hmdef, hkdef, b, Real.exp_log (ht.trans htt)]
  have hlog : Real.log (t₁ / t) = b - a := Real.log_div (ht.trans htt).ne' ht.ne'
  rw [← hDa', ← hma, ← hmb, hlog, ← hξeq]
  exact hDa

end GlobalTheory

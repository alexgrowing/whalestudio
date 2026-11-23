import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

noncomputable section

namespace GlobalTheory.CompanionTheory.DInt2.Drho

def pr (i j : Fin 2) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

theorem pr_apply (i j : Fin 2) (h : M22) : pr i j h = (h i j : ℂ) := rfl

def eps (d : Fin 2) : ℂ := if d = 0 then 1 else Complex.I

theorem norm_eps (d : Fin 2) : ‖eps d‖ = 1 := by
  unfold eps
  split_ifs <;> simp

def alC : M22 →L[ℝ] ℂ := pr 0 0 + Complex.I • pr 1 0

theorem alC_apply (h : M22) : alC h = al h := by
  simp [alC, al, pr_apply, mul_comm]

def rC (c d : Fin 2) : M22 →L[ℝ] ℂ := eps d • pr c 0

theorem al_rpol (c d : Fin 2) (h : M22) : al (rpol c d h) = eps d * (h c 0 : ℂ) := by
  fin_cases d <;> simp [al, rpol, eps, mul_comm]

theorem rC_apply (c d : Fin 2) (h : M22) : rC c d h = al (rpol c d h) := by
  simp [rC, al_rpol, pr_apply]

theorem norm_entry_le (a : Fin 2) (h : M22) : ‖((h a 0 : ℝ) : ℂ)‖ ≤ ‖al h‖ := by
  have h1 : (al h).re = h 0 0 := by simp [al]
  have h2 : (al h).im = h 1 0 := by simp [al]
  fin_cases a
  · simpa [h1] using Complex.abs_re_le_norm (al h)
  · simpa [h2] using Complex.abs_im_le_norm (al h)

theorem norm_al_rpol_le (c d : Fin 2) (h : M22) : ‖al (rpol c d h)‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul, norm_eps, one_mul]
  exact norm_entry_le c h

theorem norm_al_rpol_rpol_le (a b c d : Fin 2) (h : M22) :
    ‖al (rpol c d (rpol a b h))‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul, norm_eps, one_mul]
  by_cases hcb : c = b
  · have : rpol a b h c 0 = h a 0 := by simp [rpol, hcb]
    rw [this]
    exact norm_entry_le a h
  · have : rpol a b h c 0 = 0 := by simp [rpol, hcb]
    rw [this]
    simp

theorem al_ne (h : M22) (hΔ : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ

theorem hasFDerivAt_quot {f g : M22 → ℂ} {f' g' : M22 →L[ℝ] ℂ} {h : M22}
    (hf : HasFDerivAt f f' h) (hg : HasFDerivAt g g' h) (h0 : g h ≠ 0) :
    HasFDerivAt (fun x => f x / g x) ((g h)⁻¹ • f' + (f h * (-(g h ^ 2)⁻¹)) • g') h := by
  have hi : HasFDerivAt (fun x => (g x)⁻¹) ((-(g h ^ 2)⁻¹) • g') h :=
    (hasDerivAt_inv h0).comp_hasFDerivAt h hg
  simp only [div_eq_mul_inv]
  refine (hf.fun_mul hi).congr_fderiv ?_
  ext X
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_rho (c d : Fin 2) (h : M22) (h0 : al h ≠ 0) :
    HasFDerivAt (rho c d)
      ((al h)⁻¹ • rC c d + (al (rpol c d h) * (-(al h ^ 2)⁻¹)) • alC) h := by
  have e : rho c d = fun x => rC c d x / alC x := by
    funext x
    rw [rC_apply, alC_apply, rho]
  rw [e]
  have := hasFDerivAt_quot (rC c d).hasFDerivAt alC.hasFDerivAt
    (h := h) (by rwa [alC_apply])
  simpa only [rC_apply, alC_apply] using this

def detC (h : M22) : M22 →L[ℝ] ℂ :=
  ((h 0 0 : ℂ) • pr 1 1 + (h 1 1 : ℂ) • pr 0 0) - ((h 0 1 : ℂ) • pr 1 0 + (h 1 0 : ℂ) • pr 0 1)

theorem detC_apply (h X : M22) : detC h X = (dd h X : ℂ) := by
  simp only [detC, dd, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pr_apply]
  push_cast
  ring

theorem hasFDerivAt_det (h : M22) :
    HasFDerivAt (fun x : M22 => (((Matrix.of x).det : ℝ) : ℂ)) (detC h) h := by
  have e : (fun x : M22 => (((Matrix.of x).det : ℝ) : ℂ)) =
      fun x => pr 0 0 x * pr 1 1 x - pr 0 1 x * pr 1 0 x := by
    funext x
    rw [Matrix.det_fin_two]
    simp [pr_apply]
  rw [e]
  exact ((pr 0 0).hasFDerivAt.fun_mul (pr 1 1).hasFDerivAt).fun_sub
    ((pr 0 1).hasFDerivAt.fun_mul (pr 1 0).hasFDerivAt)

theorem hasFDerivAt_tt (h : M22) (h0 : al h ≠ 0) :
    HasFDerivAt tt
      ((al h ^ 2)⁻¹ • detC h +
        ((((Matrix.of h).det : ℝ) : ℂ) * (-((al h ^ 2) ^ 2)⁻¹)) • (al h • alC + al h • alC)) h := by
  have e : tt = fun x => (((Matrix.of x).det : ℝ) : ℂ) / (alC x * alC x) := by
    funext x
    rw [alC_apply, tt, sq]
  have hsq : HasFDerivAt (fun x => alC x * alC x) (al h • alC + al h • alC) h := by
    have := alC.hasFDerivAt.fun_mul (alC.hasFDerivAt (x := h))
    simpa only [alC_apply] using this
  have hne : alC h * alC h ≠ 0 := by
    rw [alC_apply]
    exact mul_ne_zero h0 h0
  have := hasFDerivAt_quot (hasFDerivAt_det h) hsq hne
  rw [e]
  simpa only [alC_apply, ← sq] using this

theorem dd_rpol (a b : Fin 2) (h : M22) :
    dd h (rpol a b h) = if a = b then (Matrix.of h).det else 0 := by
  fin_cases a <;> fin_cases b <;> simp [dd, rpol, Matrix.det_fin_two] <;> ring

theorem norm_tt (h : M22) (hΔ : 0 < (Matrix.of h).det) : ‖tt h‖ = uu h := by
  rw [tt, uu, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ]

theorem norm_fderiv_rho (a b c d : Fin 2) (h : M22) (h0 : al h ≠ 0) :
    ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 := by
  rw [(hasFDerivAt_rho c d h h0).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    rC_apply, alC_apply]
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr h0
  have b1 : ‖(al h)⁻¹ * al (rpol c d (rpol a b h))‖ ≤ 1 := by
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hA, mul_one]
    exact norm_al_rpol_rpol_le a b c d h
  have b2 : ‖al (rpol c d h) * (-(al h ^ 2)⁻¹) * al (rpol a b h)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_neg, norm_inv, norm_pow]
    have p1 := norm_al_rpol_le c d h
    have p2 := norm_al_rpol_le a b h
    have : ‖al (rpol c d h)‖ * ‖al (rpol a b h)‖ ≤ ‖al h‖ ^ 2 := by
      rw [sq]
      exact mul_le_mul p1 p2 (norm_nonneg _) (norm_nonneg _)
    calc ‖al (rpol c d h)‖ * (‖al h‖ ^ 2)⁻¹ * ‖al (rpol a b h)‖
        = (‖al (rpol c d h)‖ * ‖al (rpol a b h)‖) / ‖al h‖ ^ 2 := by
          rw [div_eq_mul_inv]; ring
      _ ≤ 1 := div_le_one_of_le₀ this (by positivity)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add b1 b2
    _ = 2 := by norm_num

theorem norm_fderiv_tt (a b : Fin 2) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  have h0 := al_ne h hΔ
  rw [(hasFDerivAt_tt h h0).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    alC_apply, detC_apply, dd_rpol]
  set δ : ℂ := if a = b then 1 else 0 with hδ
  have hdd : (((if a = b then (Matrix.of h).det else 0 : ℝ)) : ℂ) =
      δ * (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [hδ]
    split_ifs <;> simp
  rw [hdd]
  have key : (al h ^ 2)⁻¹ * (δ * (((Matrix.of h).det : ℝ) : ℂ)) +
      (((Matrix.of h).det : ℝ) : ℂ) * (-((al h ^ 2) ^ 2)⁻¹) *
        (al h * al (rpol a b h) + al h * al (rpol a b h)) =
      tt h * (δ - 2 * (al (rpol a b h) / al h)) := by
    rw [tt]
    field_simp
    ring
  rw [key, norm_mul, norm_tt h hΔ, mul_comm]
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr h0
  have huu : 0 ≤ uu h := by
    rw [← norm_tt h hΔ]
    exact norm_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ huu
  have n1 : ‖δ‖ ≤ 1 := by
    rw [hδ]
    split_ifs <;> simp
  have n2 : ‖2 * (al (rpol a b h) / al h)‖ ≤ 2 := by
    rw [norm_mul, norm_div]
    have : ‖al (rpol a b h)‖ / ‖al h‖ ≤ 1 := div_le_one_of_le₀ (norm_al_rpol_le a b h) hA.le
    simpa using this
  calc _ ≤ ‖δ‖ + ‖2 * (al (rpol a b h) / al h)‖ := norm_sub_le _ _
    _ ≤ 1 + 2 := add_le_add n1 n2
    _ = 3 := by norm_num

theorem main : ∀ (a b c d : Fin 2) (h : M22), 0 < (Matrix.of h).det →
    DifferentiableAt ℝ (rho c d) h ∧ DifferentiableAt ℝ tt h ∧
      ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 ∧ ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  intro a b c d h hΔ
  have h0 := al_ne h hΔ
  exact ⟨(hasFDerivAt_rho c d h h0).differentiableAt, (hasFDerivAt_tt h h0).differentiableAt,
    norm_fderiv_rho a b c d h h0, norm_fderiv_tt a b h hΔ⟩

end GlobalTheory.CompanionTheory.DInt2.Drho

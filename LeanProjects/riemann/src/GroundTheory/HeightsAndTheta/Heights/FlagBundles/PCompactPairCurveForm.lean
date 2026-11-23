import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped ComplexConjugate

lemma fderiv_comp_coord_zero (h : ℂ → ℂ) (z : Fin 1 → ℂ) (hh : DifferentiableAt ℝ h (z 0))
    (v : Fin 1 → ℂ) :
    fderiv ℝ (fun w : Fin 1 → ℂ => h (w 0)) z v = fderiv ℝ h (z 0) (v 0) := by
  have := hh.hasFDerivAt.comp z (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℂ) 0 z)
  rw [show (fun w : Fin 1 → ℂ => h (w 0)) = h ∘ fun f => f 0 from rfl, this.fderiv]
  rfl

lemma ddcDensity_eq_laplacian (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (z : ℂ) :
    ddcDensity f z = (2 * Real.pi)⁻¹ * InnerProductSpace.laplacianWithin f Set.univ z := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdc : ∀ c : ℂ, Differentiable ℝ (fun x => fderiv ℝ f x c) := fun c x =>
    (hd2 x).clm_apply (differentiableAt_const c)
  have hdd : ∀ c v : ℂ, fderiv ℝ (fun x => fderiv ℝ f x c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
    intro c v
    rw [fderiv_clm_apply (hd2 z) (differentiableAt_const c)]
    simp

  have hof : ∀ x : ℂ, HasFDerivAt (fun y : ℂ => ((f y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f x)) x := fun x =>
    Complex.ofRealCLM.hasFDerivAt.comp x (hd x).hasFDerivAt
  set g : ℂ → ℂ := fun x => (1 / 2 : ℂ) *
    (((fderiv ℝ f x 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ f x Complex.I : ℝ) : ℂ)) with hg
  have hbar : (fun w : Fin 1 → ℂ => wirtingerBar (fun u : Fin 1 → ℂ => ((f (u 0) : ℝ) : ℂ)) 0 w) =
      fun w => g (w 0) := by
    funext w
    rw [wirtingerBar, fderiv_comp_coord_zero _ w (hof (w 0)).differentiableAt,
      fderiv_comp_coord_zero _ w (hof (w 0)).differentiableAt, (hof (w 0)).fderiv]
    simp [hg]

  have hga : ∀ c : ℂ, HasFDerivAt (fun x => ((fderiv ℝ f x c : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun x => fderiv ℝ f x c) z)) z := fun c =>
    Complex.ofRealCLM.hasFDerivAt.comp z (hdc c z).hasFDerivAt
  have hgd : HasFDerivAt g ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp
      (fderiv ℝ (fun x => fderiv ℝ f x 1) z) + Complex.I • Complex.ofRealCLM.comp
      (fderiv ℝ (fun x => fderiv ℝ f x Complex.I) z))) z :=
    ((hga 1).add ((hga Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  unfold ddcDensity
  rw [hbar, wirtinger, fderiv_comp_coord_zero g _ hgd.differentiableAt,
    fderiv_comp_coord_zero g _ hgd.differentiableAt, hgd.fderiv]
  simp only [InnerProductSpace.laplacianWithin_univ,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]
  simp [hdd]
  field_simp

lemma ddcDensity_fubiniStudy (z : ℂ) :
    ddcDensity (fun w => (1 / 2) * Real.log (1 + ‖w‖ ^ 2)) z =
      Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2 := by
  have hS : ∀ u : Fin 1 → ℂ, normSqSum u = ‖u 0‖ ^ 2 := fun u => by simp [normSqSum]
  set G : (Fin 1 → ℂ) → ℂ := fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ) with hG
  have hF : (fun u : Fin 1 → ℂ => (((1 / 2) * Real.log (1 + ‖u 0‖ ^ 2) : ℝ) : ℂ)) =
      fun u => (1 / 2 : ℂ) * G u := by
    funext u; simp only [hG, hS]; push_cast; ring
  set H : (Fin 1 → ℂ) → ℂ := fun u => (1 + normSqSum u)⁻¹ • u 0 with hH
  have hbar : (fun w => wirtingerBar (fun u : Fin 1 → ℂ =>
      (((1 / 2) * Real.log (1 + ‖u 0‖ ^ 2) : ℝ) : ℂ)) 0 w) = fun w => (1 / 2 : ℂ) * H w := by
    funext w
    have h0 := wirtingerBar_logPot (0 : Fin 1) w
    rw [wirtingerBar] at h0 ⊢
    rw [hF, fderiv_const_mul (hasFDerivAt_logPot w).differentiableAt]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    simp only [hH, Complex.real_smul]
    rw [← h0]
    ring
  have hch := CP.chernCoeff_apply (N := 1) 0 (fun _ => z) 0 0
  have hpot : (fun w => wirtingerBar (fun u => ((CP.kahlerPotential 0 u : ℝ) : ℂ)) 0 w) = H := by
    funext w
    simp only [CP.kahlerPotential_eq, hH, Complex.real_smul]
    exact wirtingerBar_logPot 0 w
  rw [CP.chernCoeff, Matrix.of_apply, hpot] at hch
  have hHd : DifferentiableAt ℝ H (fun _ => z) := (hasFDerivAt_coordDiv 0 _).differentiableAt
  have hW : wirtinger (fun w => (1 / 2 : ℂ) * H w) 0 (fun _ => z) =
      (1 / 2 : ℂ) * wirtinger H 0 (fun _ => z) := by
    rw [wirtinger, wirtinger, fderiv_const_mul hHd]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  unfold ddcDensity
  rw [hbar, hW]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hSz : normSqSum (fun _ : Fin 1 => z) = ‖z‖ ^ 2 := hS _
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hWv : wirtinger H 0 (fun _ => z) = (((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) := by
    have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      have : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    rw [hSz, Matrix.one_apply_eq, Complex.conj_mul'] at hch
    have hne : (1 + (‖z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
    apply mul_left_cancel₀ hc
    rw [hch]
    push_cast
    field_simp
    ring
  rw [hWv]
  have : ((1 / 2 : ℂ) * ((((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)).re =
      (1 / 2) * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    rw [show (1 / 2 : ℂ) * ((((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) =
      (((1 / 2) * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [this]
  field_simp

lemma integral_fubiniStudy_density :
    ∫ z : ℂ, Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2 = 1 := by
  have h := (integral_complex_norm_pow_div 1 one_pos 0 0).2
  simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, zero_add, one_pow, div_one,
    mul_one, Nat.reduceAdd, one_div] at h
  have e : (fun z : ℂ => Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2) =
      fun z => Real.pi⁻¹ * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    funext z; rw [div_eq_mul_inv]
  rw [e, integral_const_mul, h, Nat.factorial_one, Nat.cast_one, inv_one, mul_one]
  exact inv_mul_cancel₀ Real.pi_ne_zero

theorem CompactPairCurveForm.proof : CompactPairCurveForm.Statement :=
  ⟨ddcDensity_eq_laplacian, ddcDensity_fubiniStudy, integral_fubiniStudy_density⟩

end GroundTheory.Heights₂.Heights.FlagBundles

import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ComplexHessianIsHermitianOfContDiffAt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Matrix

noncomputable section

variable {D E : ℕ}

def jacC (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) : Matrix (Fin E) (Fin D) ℂ :=
  Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a

theorem jacC_id (z : Fin D → ℂ) : jacC (id : (Fin D → ℂ) → (Fin D → ℂ)) z = 1 := by
  ext a k
  simp only [jacC, Matrix.of_apply, fderiv_id, ContinuousLinearMap.coe_id', id_eq,
    Matrix.one_apply, Pi.single_apply]

theorem jacC_eq_toMatrix' (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) :
    jacC τ z = LinearMap.toMatrix' (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin E → ℂ)) := by
  ext a k
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem jacC_mulVec (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z w : Fin D → ℂ) :
    jacC τ z *ᵥ w = fderiv ℂ τ z w := by
  rw [jacC_eq_toMatrix', LinearMap.toMatrix'_mulVec]
  rfl

theorem det_jacC (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ) :
    (jacC τ z).det = LinearMap.det (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) := by
  rw [jacC_eq_toMatrix', LinearMap.det_toMatrix']

theorem hessC_isHermitian (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  exact TraceConjugationCover.complexHessian_isHermitian_of_contDiffAt φ z hφ

theorem hessC_add (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  exact TraceConjugationCover.complexHessian_add_of_contDiffAt φ ψ z hφ hψ

theorem hessC_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    hessC (φ ∘ τ) z = (jacC τ z)ᵀ * hessC φ (τ z) * (jacC τ z).map (starRingEnd ℂ) := by
  exact TraceConjugationCover.complexHessian_comp_holomorphic_matrix φ τ z hτ hφ

theorem maDens_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z)) :
    maDens (fun k => φ k ∘ τ) z = maDens φ (τ z) * Complex.normSq (jacC τ z).det := by
  have h : (fun k => hessC (φ k ∘ τ) z) =
      fun k => (jacC τ z)ᵀ * hessC (φ k) (τ z) * (jacC τ z).map (starRingEnd ℂ) :=
    funext fun k => hessC_comp (φ k) τ z hτ (hφ k)
  simp only [maDens]
  rw [h, mdisc_transpose_mul_mul_conj, Complex.re_ofReal_mul]
  ring

theorem hessC_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  exact hessC_log_norm' g z hg hz

theorem hessC_add_log_norm (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  exact hessC_add_log_norm' φ g z hφ hg hz

theorem hessC_re_analytic (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => (G w).re) z = 0 := by
  exact hessC_re_analytic' G z hG

theorem hessC_add_re_analytic (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  exact hessC_add_re_analytic' φ G z hφ hG

theorem det_restrictScalars_real {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

theorem det_fderiv_real_eq_normSq (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ)
    (hτ : DifferentiableAt ℂ τ z) :
    (fderiv ℝ τ z).det = Complex.normSq (jacC τ z).det := by
  rw [(hτ.hasFDerivAt.restrictScalars ℝ).fderiv, det_jacC]
  exact det_restrictScalars_real (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

theorem integral_image_eq_integral_normSq_det_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    ∫ w in τ '' U, f w = ∫ z in U, Complex.normSq (jacC τ z).det • f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem lintegral_image_eq_lintegral_normSq_det_mul (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (U : Set (Fin D → ℂ)) (hU : IsOpen U) (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U)
    (f : (Fin D → ℂ) → ENNReal) :
    ∫⁻ w in τ '' U, f w = ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (jacC τ z).det) * f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem integrableOn_image_iff_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    IntegrableOn f (τ '' U) ↔
      IntegrableOn (fun z => Complex.normSq (jacC τ z).det • f (τ z)) U := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem maInt_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ)
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U U' : Set (Fin D → ℂ)) (hU : IsOpen U) (hU' : IsOpen U')
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (himg : τ '' U = U')
    (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) U') :
    maInt (fun k => φ k ∘ τ) (g ∘ τ) U = maInt φ g U' := by
  unfold maInt
  rw [← himg, integral_image_eq_integral_normSq_det_smul τ U hU hτ hinj]
  first
    | apply setIntegral_congr_fun hU.measurableSet
    | apply setIntegral_congr hU.measurableSet
  intro z hz
  have hz' : τ z ∈ U' := himg ▸ Set.mem_image_of_mem τ hz
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z) := fun k => (hφ k).contDiffAt (hU'.mem_nhds hz')
  simp only [Function.comp_apply, smul_eq_mul]
  rw [maDens_comp φ τ z (hτ z hz) hc]
  ring

theorem hessC_sum_normSq (z : Fin D → ℂ) :
    hessC (fun w => ∑ i, Complex.normSq (w i)) z = 1 := by
  exact TraceConjugationCover.complexHessian_sum_normSq_coord z

end

end ReciprocityTheory.AnForm.A

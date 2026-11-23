import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']

theorem eventually_fderiv_I_smul {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y) :
    ∀ᶠ y' in 𝓝 y, ∀ v, fderiv ℝ F y' (Complex.I • v) = Complex.I • fderiv ℝ F y' v := by
  filter_upwards [hF.eventually (by simp)] with y' hy' v
  rw [(hy'.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
  simp

theorem fderiv_fderiv_I_right {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y u (Complex.I • v) = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  have hR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y' => fderiv ℝ F y' (Complex.I • v))
      ((fderiv ℝ (fderiv ℝ F) y).flip (Complex.I • v)) y := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • v) y)
  have h2 : HasFDerivAt (fun y' => Complex.I • fderiv ℝ F y' v)
      (Complex.I • (fderiv ℝ (fderiv ℝ F) y).flip v) y := by
    have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).const_smul Complex.I
    simpa [Pi.smul_def] using this
  have h3 := h2.congr_of_eventuallyEq ((eventually_fderiv_I_smul hF).mono fun y' hy' => hy' v)
  have := congrArg (fun L => L u) (h1.unique h3)
  simpa using this

omit [NormedSpace ℂ E'] [IsScalarTower ℝ ℂ E'] in

theorem fderiv_fderiv_symm {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) : fderiv ℝ (fderiv ℝ F) y u v = fderiv ℝ (fderiv ℝ F) y v u :=
  hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) u v

theorem fderiv_fderiv_I_left {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y (Complex.I • u) v = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  rw [fderiv_fderiv_symm (hF.restrict_scalars ℝ), fderiv_fderiv_I_right hF,
    fderiv_fderiv_symm (hF.restrict_scalars ℝ)]

theorem fderiv_fderiv_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : G → ℝ}
    {F : (Fin D → ℂ) → G} {y : Fin D → ℂ} (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y' => g (F y')) y u v =
      fderiv ℝ (fderiv ℝ g) (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) +
        fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) := by
  have hgev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ g (F y') :=
    hF.continuousAt.tendsto.eventually
      ((hg.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hFev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ F y' :=
    (hF.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => g (F y')) =ᶠ[𝓝 y]
      fun y' => (fderiv ℝ g (F y')).comp (fderiv ℝ F y') := by
    filter_upwards [hgev, hFev] with y' h1 h2
    exact fderiv_comp y' h1 h2
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) (F y) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y' => fderiv ℝ g (F y'))
      ((fderiv ℝ (fderiv ℝ g) (F y)).comp (fderiv ℝ F y)) y :=
    hgd.hasFDerivAt.comp y (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hall := (hc.clm_comp hFd.hasFDerivAt).congr_of_eventuallyEq heq
  rw [hall.fderiv]
  simp [add_comm]

theorem fderiv_fderiv_add {f₁ f₂ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h₁ : ContDiffAt ℝ 2 f₁ y)
    (h₂ : ContDiffAt ℝ 2 f₂ y) :
    fderiv ℝ (fderiv ℝ fun y' => f₁ y' + f₂ y') y = fderiv ℝ (fderiv ℝ f₁) y + fderiv ℝ (fderiv ℝ f₂) y := by
  have heq : fderiv ℝ (fun y' => f₁ y' + f₂ y') =ᶠ[𝓝 y] fun y' => fderiv ℝ f₁ y' + fderiv ℝ f₂ y' := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y' a b
    exact fderiv_add (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))
  have hd₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₂ : DifferentiableAt ℝ (fderiv ℝ f₂) y :=
    (h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hd₁.hasFDerivAt.add hd₂.hasFDerivAt).congr_of_eventuallyEq heq).fderiv

theorem sesq_eq_of_form (H H₀ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, H u v = H₀ (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) (a b : Fin D → ℂ) :
    sesq H a b = sesq H₀ (L a) (L b) := by
  simp only [sesq, hH, map_smul]
  rw [hR₁, hR₂]
  push_cast
  ring

theorem cxHessian_of_form (f g : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ))
    (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, fderiv ℝ (fderiv ℝ f) y u v = fderiv ℝ (fderiv ℝ g) w (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) :
    cxHessian f y = (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ * cxHessian g w *
      (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map (starRingEnd ℂ) := by
  ext i j
  rw [cxHessian_eq_sesq, sesq_eq_of_form _ _ L R hH hR₁ hR₂, sesq_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian g w l k = sesq (fderiv ℝ (fderiv ℝ g) w) (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [hc, starRingEnd_apply]
  ring

theorem cxHessian_comp_holo (f g : (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ)) (h : (Fin D → ℂ) → ℂ)
    (y : Fin D → ℂ) (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℂ 2 F y) (hh : ContDiffAt ℂ 2 h y)
    (hf : f =ᶠ[𝓝 y] fun y' => g (F y') + (h y').re) :
    cxHessian f y = (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ *
      cxHessian g (F y) * (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map
        (starRingEnd ℂ) := by
  have hFR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hhR : ContDiffAt ℝ 2 h y := hh.restrict_scalars ℝ
  have hHess : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ fun y' => g (F y') + (h y').re) y := by
    have : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun y' => g (F y') + (h y').re) :=
      hf.eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq
    exact this.fderiv_eq
  have hre2 : ContDiffAt ℝ 2 (fun y' => (h y').re) y := Complex.reCLM.contDiff.contDiffAt.comp y hhR
  have hsum := fderiv_fderiv_add (f₁ := fun y' => g (F y')) (f₂ := fun y' => (h y').re) (hg.comp y hFR) hre2
  have hre : ∀ u v, fderiv ℝ (fderiv ℝ fun y' => (h y').re) y u v =
      Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v) := by
    intro u v
    have := fderiv_fderiv_comp (g := ⇑Complex.reCLM) (F := h) Complex.reCLM.contDiff.contDiffAt hhR u v
    have h0 : fderiv ℝ (fderiv ℝ (⇑Complex.reCLM)) (h y) = 0 := by
      have : fderiv ℝ (⇑Complex.reCLM) = fun _ => Complex.reCLM := funext fun _ => Complex.reCLM.fderiv
      rw [this]
      exact fderiv_const_apply _
    rw [h0, Complex.reCLM.fderiv] at this
    simpa using this
  have hLF : ∀ u, fderiv ℝ F y u = fderiv ℂ F y u := fun u => by
    rw [(hF.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  refine cxHessian_of_form f g y (F y) (fderiv ℂ F y)
    (fun u v => fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) + Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v))
    ?_ ?_ ?_
  · intro u v
    rw [hHess, hsum, _root_.add_apply, _root_.add_apply, fderiv_fderiv_comp hg hFR,
      hre, hLF, hLF]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh]

theorem maDensity_comp_holo (Φ' Φ : Fin D → (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ))
    (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ) (hΦ : ∀ j, ContDiffAt ℝ 2 (Φ j) (F y)) (hF : ContDiffAt ℂ 2 F y)
    (hh : ContDiffAt ℂ 2 h y) (hΦ' : ∀ j, Φ' j =ᶠ[𝓝 y] fun y' => Φ j (F y') + (h y').re) :
    maDensity Φ' y = Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det *
      maDensity Φ (F y) := by
  set J := LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) with hJ
  have hQ : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
  have hH : ∀ j, cxHessian (Φ' j) y = Jᵀ * cxHessian (Φ j) (F y) * J.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_holo (Φ' j) (Φ j) F h y (hΦ j) hF hh (hΦ' j)
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Jᵀ) (J.map (starRingEnd ℂ)) (fun j => cxHessian (Φ j) (F y)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem det_fderiv_real {F : (Fin D → ℂ) → (Fin D → ℂ)} {y : Fin D → ℂ} (hF : DifferentiableAt ℂ F y) :
    (fderiv ℝ F y).det =
      Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det := by
  rw [hF.fderiv_restrictScalars ℝ, LinearMap.det_toMatrix']
  have : ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F y) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) :
      (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      ((fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).restrictScalars ℝ := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

end ChartEnergySwapHessian

end

end GroundTheory.Heights₂.Heights

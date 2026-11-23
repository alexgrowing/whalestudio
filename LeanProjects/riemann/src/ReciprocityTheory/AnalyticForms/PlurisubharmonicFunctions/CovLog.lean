import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm.A

open Complex Filter Topology

noncomputable section

variable {D : ℕ}

theorem hessC_congr' {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    hessC φ z = hessC ψ z := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
    h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := h1.fderiv_eq
  ext i j
  simp only [hessC, h2]

theorem hessC_eq_zero_of_re_bilin (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ)
    (hB : ∀ v u, fderiv ℝ (fderiv ℝ φ) z v u = (B v u).re) : hessC φ z = 0 := by
  ext i j
  simp only [hessC, hB, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  simp

theorem hessC_add' (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have hφ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ φ w :=
    (hφ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hψ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ ψ w :=
    (hψ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hE : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w :=
    (hφ'.and hψ').mono fun w hw => fderiv_add hw.1 hw.2
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdψ : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [hE.fderiv_eq]
    exact fderiv_add hdφ hdψ
  ext i j
  simp only [hessC, h2, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

private lemma fderiv_re_apply_lemma (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : DifferentiableAt ℂ g z) (v : Fin D → ℂ) :
    fderiv ℝ (fun w => (g w).re) z v = (fderiv ℂ g z v).re := by
  have h : HasFDerivAt (fun w => (g w).re)
      (Complex.reCLM.comp ((fderiv ℂ g z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  rw [h.fderiv]
  rfl

theorem fderiv_fderiv_re_analytic (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z)
    (v u : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u = (fderiv ℂ (fderiv ℂ G) z v u).re := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  have hdΦ : DifferentiableAt ℝ (fderiv ℝ (fun w => (G w).re)) z :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ G w := hG.eventually_analyticAt
  have hE : (fun w => fderiv ℝ (fun w => (G w).re) w u) =ᶠ[𝓝 z]
      fun w => (fderiv ℂ G w u).re :=
    hA.mono fun w hw => fderiv_re_apply_lemma G w hw.differentiableAt u
  have hdG : DifferentiableAt ℂ (fun w => fderiv ℂ G w u) z :=
    (hG.fderiv.differentiableAt).clm_apply (differentiableAt_const u)
  have h1 : fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u =
      fderiv ℝ (fun w => fderiv ℝ (fun w => (G w).re) w u) z v := by
    rw [fderiv_clm_apply hdΦ (differentiableAt_const u)]
    simp
  have h2 : fderiv ℂ (fun w => fderiv ℂ G w u) z v = fderiv ℂ (fderiv ℂ G) z v u := by
    rw [fderiv_clm_apply (hG.fderiv.differentiableAt) (differentiableAt_const u)]
    simp
  rw [h1, hE.fderiv_eq, fderiv_re_apply_lemma _ z hdG v, h2]

theorem hessC_re_analytic' (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => (G w).re) z = 0 := hessC_eq_zero_of_re_bilin _ z _ (fderiv_fderiv_re_analytic G z hG)

theorem hessC_add_re_analytic' (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  rw [hessC_add' φ _ z hφ hΦ, hessC_re_analytic' G z hG, add_zero]

theorem exists_re_analytic_eq_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticAt ℂ G z ∧
      (fun w => Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => (G w).re := by
  refine ⟨fun w => Complex.log (g w / g z) + Complex.log (g z), ?_, ?_⟩
  · refine AnalyticAt.add ?_ analyticAt_const
    refine (hg.div analyticAt_const hz).clog ?_
    show g z / g z ∈ Complex.slitPlane
    rw [div_self hz]
    exact Complex.one_mem_slitPlane
  · filter_upwards [hg.continuousAt.eventually_ne hz] with w hw
    simp only [Complex.add_re, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 hz)]
    ring

theorem hessC_log_norm' (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  rw [hessC_congr' hEq]
  exact hessC_re_analytic' G z hG

theorem hessC_add_log_norm' (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  have h2 : (fun w => φ w + Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => φ w + (G w).re :=
    hEq.mono fun w hw => by simp only [hw]
  rw [hessC_congr' h2]
  exact hessC_add_re_analytic' φ G z hφ hG

end

end ReciprocityTheory.AnForm.A

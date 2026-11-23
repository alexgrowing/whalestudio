import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

open UpperHalfPlane hiding I
open scoped Manifold ContDiff

private theorem archSm_eval_eq (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (σ : ℂ)
    (x0 : Fin 2 → Fin 2 → ℝ)
    (hD : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0)
    (hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0)
    (him : 0 < (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im) :
    ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ)) *
        f (ofComplex (σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
          ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))))) x0 := by
  have hre : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => ((x i j : ℝ) : ℂ)) :=
    fun i j => Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have hDd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  have hcd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) :=
    ((hre 1 0).mul contDiff_const).add (hre 1 1)
  have had : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) :=
    ((hre 0 0).mul contDiff_const).add (hre 0 1)
  have habs : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      |x 0 0 * x 1 1 - x 0 1 * x 1 0|) x0 :=
    ContDiffAt.comp (g := fun t : ℝ => |t|) x0 (contDiffAt_abs hD) hDd.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ)) x0 := by
    refine Complex.ofRealCLM.contDiff.contDiffAt.comp x0 ?_
    exact habs.rpow_const_of_ne (abs_ne_zero.mpr hD)
  have h2 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ))) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-(k : ℤ)))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-(k : ℤ)) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact (hz.contDiffAt.restrict_scalars ℝ).comp x0 hcd.contDiffAt
  have hinv : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-1 : ℤ)) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-1 : ℤ))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-1 : ℤ) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact (hz.contDiffAt.restrict_scalars ℝ).comp x0 hcd.contDiffAt
  have hw : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0 := by
    simp only [div_eq_mul_inv, ← zpow_neg_one]
    exact contDiffAt_const.mul (had.contDiffAt.mul hinv)
  have hF : AnalyticAt ℂ (f ∘ ofComplex) (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) +
      (x0 0 1 : ℂ)) / ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))) :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet _ him
  have h3 := ContDiffAt.comp (g := f ∘ ofComplex) (f := fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0
    (hF.contDiffAt.restrict_scalars ℝ) hw
  exact (h1.mul h2).mul h3

theorem UpperTheory.V.Af.Nf.archSm :
    UpperTheory.V.Af.Nf.ArchSm := by
  intro k f hf
  have hD : ∀ x : Fin 2 → Fin 2 → ℝ,
      (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    intro x
    simp [Matrix.det_fin_two]
  have hDc : Continuous (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  intro x0 hx0
  refine ContDiffAt.contDiffWithinAt ?_
  have hx0' : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0 := by
    simpa [hD] using hx0
  have hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    apply hx0'
    rw [h1, h2]
    ring
  have hsign : ∀ᶠ x in nhds x0, SignType.sign (x 0 0 * x 1 1 - x 0 1 * x 1 0) =
      SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) := by
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · filter_upwards [hDc.continuousAt.eventually (gt_mem_nhds hneg)] with x hx
      rw [sign_neg hx, sign_neg hneg]
    · filter_upwards [hDc.continuousAt.eventually (lt_mem_nhds hpos)] with x hx
      rw [sign_pos hx, sign_pos hpos]
  have hq : (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
      ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ))).im =
      (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
        Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) := by
    rw [Complex.div_im]
    simp
    ring
  have hn : 0 < Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
    Complex.normSq_pos.mpr hc
  have him : 0 < ((((SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) : ℝ)) : ℂ) *
      (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq]
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · rw [sign_neg hneg]
      have : (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
          Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) < 0 :=
        div_neg_of_neg_of_pos hneg hn
      simp only [SignType.coe_neg, SignType.coe_one]
      linarith
    · rw [sign_pos hpos]
      simp only [SignType.coe_one, one_mul]
      exact div_pos hpos hn
  refine (archSm_eval_eq k f hf _ x0 hx0' hc him).congr_of_eventuallyEq ?_
  filter_upwards [hsign] with x hx
  unfold UpperTheory.V.Af.Nf.arch UpperTheory.V.Af.Nf.nsl
  rw [hD, hx]
  simp only [Matrix.of_apply]

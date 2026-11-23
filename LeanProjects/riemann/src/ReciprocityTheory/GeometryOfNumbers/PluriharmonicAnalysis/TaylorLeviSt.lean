import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Complex

section
variable {D : ℕ}

lemma pgtl_smul_decomp (c : ℂ) (z : Fin D → ℂ) : c • z = c.re • z + c.im • (I • z) := by
  ext j
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

lemma pgtl_clin {F : Type*} [AddCommGroup F] [Module ℂ F] (f : (Fin D → ℂ) → F)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hr : ∀ (r : ℝ) x, f (r • x) = (r : ℂ) • f x)
    (hI : ∀ x, f (I • x) = I • f x) (c : ℂ) (x : Fin D → ℂ) : f (c • x) = c • f x := by
  rw [pgtl_smul_decomp c x, hadd, hr, hr, hI]
  conv_rhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul]

noncomputable def pgtlCx (d : (Fin D → ℂ) →L[ℝ] ℝ) : (Fin D → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
  { toFun := fun z => (d z : ℂ) - I * (d (I • z) : ℂ)
    map_add' := by intro x y; simp only [smul_add, map_add, ofReal_add]; ring
    map_smul' := by
      intro c z
      simp only [RingHom.id_apply, smul_eq_mul]
      refine pgtl_clin (fun z => (d z : ℂ) - I * (d (I • z) : ℂ)) ?_ ?_ ?_ c z
      · intro x y; simp only [smul_add, map_add, ofReal_add]; ring
      · intro r x
        rw [smul_comm I r x, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        push_cast; ring
      · intro x
        rw [smul_smul, I_mul_I, neg_one_smul, map_neg, smul_eq_mul]
        push_cast
        ring_nf
        rw [I_sq]; ring }

lemma pgtlCx_apply (d : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    pgtlCx d z = (d z : ℂ) - I * (d (I • z) : ℂ) := rfl

lemma pgtlCx_re (d : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) : (pgtlCx d z).re = d z := by
  simp [pgtlCx_apply]

noncomputable def pgtlJ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) :=
  (I • ContinuousLinearMap.id ℂ (Fin D → ℂ)).restrictScalars ℝ

lemma pgtlJ_apply (w : Fin D → ℂ) : pgtlJ w = I • w := rfl

noncomputable def pgtlDz (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (Fin D → ℂ) →L[ℝ] ℝ :=
  (1 / 4 : ℝ) • (B z - (B (I • z)).comp pgtlJ)

lemma pgtlDz_apply (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z w : Fin D → ℂ) :
    pgtlDz B z w = (B z w - B (I • z) (I • w)) / 4 := by
  simp only [pgtlDz, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, pgtlJ_apply, smul_eq_mul]
  ring

noncomputable def pgtlBil (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
  { toFun := fun z => pgtlCx (pgtlDz B z)
    map_add' := by
      intro x y
      refine ContinuousLinearMap.ext fun w => ?_
      simp only [ContinuousLinearMap.add_apply, pgtlCx_apply, pgtlDz_apply, smul_add, map_add]
      apply Complex.ext <;> simp <;> ring
    map_smul' := by
      intro c z
      simp only [RingHom.id_apply]
      refine pgtl_clin (fun z => pgtlCx (pgtlDz B z)) ?_ ?_ ?_ c z
      · intro x y
        refine ContinuousLinearMap.ext fun w => ?_
        simp only [ContinuousLinearMap.add_apply, pgtlCx_apply, pgtlDz_apply, smul_add, map_add]
        apply Complex.ext <;> simp <;> ring
      · intro r x
        refine ContinuousLinearMap.ext fun w => ?_
        simp only [ContinuousLinearMap.smul_apply, pgtlCx_apply, pgtlDz_apply, smul_comm I r x,
          map_smul, smul_eq_mul]
        apply Complex.ext <;> simp <;> ring
      · intro x
        refine ContinuousLinearMap.ext fun w => ?_
        simp only [ContinuousLinearMap.smul_apply, pgtlCx_apply, pgtlDz_apply, smul_smul, I_mul_I,
          neg_one_smul, map_neg, ContinuousLinearMap.neg_apply, smul_eq_mul]
        apply Complex.ext <;> simp <;> ring }

lemma pgtlBil_apply (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z w : Fin D → ℂ) :
    pgtlBil B z w = pgtlCx (pgtlDz B z) w := rfl

lemma pgtlBil_re (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (pgtlBil B z z).re = (B z z - B (I • z) (I • z)) / 4 := by
  rw [pgtlBil_apply, pgtlCx_re, pgtlDz_apply]

end

lemma pgtl_taylor {D : ℕ} {ρ₀ K₃ : ℝ} (φ : (Fin D → ℂ) → ℝ)
    (hφ : ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀))
    (hK₃ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃)
    (z : Fin D → ℂ) (hz : z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀) :
    |φ z - φ 0 - fderiv ℝ φ 0 z - fderiv ℝ (fderiv ℝ φ) 0 z z / 2| ≤ K₃ * ‖z‖ ^ 3 := by
  have hzr : ‖z‖ < ρ₀ := mem_ball_zero_iff.mp hz
  have h0 : (0 : Fin D → ℂ) ∈ Metric.ball (0 : Fin D → ℂ) ρ₀ :=
    Metric.mem_ball_self ((norm_nonneg z).trans_lt hzr)
  have hK : 0 ≤ K₃ := (norm_nonneg _).trans (hK₃ 0 h0)
  have hat : ∀ x ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ContDiffAt ℝ 3 φ x :=
    fun x hx => hφ.contDiffAt (Metric.isOpen_ball.mem_nhds hx)
  set B := fderiv ℝ (fderiv ℝ φ) 0 with hB
  set d₁ := fderiv ℝ φ 0 with hd₁
  set s := Metric.closedBall (0 : Fin D → ℂ) ‖z‖ with hs
  have hsub : s ⊆ Metric.ball 0 ρ₀ := Metric.closedBall_subset_ball hzr
  have hsc : Convex ℝ s := convex_closedBall _ _
  have h0s : (0 : Fin D → ℂ) ∈ s := Metric.mem_closedBall_self (norm_nonneg z)
  have hzs : z ∈ s := mem_closedBall_zero_iff.2 le_rfl
  have hxs : ∀ x ∈ s, ‖x‖ ≤ ‖z‖ := fun x hx => mem_closedBall_zero_iff.1 hx
  have hd3 : ∀ x ∈ s, HasFDerivAt (fderiv ℝ (fderiv ℝ φ))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x) x := by
    intro x hx
    have h2 := ((hat x (hsub hx)).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)
    exact (h2.differentiableAt (by norm_num)).hasFDerivAt
  have hd2 : ∀ x ∈ s, HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x := by
    intro x hx
    have h2 := (hat x (hsub hx)).fderiv_right (m := 2) (by norm_num)
    exact (h2.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 : ∀ x ∈ s, HasFDerivAt φ (fderiv ℝ φ x) x := by
    intro x hx
    exact ((hat x (hsub hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hT : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ K₃ := by
    intro x hx
    have e : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ = ‖iteratedFDeriv ℝ 3 φ x‖ := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ (fderiv ℝ (fderiv ℝ φ))),
        norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    rw [e]; exact hK₃ x (hsub hx)
  have hA : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ φ) x - B‖ ≤ K₃ * ‖x‖ := by
    intro x hx
    have := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hd3 y hy).hasFDerivWithinAt) hT h0s hx
    simpa using this
  have hBd : ∀ x ∈ s, HasFDerivAt (fun y => fderiv ℝ φ y - d₁ - B y)
      (fderiv ℝ (fderiv ℝ φ) x - B) x := by
    intro x hx
    exact ((hd2 x hx).sub_const d₁).sub B.hasFDerivAt
  have hBb : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ φ) x - B‖ ≤ K₃ * ‖z‖ :=
    fun x hx => (hA x hx).trans (mul_le_mul_of_nonneg_left (hxs x hx) hK)
  have hψ : ∀ x ∈ s, ‖fderiv ℝ φ x - d₁ - B x‖ ≤ K₃ * ‖z‖ * ‖x‖ := by
    intro x hx
    have := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hBd y hy).hasFDerivWithinAt) hBb h0s hx
    simpa [hd₁] using this
  have hsym : ∀ v w, B v w = B w v := (hat 0 h0).isSymmSndFDerivAt (by simp; norm_num)
  have hCd : ∀ x ∈ s, HasFDerivAt (fun y => φ y - φ 0 - d₁ y - B y y / 2)
      (fderiv ℝ φ x - d₁ - B x) x := by
    intro x hx
    have h := ((((hd1 x hx).sub_const (φ 0)).sub d₁.hasFDerivAt).sub
      (HasFDerivAt.mul_const (B.hasFDerivAt.clm_apply (hasFDerivAt_id x)) (2⁻¹ : ℝ)))
    have hf : (fun y => φ y - φ 0 - d₁ y - B y y / 2) =
        ((fun x => φ x - φ 0) - ⇑d₁ - fun y => (B y) (id y) * 2⁻¹) := by
      funext y; simp [div_eq_mul_inv]
    rw [hf]
    refine h.congr_fderiv ?_
    ext h'
    simp
    rw [hsym h' x]
    ring
  have hCb : ∀ x ∈ s, ‖fderiv ℝ φ x - d₁ - B x‖ ≤ K₃ * ‖z‖ * ‖z‖ :=
    fun x hx => (hψ x hx).trans (mul_le_mul_of_nonneg_left (hxs x hx) (by positivity))
  have key := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hCd y hy).hasFDerivWithinAt) hCb h0s hzs
  simp only [sub_self, map_zero, zero_div, sub_zero,
    Real.norm_eq_abs] at key
  calc _ ≤ K₃ * ‖z‖ * ‖z‖ * ‖z‖ := key
    _ = K₃ * ‖z‖ ^ 3 := by ring

theorem exists_pluriharmonic_part {D : ℕ} {ρ₀ K₃ : ℝ} (φ : (Fin D → ℂ) → ℝ)
    (hφ : ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀))
    (hK₃ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃) :
    ∃ q : (Fin D → ℂ) → ℂ, Differentiable ℂ q ∧ q 0 = 0 ∧
      ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
        |φ z - φ 0 - (q z).re -
          (fderiv ℝ (fderiv ℝ φ) 0 z z + fderiv ℝ (fderiv ℝ φ) 0 (I • z) (I • z)) / 4| ≤
        K₃ * ‖z‖ ^ 3 := by
  refine ⟨fun z => pgtlCx (fderiv ℝ φ 0) z + pgtlBil (fderiv ℝ (fderiv ℝ φ) 0) z z, ?_, ?_, ?_⟩
  · exact (pgtlCx _).differentiable.add ((pgtlBil _).differentiable.clm_apply differentiable_id)
  · simp
  · intro z hz
    have h := pgtl_taylor φ hφ hK₃ z hz
    dsimp only
    rw [add_re, pgtlCx_re, pgtlBil_re]
    have e : φ z - φ 0 - (fderiv ℝ φ 0 z + (fderiv ℝ (fderiv ℝ φ) 0 z z -
        fderiv ℝ (fderiv ℝ φ) 0 (I • z) (I • z)) / 4) -
        (fderiv ℝ (fderiv ℝ φ) 0 z z + fderiv ℝ (fderiv ℝ φ) 0 (I • z) (I • z)) / 4 =
        φ z - φ 0 - fderiv ℝ φ 0 z - fderiv ℝ (fderiv ℝ φ) 0 z z / 2 := by ring
    rw [e]
    exact h

end ReciprocityTheory.GeometryOfNumbersTheory

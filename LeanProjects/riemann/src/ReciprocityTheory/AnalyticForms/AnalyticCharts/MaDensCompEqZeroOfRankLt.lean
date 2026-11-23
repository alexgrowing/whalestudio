import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm

open Complex Filter Topology
open scoped Matrix

noncomputable section

def leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a b : Fin e → ℂ) : ℂ :=
  ((H a b + H (I • a) (I • b) : ℝ) + I * ((H a (I • b) - H (I • a) b : ℝ))) / 4

theorem hessC_eq_leviC {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (i j : Fin e) :
    hessC f z i j = leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl

theorem leviC_add {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a a' b : Fin e → ℂ) :
    leviC H (a + a') b = leviC H a b + leviC H a' b := by
  unfold leviC
  simp only [smul_add, map_add, ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem leviC_smul {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin e → ℂ) :
    leviC H (c • a) b = c * leviC H a b := by
  have hc : c • a = (c.re : ℝ) • a + (c.im : ℝ) • (I • a) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hc' : I • (c • a) = (c.re : ℝ) • (I • a) + (-c.im : ℝ) • a := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_neg]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination (↑c.im * a k) * Complex.I_sq
  unfold leviC
  rw [hc', hc]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  push_cast
  conv_rhs => rw [← Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem sum_mul_leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (v b : Fin e → ℂ) :
    ∑ i, v i * leviC H (Pi.single i 1) b = leviC H v b := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin e → ℂ) := by
    funext k
    simp [Pi.single_apply]
  have key : ∀ s : Finset (Fin e), leviC H (∑ i ∈ s, v i • (Pi.single i 1 : Fin e → ℂ)) b =
      ∑ i ∈ s, v i * leviC H (Pi.single i 1) b := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using leviC_smul H 0 0 b
    · intro i s hi ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi, leviC_add, leviC_smul, ih]
  rw [← key, ← hv]

theorem hess_comp_of_ker {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (w b : Fin e → ℂ) (hw : fderiv ℂ τ z w = 0) :
    fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b =
      fderiv ℝ φ (τ z) (fderiv ℂ (fun x => fderiv ℂ τ x b) z w) := by
  have hτev : ∀ᶠ x in 𝓝 z, AnalyticAt ℂ τ x := hτ.eventually_analyticAt
  have hφev : ∀ᶠ y in 𝓝 (τ z), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hφev' : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ φ (τ x) :=
    hτ.continuousAt.tendsto.eventually hφev
  have heq : (fun x => fderiv ℝ (φ ∘ τ) x b) =ᶠ[𝓝 z]
      (fun x => fderiv ℝ φ (τ x) (fderiv ℂ τ x b)) := by
    filter_upwards [hτev, hφev'] with x hx hφx
    have hxR : DifferentiableAt ℝ τ x := hx.differentiableAt.restrictScalars ℝ
    rw [fderiv_comp x hφx hxR, hx.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hf2 : ContDiffAt ℝ 2 (φ ∘ τ) z :=
    hφ.comp z ((hτ.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hD : DifferentiableAt ℝ (fderiv ℝ (φ ∘ τ)) z :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b = fderiv ℝ (fun x => fderiv ℝ (φ ∘ τ) x b) z w := by
    rw [fderiv_clm_apply hD (differentiableAt_const b)]
    simp
  rw [h1, heq.fderiv_eq]
  have hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (τ z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hτR : DifferentiableAt ℝ τ z := hτ.differentiableAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun x => fderiv ℝ φ (τ x))
      ((fderiv ℝ (fderiv ℝ φ) (τ z)).comp (fderiv ℝ τ z)) z :=
    hφ2.hasFDerivAt.comp z hτR.hasFDerivAt
  have hg : DifferentiableAt ℂ (fun x => fderiv ℂ τ x b) z :=
    hτ.fderiv.differentiableAt.clm_apply (differentiableAt_const b)
  have hu : HasFDerivAt (fun x => fderiv ℂ τ x b)
      ((fderiv ℂ (fun x => fderiv ℂ τ x b) z).restrictScalars ℝ) z :=
    hg.hasFDerivAt.restrictScalars ℝ
  rw [(hc.clm_apply hu).fderiv]
  have hwR : fderiv ℝ τ z w = 0 := by
    rw [hτ.differentiableAt.fderiv_restrictScalars ℝ]
    exact hw
  simp [hwR]

theorem vecMul_hessC_comp_eq_zero {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (v : Fin e → ℂ) (hv : fderiv ℂ τ z v = 0) :
    v ᵥ* hessC (φ ∘ τ) z = 0 := by
  have hH : ∀ b, leviC (fderiv ℝ (fderiv ℝ (φ ∘ τ)) z) v b = 0 := by
    intro b
    have hIv : fderiv ℂ τ z (Complex.I • v) = 0 := by rw [map_smul, hv, smul_zero]
    have hdiff : DifferentiableAt ℂ (fun x => fderiv ℂ τ x b) z :=
      (hτ.fderiv.differentiableAt).clm_apply (differentiableAt_const b)
    have hB : fderiv ℂ (fun x => fderiv ℂ τ x (Complex.I • b)) z =
        Complex.I • fderiv ℂ (fun x => fderiv ℂ τ x b) z := by
      have h0 : (fun x => fderiv ℂ τ x (Complex.I • b)) = fun x => Complex.I • fderiv ℂ τ x b := by
        funext x
        rw [map_smul]
      rw [h0]
      exact fderiv_const_smul hdiff Complex.I
    unfold leviC
    rw [hess_comp_of_ker φ τ z hτ hφ v b hv, hess_comp_of_ker φ τ z hτ hφ v _ hv,
      hess_comp_of_ker φ τ z hτ hφ _ b hIv, hess_comp_of_ker φ τ z hτ hφ _ _ hIv, hB]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
      map_neg]
    simp
  funext j
  show ∑ i, v i * hessC (φ ∘ τ) z i j = 0
  simp_rw [hessC_eq_leviC]
  rw [sum_mul_leviC, hH]

theorem maDens_comp_eq_zero_of_rank_lt {N e : ℕ} (φ : Fin e → (Fin N → ℂ) → ℝ)
    (τ : (Fin e → ℂ) → (Fin N → ℂ)) (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z)
    (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z))
    (hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ z).toLinearMap) < e) :
    maDens (fun k => φ k ∘ τ) z = 0 := by
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin e → ℂ, v ≠ 0 ∧ fderiv ℂ τ z v = 0 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ τ z).toLinearMap
    rw [Module.finrank_fin_fun] at h1
    have h2 : 0 < Module.finrank ℂ (LinearMap.ker (fderiv ℂ τ z).toLinearMap) := by omega
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
    exact ⟨x, fun h => hx (Subtype.ext h), x.2⟩
  have hvm : ∀ S : Finset (Fin e), v ᵥ* (∑ k ∈ S, hessC (φ k ∘ τ) z) = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp
    · intro k S hk ih
      rw [Finset.sum_insert hk, Matrix.vecMul_add, ih,
        vecMul_hessC_comp_eq_zero (φ k) τ z hτ (hφ k) v hv, add_zero]
  have hdet : ∀ S : Finset (Fin e), (∑ k ∈ S, hessC (φ k ∘ τ) z).det = 0 := fun S =>
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv0, hvm S⟩
  unfold maDens mdisc
  simp [hdet]

end

end ReciprocityTheory.AnForm

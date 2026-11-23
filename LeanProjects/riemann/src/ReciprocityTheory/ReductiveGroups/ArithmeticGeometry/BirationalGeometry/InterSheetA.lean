import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter Topology

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => c p.1 * z p

theorem eval_bsmul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (bsmul c z) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ s.support := support_map_subset _ _ hm
  have hblk := hs m hm'
  simp only [bsmul, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [← hblk k, Finset.prod_pow_eq_pow_sum]
  rw [hc]
  ring

theorem logNorm_bsmul (A : HermLine ι) {s : MRing ι} {a : K → ℕ} (hA : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNorm A s (bsmul c z) = logNorm A s z := by
  unfold logNorm
  rw [eval_bsmul_of_isMultiHomog hs]
  have hh : A.h (bsmul c z) = (∏ k, ‖c k‖ ^ (a k)) * A.h z := by
    rw [show bsmul c z = fun p => c p.1 * z p from rfl, A.smul c z hc]
    simp [hA, zpow_natCast]
  rw [hh, norm_mul, norm_prod]
  simp only [norm_pow]
  rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]

theorem prod_update_eq [DecidableEq K] (z : (Σ k, ι k) → ℂ) (i0 : (k : K) → ι k) (k : K) (i : ι k) :
    ∏ k', z ⟨k', Function.update i0 k i k'⟩ = z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k' hk' => ?_
    simp [Finset.ne_of_mem_erase hk']

theorem eq_bsmul_of_segre_eq {z z' : (Σ k, ι k) → ℂ} (i0 : (k : K) → ι k)
    (h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0) (hs : segre z = segre z') :
    (∀ k, z' ⟨k, i0 k⟩ ≠ 0) ∧ z' = bsmul (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z := by
  classical
  have hseg : ∀ i : (k : K) → ι k, ∏ k, z ⟨k, i k⟩ = ∏ k, z' ⟨k, i k⟩ := fun i => congrFun hs i
  have hP0 : ∏ k, z ⟨k, i0 k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => h0 k
  have h0' : ∀ k, z' ⟨k, i0 k⟩ ≠ 0 := by
    intro k
    have h1 : ∏ k, z' ⟨k, i0 k⟩ ≠ 0 := by rw [← hseg i0]; exact hP0
    exact Finset.prod_ne_zero_iff.1 h1 k (Finset.mem_univ _)
  refine ⟨h0', ?_⟩
  funext ⟨k, i⟩
  simp only [bsmul]
  have hA' : z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k i, ← prod_update_eq z' i0 k i]
    exact hseg _
  have hB' : z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k (i0 k), ← prod_update_eq z' i0 k (i0 k)]
    exact hseg _
  have hP' : ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => h0' k'
  rw [div_mul_eq_mul_div, eq_div_iff (h0 k)]
  apply mul_right_cancel₀ hP'
  linear_combination (-(z ⟨k, i0 k⟩)) * hA' + z ⟨k, i⟩ * hB'

end Alg

section Hess

variable {e : ℕ}

theorem fderiv_re_apply {h : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hh : DifferentiableAt ℂ h y)
    (v : Fin e → ℂ) : fderiv ℝ (fun y' => (h y').re) y v = (fderiv ℂ h y v).re := by
  have hd : HasFDerivAt (fun y' => (h y').re)
      (Complex.reCLM.comp ((fderiv ℂ h y).restrictScalars ℝ)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hh.hasFDerivAt.restrictScalars ℝ)
  rw [hd.fderiv]
  rfl

theorem hess_re {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hG : AnalyticAt ℂ G y) (v w : Fin e → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y v w = (fderiv ℂ (fderiv ℂ G) y v w).re := by
  let Φ : ((Fin e → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin e → ℂ) ℂ ℝ ℝ)
  have hΦ : ∀ L : (Fin e → ℂ) →L[ℂ] ℂ, ∀ u, Φ L u = (L u).re := fun L u => rfl
  have heq : fderiv ℝ (fun y' => (G y').re) =ᶠ[𝓝 y] fun y' => Φ (fderiv ℂ G y') := by
    filter_upwards [hG.eventually_analyticAt] with y' hy'
    ext u
    rw [fderiv_re_apply hy'.differentiableAt u, hΦ]
  have hD : HasFDerivAt (fderiv ℂ G) (fderiv ℂ (fderiv ℂ G) y) y :=
    hG.fderiv.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y' => Φ (fderiv ℂ G y'))
      (Φ.comp ((fderiv ℂ (fderiv ℂ G) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hD.restrictScalars ℝ)
  rw [heq.fderiv_eq, h2.fderiv]
  rfl

theorem cxHessian_add_re {φ : (Fin e → ℂ) → ℝ} {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (C : ℝ)
    (hφ : ContDiffAt ℝ 2 φ y) (hG : AnalyticAt ℂ G y) :
    cxHessian (fun y' => φ y' + (G y').re + C) y = cxHessian φ y := by
  have hre2 : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hG.contDiffAt.restrict_scalars ℝ)
  have hφev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ φ y' :=
    (hφ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hreev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y' => (G y').re) y' :=
    (hre2.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => φ y' + (G y').re + C) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ y' + fderiv ℝ (fun y' => (G y').re) y' := by
    filter_upwards [hφev, hreev] with y' h1 h2
    rw [fderiv_add_const]
    exact (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdre : DifferentiableAt ℝ (fderiv ℝ (fun y' => (G y').re)) y :=
    (hre2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsum : fderiv ℝ (fderiv ℝ (fun y' => φ y' + (G y').re + C)) y =
      fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y := by
    rw [heq.fderiv_eq]
    exact (hdφ.hasFDerivAt.add hdre.hasFDerivAt).fderiv
  have hH := hess_re hG
  have k1 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) (Complex.I • v) =
      - fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u v := by
    intro u v
    rw [hH, hH]
    simp [map_smul, ← mul_assoc]
  have k2 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u (Complex.I • v) =
      fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) v := by
    intro u v
    rw [hH, hH]
    simp [map_smul]
  ext i j
  simp only [cxHessian, hsum, ContinuousLinearMap.add_apply, k1, k2]
  push_cast
  ring

theorem cxHessian_congr {f g : (Fin e → ℂ) → ℝ} {y : Fin e → ℂ} (h : f =ᶠ[𝓝 y] g) :
    cxHessian f y = cxHessian g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := h.fderiv.fderiv_eq
  unfold cxHessian
  rw [h2]

end Hess

end ReciprocityTheory.ChartRestriction.G.Geo

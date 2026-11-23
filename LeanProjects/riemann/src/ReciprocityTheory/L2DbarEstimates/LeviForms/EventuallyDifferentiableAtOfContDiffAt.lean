import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph

open Complex ComplexConjugate Filter Topology

namespace ReciprocityTheory.L2DbarEstimates

def LeviNonnegOn (n : ℕ) (φ : V n → ℝ) (U : Set (V n)) : Prop :=
  ∀ x ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re

variable {n : ℕ}

theorem wd_congr {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by
  simp only [wd, h.fderiv_eq]

theorem wdb_congr {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wdb n j f x = wdb n j g x := by
  simp only [wdb, h.fderiv_eq]

theorem wdb_eventuallyEq {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wdb n j f =ᶠ[𝓝 x] wdb n j g := h.eventuallyEq_nhds.mono fun _ hy => wdb_congr hy

theorem leviV_congr {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) (ξ : Fin n → ℂ) :
    leviV n f x ξ = leviV n g x ξ := by
  unfold leviV
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [wd_congr (wdb_eventuallyEq h)]

theorem wd_add {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : wd n j (fun y => f y + g y) x = wd n j f x + wd n j g x := by
  unfold wd
  rw [(show HasFDerivAt (fun y => f y + g y) _ x from hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply]
  ring

theorem wdb_add {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : wdb n j (fun y => f y + g y) x = wdb n j f x + wdb n j g x := by
  unfold wdb
  rw [(show HasFDerivAt (fun y => f y + g y) _ x from hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply]
  ring

theorem wd_sum {ι : Type*} (s : Finset ι) {j : Fin n} {f : ι → V n → ℂ} {x : V n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wd n j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, wd n j (f i) x := by
  have e : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp [Finset.sum_apply]
  unfold wd
  rw [e, (HasFDerivAt.sum fun i hi => (hf i hi).hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]

theorem wdb_sum {ι : Type*} (s : Finset ι) {j : Fin n} {f : ι → V n → ℂ} {x : V n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wdb n j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, wdb n j (f i) x := by
  have e : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp [Finset.sum_apply]
  unfold wdb
  rw [e, (HasFDerivAt.sum fun i hi => (hf i hi).hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]

theorem wd_mul {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    wd n j (fun y => f y * g y) x = wd n j f x * g x + f x * wd n j g x := by
  unfold wd
  rw [(show HasFDerivAt (fun y => f y * g y) _ x from hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wdb_mul {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    wdb n j (fun y => f y * g y) x = wdb n j f x * g x + f x * wdb n j g x := by
  unfold wdb
  rw [(show HasFDerivAt (fun y => f y * g y) _ x from hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem fderiv_ofReal_apply {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) (w : V n) :
    fderiv ℝ (fun y => (v y : ℂ)) x w = (fderiv ℝ v x w : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hv.hasFDerivAt
  rw [(show HasFDerivAt (fun y => (v y : ℂ)) _ x from h).fderiv]
  rfl

theorem differentiableAt_ofReal {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (fun y => (v y : ℂ)) x := (show HasFDerivAt (fun y => (v y : ℂ)) _ x from
    Complex.ofRealCLM.hasFDerivAt.comp x hv.hasFDerivAt).differentiableAt

theorem wd_ofReal_comp {j : Fin n} {k : ℝ → ℝ} {v : V n → ℝ} {x : V n}
    (hk : DifferentiableAt ℝ k (v x)) (hv : DifferentiableAt ℝ v x) :
    wd n j (fun y => (k (v y) : ℂ)) x = ((deriv k (v x) : ℝ) : ℂ) * wd n j (fun y => (v y : ℂ)) x := by
  have hkv : DifferentiableAt ℝ (fun y => k (v y)) x := hk.comp x hv
  have e : ∀ w, fderiv ℝ (fun y => (k (v y) : ℂ)) x w =
      ((deriv k (v x) : ℝ) : ℂ) * (fderiv ℝ v x w : ℂ) := by
    intro w
    rw [fderiv_ofReal_apply hkv, (show HasFDerivAt (fun y => k (v y)) _ x from
      hk.hasDerivAt.comp_hasFDerivAt x hv.hasFDerivAt).fderiv]
    simp
  simp only [wd, e, fderiv_ofReal_apply hv]
  ring

theorem wdb_ofReal_comp {j : Fin n} {k : ℝ → ℝ} {v : V n → ℝ} {x : V n}
    (hk : DifferentiableAt ℝ k (v x)) (hv : DifferentiableAt ℝ v x) :
    wdb n j (fun y => (k (v y) : ℂ)) x = ((deriv k (v x) : ℝ) : ℂ) * wdb n j (fun y => (v y : ℂ)) x := by
  have hkv : DifferentiableAt ℝ (fun y => k (v y)) x := hk.comp x hv
  have e : ∀ w, fderiv ℝ (fun y => (k (v y) : ℂ)) x w =
      ((deriv k (v x) : ℝ) : ℂ) * (fderiv ℝ v x w : ℂ) := by
    intro w
    rw [fderiv_ofReal_apply hkv, (show HasFDerivAt (fun y => k (v y)) _ x from
      hk.hasDerivAt.comp_hasFDerivAt x hv.hasFDerivAt).fderiv]
    simp
  simp only [wdb, e, fderiv_ofReal_apply hv]
  ring

theorem wdb_ofReal {j : Fin n} {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    wdb n j (fun y => (v y : ℂ)) x = conj (wd n j (fun y => (v y : ℂ)) x) := by
  simp only [wdb, wd, fderiv_ofReal_apply hv]
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  all_goals ring

theorem fderiv_conj_apply {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) (w : V n) :
    fderiv ℝ (fun y => conj (f y)) x w = conj (fderiv ℝ f x w) := by
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt
  rw [(show HasFDerivAt (fun y => conj (f y)) _ x from h).fderiv]
  rfl

theorem differentiableAt_conj {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x := (show HasFDerivAt (fun y => conj (f y)) _ x from
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

theorem wd_conj {j : Fin n} {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    wd n j (fun y => conj (f y)) x = conj (wdb n j f x) := by
  simp only [wd, wdb, fderiv_conj_apply hf]
  simp [map_div₀, map_ofNat]
  all_goals ring

theorem wdb_conj {j : Fin n} {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    wdb n j (fun y => conj (f y)) x = conj (wd n j f x) := by
  simp only [wd, wdb, fderiv_conj_apply hf]
  simp [map_div₀, map_ofNat]
  all_goals ring

theorem fderiv_real_of_complex {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℂ f x) (w : V n) :
    fderiv ℝ f x w = fderiv ℂ f x w := by
  rw [(hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  rfl

theorem wdb_of_differentiableAt {j : Fin n} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℂ f x) : wdb n j f x = 0 := by
  rw [wdb, fderiv_real_of_complex hf, fderiv_real_of_complex hf,
    ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem wd_of_differentiableAt {j : Fin n} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℂ f x) : wd n j f x = fderiv ℂ f x (bas n j) := by
  rw [wd, fderiv_real_of_complex hf, fderiv_real_of_complex hf,
    ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem differentiableAt_wdb {j : Fin n} {f : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (wdb n j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun y => (fderiv ℝ f y (bas n j) +
    Complex.I * fderiv ℝ f y (Complex.I • bas n j)) / 2) x
  have h1 := hd.clm_apply (differentiableAt_const (bas n j))
  have h2 := (hd.clm_apply (differentiableAt_const (Complex.I • bas n j))).const_mul Complex.I
  refine ((h1.add h2).mul_const (2 : ℂ)⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv]

theorem differentiableAt_wd {j : Fin n} {f : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (wd n j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun y => (fderiv ℝ f y (bas n j) -
    Complex.I * fderiv ℝ f y (Complex.I • bas n j)) / 2) x
  have h1 := hd.clm_apply (differentiableAt_const (bas n j))
  have h2 := (hd.clm_apply (differentiableAt_const (Complex.I • bas n j))).const_mul Complex.I
  refine ((h1.sub h2).mul_const (2 : ℂ)⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv]

theorem differentiableAt_deriv_of_contDiffAt {k : ℝ → ℝ} {t : ℝ} (hk : ContDiffAt ℝ 2 k t) :
    DifferentiableAt ℝ (deriv k) t := by
  have hd : DifferentiableAt ℝ (fderiv ℝ k) t :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun s => fderiv ℝ k s 1) t
  exact hd.clm_apply (differentiableAt_const _)

theorem eventually_differentiableAt_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := (hf.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)

theorem leviNonnegOn_const (c : ℝ) (U : Set (V n)) : LeviNonnegOn n (fun _ => c) U := by
  intro x _ ξ
  have h0 : ∀ k, wdb n k (fun _ : V n => ((c : ℝ) : ℂ)) = fun _ => 0 := fun k => by
    funext y
    simp [wdb]
  simp [leviV, h0, wd]

end ReciprocityTheory.L2DbarEstimates

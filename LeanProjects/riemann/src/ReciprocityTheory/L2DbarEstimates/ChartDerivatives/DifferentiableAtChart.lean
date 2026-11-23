import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq

namespace ReciprocityTheory.L2DbarEstimates

namespace ChartWirtingerDerivatives

open Filter Topology Set
open scoped ContDiff

noncomputable section

theorem d_of_not_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M)
    (h : ¬ ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    d n z j f x = 0 := by
  unfold d
  exact dif_neg h

theorem db_of_not_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M)
    (h : ¬ ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    db n z j f x = 0 := by
  unfold db
  exact dif_neg h

theorem chart_mem_target {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M) (hx : x ∈ e.source) :
    z x ∈ e.target := by
  rw [he hx]
  exact e.map_source hx

theorem chart_symm_apply {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M) (hx : x ∈ e.source) :
    e.symm (z x) = x := by
  rw [he hx]
  exact e.left_inv hx

theorem Ck.differentiableAt_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → ℂ) (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (x : M) (hx : x ∈ e.source) :
    DifferentiableAt ℝ (f ∘ e.symm) (z x) :=
  ((hf e he).contDiffAt (e.open_target.mem_nhds (chart_mem_target n z e he x hx))).differentiableAt
    (by simp)

theorem wd_add' (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) : wd n j (fun w => g w + h w) y = wd n j g y + wd n j h y := by
  simp only [wd, fderiv_fun_add hg hh, ContinuousLinearMap.add_apply]
  ring

theorem wdb_add' (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) : wdb n j (fun w => g w + h w) y = wdb n j g y + wdb n j h y := by
  simp only [wdb, fderiv_fun_add hg hh, ContinuousLinearMap.add_apply]
  ring

theorem wd_const_mul' (n : ℕ) (j : Fin n) (c : ℂ) (g : V n → ℂ) (y : V n)
    (hg : DifferentiableAt ℝ g y) : wd n j (fun w => c * g w) y = c * wd n j g y := by
  simp only [wd, fderiv_const_mul hg c, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wdb_const_mul' (n : ℕ) (j : Fin n) (c : ℂ) (g : V n → ℂ) (y : V n)
    (hg : DifferentiableAt ℝ g y) : wdb n j (fun w => c * g w) y = c * wdb n j g y := by
  simp only [wdb, fderiv_const_mul hg c, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wd_mul' (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) :
    wd n j (fun w => g w * h w) y = wd n j g y * h y + g y * wd n j h y := by
  simp only [wd, fderiv_fun_mul hg hh, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wdb_mul' (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) :
    wdb n j (fun w => g w * h w) y = wdb n j g y * h y + g y * wdb n j h y := by
  simp only [wdb, fderiv_fun_mul hg hh, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wd_cexp' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y) :
    wd n j (fun w => Complex.exp (g w)) y = Complex.exp (g y) * wd n j g y := by
  simp only [wd, hg.hasFDerivAt.cexp.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wdb_cexp' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y) :
    wdb n j (fun w => Complex.exp (g w)) y = Complex.exp (g y) * wdb n j g y := by
  simp only [wdb, hg.hasFDerivAt.cexp.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem fderiv_conj' (n : ℕ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (starRingEnd ℂ) (g w)) y v = (starRingEnd ℂ) (fderiv ℝ g y v) := by
  have h : (fun w => (starRingEnd ℂ) (g w)) = Complex.conjLIE ∘ g := by
    funext w
    simp [Complex.conjLIE_apply]
  rw [h, LinearIsometryEquiv.comp_fderiv]
  simp

theorem wdb_conj' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wdb n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wd n j g y) := by
  simp only [wdb, wd, fderiv_conj', map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem wd_conj' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wd n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wdb n j g y) := by
  simp only [wdb, wd, fderiv_conj', map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem wd_comp_real' (n : ℕ) (j : Fin n) (k : ℝ → ℝ) (p : V n → ℝ) (y : V n)
    (hk : DifferentiableAt ℝ k (p y)) (hp : DifferentiableAt ℝ p y) :
    wd n j (fun w => ((k (p w) : ℝ) : ℂ)) y = ((deriv k (p y) : ℝ) : ℂ) * wd n j (fun w => (p w : ℂ)) y := by
  have h1 := Complex.ofRealCLM.hasFDerivAt.comp y (hk.hasDerivAt.comp_hasFDerivAt y hp.hasFDerivAt)
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y hp.hasFDerivAt
  have e1 : (fun w => ((k (p w) : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ (k ∘ p) := by
    funext w; simp
  have e2 : (fun w => ((p w : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ p := by
    funext w; simp
  rw [e1, e2]
  simp only [wd]
  rw [h1.fderiv, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem wdb_comp_real' (n : ℕ) (j : Fin n) (k : ℝ → ℝ) (p : V n → ℝ) (y : V n)
    (hk : DifferentiableAt ℝ k (p y)) (hp : DifferentiableAt ℝ p y) :
    wdb n j (fun w => ((k (p w) : ℝ) : ℂ)) y = ((deriv k (p y) : ℝ) : ℂ) * wdb n j (fun w => (p w : ℂ)) y := by
  have h1 := Complex.ofRealCLM.hasFDerivAt.comp y (hk.hasDerivAt.comp_hasFDerivAt y hp.hasFDerivAt)
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y hp.hasFDerivAt
  have e1 : (fun w => ((k (p w) : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ (k ∘ p) := by
    funext w; simp
  have e2 : (fun w => ((p w : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ p := by
    funext w; simp
  rw [e1, e2]
  simp only [wdb]
  rw [h1.fderiv, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem CkR.differentiableAt_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (ph : M → ℝ) (hph : CkR n z 1 ph) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (x : M) (hx : x ∈ e.source) :
    DifferentiableAt ℝ (fun w => ph (e.symm w)) (z x) := by
  have h := (Complex.reCLM.differentiable.differentiableAt).comp (z x)
    (Ck.differentiableAt_chart n z _ hph e he x hx)
  have e1 : (fun w => ph (e.symm w)) = ⇑Complex.reCLM ∘ (fun x => (ph x : ℂ)) ∘ e.symm := by
    funext w; simp
  rw [e1]
  exact h

theorem d_eq_zero_of_notMem {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hx : x ∉ tsupport f) : d n z j f x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨e, he, hxe⟩ := h
    rw [d_eq_wd n z e he j f x hxe]
    have h0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have ht := (e.continuousAt_symm (chart_mem_target n z e he x hxe)).tendsto
    rw [chart_symm_apply n z e he x hxe] at ht
    have h1 : (f ∘ e.symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
      filter_upwards [h0.comp_tendsto ht] with w hw
      simpa using hw
    rw [wd_congr n j _ _ _ h1]
    simp [wd]
  · exact d_of_not_chart n z j f x h

theorem db_eq_zero_of_notMem {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hx : x ∉ tsupport f) : db n z j f x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨e, he, hxe⟩ := h
    rw [db_eq_wdb n z e he j f x hxe]
    have h0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have ht := (e.continuousAt_symm (chart_mem_target n z e he x hxe)).tendsto
    rw [chart_symm_apply n z e he x hxe] at ht
    have h1 : (f ∘ e.symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
      filter_upwards [h0.comp_tendsto ht] with w hw
      simpa using hw
    rw [wdb_congr n j _ _ _ h1]
    simp [wdb]
  · exact db_of_not_chart n z j f x h

end

end ChartWirtingerDerivatives

end ReciprocityTheory.L2DbarEstimates

import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal

noncomputable section

theorem Smooth.const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) :
    Smooth n z (fun _ => c) := by
  exact fun _ _ => contDiffOn_const

theorem Smooth.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Smooth n z f) (hg : Smooth n z g) :
    Smooth n z (fun x => f x + g x) := by
  exact fun e he => (hf e he).add (hg e he)

theorem Smooth.sub {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Smooth n z f) (hg : Smooth n z g) :
    Smooth n z (fun x => f x - g x) := by
  exact fun e he => (hf e he).sub (hg e he)

theorem Smooth.mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Smooth n z f) (hg : Smooth n z g) :
    Smooth n z (fun x => f x * g x) := by
  exact fun e he => (hf e he).mul (hg e he)

theorem Smooth.conj {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    Smooth n z (fun x => (starRingEnd ℂ) (f x)) := by
  intro e he
  have h1 := Complex.conjCLE.contDiff.comp_contDiffOn (hf e he)
  refine h1.congr (fun w _ => ?_)
  simp

theorem Smooth.cexp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    Smooth n z (fun x => Complex.exp (f x)) := by
  intro e he
  exact Complex.contDiff_exp.comp_contDiffOn (hf e he)

theorem Smooth.re {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    SmoothR n z (fun x => (f x).re) := by
  intro e he
  have h1 := (Complex.ofRealCLM.comp Complex.reCLM).contDiff.comp_contDiffOn (hf e he)
  refine h1.congr (fun w _ => ?_)
  simp

theorem Smooth.normSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    SmoothR n z (fun x => ‖f x‖ ^ 2) := by
  intro e he
  have h1 := (Smooth.mul n z f _ hf (Smooth.conj n z f hf)) e he
  refine h1.congr (fun w _ => ?_)
  simp only [Function.comp_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem SmoothR.comp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (f : M → ℝ) (hf : SmoothR n z f) :
    SmoothR n z (fun x => k (f x)) := by
  intro e he
  have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf e he)
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn (hk.comp_contDiffOn h1)
  refine h2.congr (fun w _ => ?_)
  simp

theorem SmoothR.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ) (hf : SmoothR n z f) (hg : SmoothR n z g) :
    SmoothR n z (fun x => f x + g x) := by
  have h1 := Smooth.add n z _ _ hf hg
  unfold SmoothR
  simpa using h1

theorem SmoothR.mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ) (hf : SmoothR n z f) (hg : SmoothR n z g) :
    SmoothR n z (fun x => f x * g x) := by
  have h1 := Smooth.mul n z _ _ hf hg
  unfold SmoothR
  simpa using h1

theorem Holo.const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) :
    Holo n z (fun _ => c) := by
  exact fun _ _ => differentiableOn_const _

theorem Holo.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Holo n z f) (hg : Holo n z g) :
    Holo n z (fun x => f x + g x) := by
  exact fun e he => (hf e he).add (hg e he)

theorem Holo.sub {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Holo n z f) (hg : Holo n z g) :
    Holo n z (fun x => f x - g x) := by
  exact fun e he => (hf e he).sub (hg e he)

theorem Holo.mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Holo n z f) (hg : Holo n z g) :
    Holo n z (fun x => f x * g x) := by
  exact fun e he => (hf e he).mul (hg e he)

theorem Ck.const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (c : ℂ) :
    Ck n z k (fun _ => c) := by
  exact fun _ _ => contDiffOn_const

theorem Ck.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℂ) (hf : Ck n z k f) (hg : Ck n z k g) :
    Ck n z k (fun x => f x + g x) := by
  exact fun e he => (hf e he).add (hg e he)

theorem Ck.sub {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℂ) (hf : Ck n z k f) (hg : Ck n z k g) :
    Ck n z k (fun x => f x - g x) := by
  exact fun e he => (hf e he).sub (hg e he)

theorem Ck.mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℂ) (hf : Ck n z k f) (hg : Ck n z k g) :
    Ck n z k (fun x => f x * g x) := by
  exact fun e he => (hf e he).mul (hg e he)

theorem Ck.conj {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) :
    Ck n z k (fun x => (starRingEnd ℂ) (f x)) := by
  intro e he
  have h1 := Complex.conjCLE.contDiff.comp_contDiffOn (hf e he)
  refine h1.congr (fun w _ => ?_)
  simp

theorem Ck.cexp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) :
    Ck n z k (fun x => Complex.exp (f x)) := by
  intro e he
  exact Complex.contDiff_exp.comp_contDiffOn (hf e he)

theorem Ck.re {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) :
    CkR n z k (fun x => (f x).re) := by
  intro e he
  have h1 := (Complex.ofRealCLM.comp Complex.reCLM).contDiff.comp_contDiffOn (hf e he)
  refine h1.congr (fun w _ => ?_)
  simp

theorem Ck.normSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) :
    CkR n z k (fun x => ‖f x‖ ^ 2) := by
  intro e he
  have h1 := (Ck.mul n z k f _ hf (Ck.conj n z k f hf)) e he
  refine h1.congr (fun w _ => ?_)
  simp only [Function.comp_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem CkR.comp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (f : M → ℝ) (hf : CkR n z k f) :
    CkR n z k (fun x => φ (f x)) := by
  intro e he
  have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf e he)
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((hφ.of_le (by exact_mod_cast le_top)).comp_contDiffOn h1)
  refine h2.congr (fun w _ => ?_)
  simp

theorem CkR.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℝ) (hf : CkR n z k f) (hg : CkR n z k g) :
    CkR n z k (fun x => f x + g x) := by
  have h1 := Ck.add n z k _ _ hf hg
  unfold CkR
  simpa using h1

theorem CkR.mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℝ) (hf : CkR n z k f) (hg : CkR n z k g) :
    CkR n z k (fun x => f x * g x) := by
  have h1 := Ck.mul n z k _ _ hf hg
  unfold CkR
  simpa using h1

theorem CkR.ofReal {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℝ) (hf : CkR n z k f) :
    Ck n z k (fun x => (f x : ℂ)) := by
  exact hf

private theorem isChart_choose_and_symm_apply {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (x : M)
    (h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    IsChart n z (Classical.choose h) ∧ z x ∈ (Classical.choose h).target ∧
      (Classical.choose h).symm (z x) = x := by
  obtain ⟨he, hx⟩ := Classical.choose_spec h
  refine ⟨he, ?_, ?_⟩
  · rw [he hx]; exact (Classical.choose h).map_source hx
  · rw [he hx]; exact (Classical.choose h).left_inv hx

private theorem d_eq_wd_comp_chosen_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    d n z j f x = wd n j (f ∘ (Classical.choose h).symm) (z x) := by
  simp only [d, dif_pos h]

private theorem db_eq_wdb_comp_chosen_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    db n z j f x = wdb n j (f ∘ (Classical.choose h).symm) (z x) := by
  simp only [db, dif_pos h]

private theorem differentiableAt_comp_chart_symm_of_mem_target {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (w : V n)
    (hw : w ∈ e.target) : DifferentiableAt ℝ (f ∘ e.symm) w :=
  ((hf e he).differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hw)

private theorem wd_wdb_add_and_mul (n : ℕ) (j : Fin n) {F G : V n → ℂ} {w : V n}
    (hF : DifferentiableAt ℝ F w) (hG : DifferentiableAt ℝ G w) :
    wd n j (fun y => F y + G y) w = wd n j F w + wd n j G w ∧
    wdb n j (fun y => F y + G y) w = wdb n j F w + wdb n j G w ∧
    wd n j (fun y => F y * G y) w = wd n j F w * G w + F w * wd n j G w ∧
    wdb n j (fun y => F y * G y) w = wdb n j F w * G w + F w * wdb n j G w := by
  have h1 : HasFDerivAt (fun y => F y + G y) _ w := hF.hasFDerivAt.add hG.hasFDerivAt
  have h2 : HasFDerivAt (fun y => F y * G y) _ w := hF.hasFDerivAt.mul hG.hasFDerivAt
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring

private theorem wd_wdb_const_mul (n : ℕ) (j : Fin n) (c : ℂ) {F : V n → ℂ} {w : V n}
    (hF : DifferentiableAt ℝ F w) :
    wd n j (fun y => c * F y) w = c * wd n j F w ∧
    wdb n j (fun y => c * F y) w = c * wdb n j F w := by
  have h1 : HasFDerivAt (fun y => c * F y) _ w := hF.hasFDerivAt.const_mul c
  refine ⟨?_, ?_⟩ <;>
    simp only [wd, wdb, h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring

private theorem wd_wdb_cexp (n : ℕ) (j : Fin n) {F : V n → ℂ} {w : V n}
    (hF : DifferentiableAt ℝ F w) :
    wd n j (fun y => Complex.exp (F y)) w = Complex.exp (F w) * wd n j F w ∧
    wdb n j (fun y => Complex.exp (F y)) w = Complex.exp (F w) * wdb n j F w := by
  have h1 := hF.hasFDerivAt.cexp
  refine ⟨?_, ?_⟩ <;>
    simp only [wd, wdb, h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring

private theorem wdb_conj_eq_conj_wd_and_wd_conj (n : ℕ) (j : Fin n) (F : V n → ℂ) (w : V n) :
    wdb n j (fun y => (starRingEnd ℂ) (F y)) w = (starRingEnd ℂ) (wd n j F w) ∧
    wd n j (fun y => (starRingEnd ℂ) (F y)) w = (starRingEnd ℂ) (wdb n j F w) := by
  have h1 : (fun y => (starRingEnd ℂ) (F y)) = Complex.conjCLE ∘ F := by funext y; simp
  have h2 : ∀ v, fderiv ℝ (fun y => (starRingEnd ℂ) (F y)) w v = (starRingEnd ℂ) (fderiv ℝ F w v) := by
    intro v; rw [h1, Complex.conjCLE.comp_fderiv]; simp
  refine ⟨?_, ?_⟩ <;>
    simp only [wd, wdb, h2, map_div₀, map_sub, map_add, map_mul, Complex.conj_I, map_ofNat] <;> ring

private theorem wd_wdb_ofReal_comp_real_chain (n : ℕ) (j : Fin n) (k : ℝ → ℝ) (hk : Differentiable ℝ k)
    (P : V n → ℝ) (w : V n) (hP : DifferentiableAt ℝ P w) :
    wd n j (fun y => ((k (P y) : ℝ) : ℂ)) w = ((deriv k (P w) : ℝ) : ℂ) * wd n j (fun y => ((P y : ℝ) : ℂ)) w ∧
    wdb n j (fun y => ((k (P y) : ℝ) : ℂ)) w = ((deriv k (P w) : ℝ) : ℂ) * wdb n j (fun y => ((P y : ℝ) : ℂ)) w := by
  have h1 : HasFDerivAt (fun y => ((P y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ P w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hP.hasFDerivAt
  have h2 : HasFDerivAt (fun y => ((k (P y) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (deriv k (P w) • fderiv ℝ P w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w ((hk (P w)).hasDerivAt.comp_hasFDerivAt w hP.hasFDerivAt)
  refine ⟨?_, ?_⟩ <;>
    simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul] <;> ring

theorem d_add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y + g y) x = d n z j f x + d n z j g x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [d_eq_wd_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j f x h, d_eq_wd_comp_chosen_chart_symm n z j g x h]
    exact (wd_wdb_add_and_mul n j (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht) (differentiableAt_comp_chart_symm_of_mem_target n z g hg _ he _ ht)).1
  · simp [d, db, h]

theorem db_add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    db n z j (fun y => f y + g y) x = db n z j f x + db n z j g x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j f x h, db_eq_wdb_comp_chosen_chart_symm n z j g x h]
    exact (wd_wdb_add_and_mul n j (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht) (differentiableAt_comp_chart_symm_of_mem_target n z g hg _ he _ ht)).2.1
  · simp [d, db, h]

theorem d_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    d n z j (fun y => c * f y) x = c * d n z j f x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [d_eq_wd_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j f x h]
    exact (wd_wdb_const_mul n j c (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht)).1
  · simp [d, db, h]

theorem db_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    db n z j (fun y => c * f y) x = c * db n z j f x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j f x h]
    exact (wd_wdb_const_mul n j c (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht)).2
  · simp [d, db, h]

theorem d_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y * g y) x = d n z j f x * g x + f x * d n z j g x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    have hx' : ∀ F : M → ℂ, (F ∘ (Classical.choose h).symm) (z x) = F x := fun F => by simp [hsx]
    rw [d_eq_wd_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j f x h, d_eq_wd_comp_chosen_chart_symm n z j g x h]
    refine (wd_wdb_add_and_mul n j (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht) (differentiableAt_comp_chart_symm_of_mem_target n z g hg _ he _ ht)).2.2.1.trans ?_
    rw [hx' f, hx' g]
  · simp [d, db, h]

theorem db_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    db n z j (fun y => f y * g y) x = db n z j f x * g x + f x * db n z j g x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    have hx' : ∀ F : M → ℂ, (F ∘ (Classical.choose h).symm) (z x) = F x := fun F => by simp [hsx]
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j f x h, db_eq_wdb_comp_chosen_chart_symm n z j g x h]
    refine (wd_wdb_add_and_mul n j (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht) (differentiableAt_comp_chart_symm_of_mem_target n z g hg _ he _ ht)).2.2.2.trans ?_
    rw [hx' f, hx' g]
  · simp [d, db, h]

theorem d_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) (j : Fin n) (x : M) :
    d n z j (fun _ => c) x = 0 := by
  simp [d, wd, Function.comp_def]

theorem db_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) (j : Fin n) (x : M) :
    db n z j (fun _ => c) x = 0 := by
  simp [db, wdb, Function.comp_def]

theorem db_conj {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (j : Fin n) (x : M) :
    db n z j (fun y => (starRingEnd ℂ) (f y)) x = (starRingEnd ℂ) (d n z j f x) := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j f x h]
    exact (wdb_conj_eq_conj_wd_and_wd_conj n j (f ∘ (Classical.choose h).symm) (z x)).1
  · simp [d, db, h]

theorem d_conj {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (j : Fin n) (x : M) :
    d n z j (fun y => (starRingEnd ℂ) (f y)) x = (starRingEnd ℂ) (db n z j f x) := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [d_eq_wd_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j f x h]
    exact (wdb_conj_eq_conj_wd_and_wd_conj n j (f ∘ (Classical.choose h).symm) (z x)).2
  · simp [d, db, h]

theorem db_ofReal {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (x : M) :
    db n z j (fun y => (ph y : ℂ)) x = (starRingEnd ℂ) (d n z j (fun y => (ph y : ℂ)) x) := by
  have h1 := db_conj n z (fun y => (ph y : ℂ)) j x
  simpa using h1

theorem d_cexp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    d n z j (fun y => Complex.exp (f y)) x = Complex.exp (f x) * d n z j f x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    have hx' : ∀ F : M → ℂ, (F ∘ (Classical.choose h).symm) (z x) = F x := fun F => by simp [hsx]
    rw [d_eq_wd_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j f x h]
    refine (wd_wdb_cexp n j (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht)).1.trans ?_
    rw [hx' f]
  · simp [d, db, h]

theorem db_cexp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    db n z j (fun y => Complex.exp (f y)) x = Complex.exp (f x) * db n z j f x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    have hx' : ∀ F : M → ℂ, (F ∘ (Classical.choose h).symm) (z x) = F x := fun F => by simp [hsx]
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j f x h]
    refine (wd_wdb_cexp n j (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht)).2.trans ?_
    rw [hx' f]
  · simp [d, db, h]

theorem d_comp_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n) (x : M) :
    d n z j (fun y => (k (ph y) : ℂ)) x = ((deriv k (ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [d_eq_wd_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j _ x h]
    have hP : DifferentiableAt ℝ (ph ∘ (Classical.choose h).symm) (z x) := by
      have h1 := ((Complex.reCLM.contDiff.comp_contDiffOn (hph _ he)).differentiableOn
        (by simp)).differentiableAt ((Classical.choose h).open_target.mem_nhds ht)
      exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp)
    refine (wd_wdb_ofReal_comp_real_chain n j k (hk.differentiable (by simp)) _ _ hP).1.trans ?_
    simp [hsx, Function.comp_def]
  · simp [d, db, h]

theorem db_comp_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n) (x : M) :
    db n z j (fun y => (k (ph y) : ℂ)) x = ((deriv k (ph x) : ℝ) : ℂ) * db n z j (fun y => (ph y : ℂ)) x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j _ x h]
    have hP : DifferentiableAt ℝ (ph ∘ (Classical.choose h).symm) (z x) := by
      have h1 := ((Complex.reCLM.contDiff.comp_contDiffOn (hph _ he)).differentiableOn
        (by simp)).differentiableAt ((Classical.choose h).open_target.mem_nhds ht)
      exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp)
    refine (wd_wdb_ofReal_comp_real_chain n j k (hk.differentiable (by simp)) _ _ hP).2.trans ?_
    simp [hsx, Function.comp_def]
  · simp [d, db, h]

theorem tsupport_d_subset {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (f : M → ℂ) :
    tsupport (d n z j f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra hxs
  rw [Function.mem_support] at hx
  apply hx
  have hf0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [d_eq_wd_comp_chosen_chart_symm n z j f x h]
    have h2 : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
      have hc := (Classical.choose h).continuousAt_symm ht
      rw [← hsx] at hf0
      exact hc.eventually hf0
    simp only [wd, h2.fderiv_eq]
    simp
  · simp [d, h]

theorem tsupport_db_subset {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (f : M → ℂ) :
    tsupport (db n z j f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra hxs
  rw [Function.mem_support] at hx
  apply hx
  have hf0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j f x h]
    have h2 : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
      have hc := (Classical.choose h).continuousAt_symm ht
      rw [← hsx] at hf0
      exact hc.eventually hf0
    simp only [wdb, h2.fderiv_eq]
    simp
  · simp [db, h]

end

end ReciprocityTheory.L2DbarEstimates

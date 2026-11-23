import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

theorem comm_fderiv_apply {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (u : V n) :
    HasFDerivAt (fun y' => fderiv ℝ g y' u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ g) y)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) y := h1.differentiableAt one_ne_zero
  exact (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp y hd.hasFDerivAt

theorem comm_fderiv_wd {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j : Fin n) (v : V n) :
    fderiv ℝ (wd n j g) y v = (fderiv ℝ (fderiv ℝ g) y v (bas n j)
      - Complex.I * fderiv ℝ (fderiv ℝ g) y v (Complex.I • bas n j)) * (2 : ℂ)⁻¹ := by
  have hA := comm_fderiv_apply g y hg (bas n j)
  have hB := comm_fderiv_apply g y hg (Complex.I • bas n j)
  have hW : HasFDerivAt (fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      - Complex.I • fderiv ℝ g y' (Complex.I • bas n j))) _ y := (hA.sub (hB.const_smul Complex.I)).const_smul (2 : ℂ)⁻¹
  have hfun : wd n j g = fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      - Complex.I • fderiv ℝ g y' (Complex.I • bas n j)) := by
    funext y'
    simp only [wd, smul_eq_mul]
    ring
  rw [hfun, hW.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem comm_fderiv_wdb {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j : Fin n) (v : V n) :
    fderiv ℝ (wdb n j g) y v = (fderiv ℝ (fderiv ℝ g) y v (bas n j)
      + Complex.I * fderiv ℝ (fderiv ℝ g) y v (Complex.I • bas n j)) * (2 : ℂ)⁻¹ := by
  have hA := comm_fderiv_apply g y hg (bas n j)
  have hB := comm_fderiv_apply g y hg (Complex.I • bas n j)
  have hW : HasFDerivAt (fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      + Complex.I • fderiv ℝ g y' (Complex.I • bas n j))) _ y := (hA.add (hB.const_smul Complex.I)).const_smul (2 : ℂ)⁻¹
  have hfun : wdb n j g = fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      + Complex.I • fderiv ℝ g y' (Complex.I • bas n j)) := by
    funext y'
    simp only [wdb, smul_eq_mul]
    ring
  rw [hfun, hW.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem comm_wd_wdb {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wd n j (wdb n k g) y = wdb n k (wd n j g) y := by
  have S := hg.isSymmSndFDerivAt (by simp)
  have e1 : wd n j (wdb n k g) y = (fderiv ℝ (wdb n k g) y (bas n j)
      - Complex.I * fderiv ℝ (wdb n k g) y (Complex.I • bas n j)) / 2 := rfl
  have e2 : wdb n k (wd n j g) y = (fderiv ℝ (wd n j g) y (bas n k)
      + Complex.I * fderiv ℝ (wd n j g) y (Complex.I • bas n k)) / 2 := rfl
  rw [e1, e2, comm_fderiv_wdb g y hg k (bas n j), comm_fderiv_wdb g y hg k (Complex.I • bas n j),
    comm_fderiv_wd g y hg j (bas n k), comm_fderiv_wd g y hg j (Complex.I • bas n k),
    S (bas n k) (bas n j), S (bas n k) (Complex.I • bas n j),
    S (Complex.I • bas n k) (bas n j), S (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

theorem comm_wd_wd {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wd n j (wd n k g) y = wd n k (wd n j g) y := by
  have S := hg.isSymmSndFDerivAt (by simp)
  have e1 : wd n j (wd n k g) y = (fderiv ℝ (wd n k g) y (bas n j)
      - Complex.I * fderiv ℝ (wd n k g) y (Complex.I • bas n j)) / 2 := rfl
  have e2 : wd n k (wd n j g) y = (fderiv ℝ (wd n j g) y (bas n k)
      - Complex.I * fderiv ℝ (wd n j g) y (Complex.I • bas n k)) / 2 := rfl
  rw [e1, e2, comm_fderiv_wd g y hg k (bas n j), comm_fderiv_wd g y hg k (Complex.I • bas n j),
    comm_fderiv_wd g y hg j (bas n k), comm_fderiv_wd g y hg j (Complex.I • bas n k),
    S (bas n k) (bas n j), S (bas n k) (Complex.I • bas n j),
    S (Complex.I • bas n k) (bas n j), S (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

theorem comm_wdb_wdb {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wdb n j (wdb n k g) y = wdb n k (wdb n j g) y := by
  have S := hg.isSymmSndFDerivAt (by simp)
  have e1 : wdb n j (wdb n k g) y = (fderiv ℝ (wdb n k g) y (bas n j)
      + Complex.I * fderiv ℝ (wdb n k g) y (Complex.I • bas n j)) / 2 := rfl
  have e2 : wdb n k (wdb n j g) y = (fderiv ℝ (wdb n j g) y (bas n k)
      + Complex.I * fderiv ℝ (wdb n j g) y (Complex.I • bas n k)) / 2 := rfl
  rw [e1, e2, comm_fderiv_wdb g y hg k (bas n j), comm_fderiv_wdb g y hg k (Complex.I • bas n j),
    comm_fderiv_wdb g y hg j (bas n k), comm_fderiv_wdb g y hg j (Complex.I • bas n k),
    S (bas n k) (bas n j), S (bas n k) (Complex.I • bas n j),
    S (Complex.I • bas n k) (bas n j), S (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

private theorem chart_symm_eventuallyEq_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e') (y : M)
    (hy : y ∈ e.source) (hy' : y ∈ e'.source) : (e'.symm : V n → M) =ᶠ[𝓝 (z y)] e.symm := by
  have hzy : z y = e' y := he' hy'
  have ht : z y ∈ e'.target := by rw [hzy]; exact e'.map_source hy'
  have hc : ContinuousAt e'.symm (z y) := e'.continuousAt_symm ht
  have hs : e.source ∈ 𝓝 (e'.symm (z y)) := by
    rw [hzy, e'.left_inv hy']; exact e.open_source.mem_nhds hy
  filter_upwards [e'.open_target.mem_nhds ht, hc hs] with w hw hw2
  have h1 : e (e'.symm w) = w := by
    rw [← he hw2, he' (e'.map_target hw), e'.right_inv hw]
  calc e'.symm w = e.symm (e (e'.symm w)) := (e.left_inv hw2).symm
    _ = e.symm w := by rw [h1]

private theorem d_apply_eq_wd_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : d n z j f y = wd n j (f ∘ e.symm) (z y) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  have hg : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z y)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_symm n z e _ he (Classical.choose_spec h).1 y hy
      (Classical.choose_spec h).2).fun_comp f
  simp only [d, dif_pos h, wd, hg.fderiv_eq]

private theorem db_apply_eq_wdb_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : db n z j f y = wdb n j (f ∘ e.symm) (z y) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  have hg : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z y)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_symm n z e _ he (Classical.choose_spec h).1 y hy
      (Classical.choose_spec h).2).fun_comp f
  simp only [db, dif_pos h, wdb, hg.fderiv_eq]

theorem comm_chart_setup {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 2 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) :
    z x ∈ e.target ∧ ContDiffAt ℝ 2 (f ∘ e.symm) (z x) ∧
      (∀ j, (d n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wd n j (f ∘ e.symm)) ∧
      (∀ j, (db n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wdb n j (f ∘ e.symm)) := by
  have h1 : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  refine ⟨h1, ?_, ?_, ?_⟩
  · have h2 := (hf e he).contDiffAt (e.open_target.mem_nhds h1)
    exact_mod_cast h2
  · intro j
    filter_upwards [e.open_target.mem_nhds h1] with w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    show d n z j f (e.symm w) = wd n j (f ∘ e.symm) w
    rw [d_apply_eq_wd_comp_chart_symm n z j f e he _ hs, he hs, e.right_inv hw]
  · intro j
    filter_upwards [e.open_target.mem_nhds h1] with w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    show db n z j f (e.symm w) = wdb n j (f ∘ e.symm) w
    rw [db_apply_eq_wdb_comp_chart_symm n z j f e he _ hs, he hs, e.right_inv hw]

private theorem wd_congr_of_eventuallyEq' (n : ℕ) (j : Fin n) {g h : V n → ℂ} {w : V n}
    (hgh : g =ᶠ[𝓝 w] h) : wd n j g w = wd n j h w := by
  simp only [wd, hgh.fderiv_eq]

private theorem wdb_congr_of_eventuallyEq (n : ℕ) (j : Fin n) {g h : V n → ℂ} {w : V n}
    (hgh : g =ᶠ[𝓝 w] h) : wdb n j g w = wdb n j h w := by
  simp only [wdb, hgh.fderiv_eq]

theorem d_db_comm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Ck n z 2 f) (j k : Fin n) (x : M) :
    d n z j (db n z k f) x = db n z k (d n z j f) x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨e, he, hx⟩ := h
    obtain ⟨_, h2, h3, h4⟩ := comm_chart_setup n z f hf e he x hx
    rw [d_apply_eq_wd_comp_chart_symm n z j _ e he x hx, db_apply_eq_wdb_comp_chart_symm n z k _ e he x hx,
      wd_congr_of_eventuallyEq' n j (h4 k), wdb_congr_of_eventuallyEq n k (h3 j)]
    exact comm_wd_wdb _ _ h2 j k
  · simp [d, db, h]

theorem levi_add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ps : M → ℝ) (hph : CkR n z 2 ph) (hps : CkR n z 2 ps) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ph y + ps y) x ξ = Levi n z ph x ξ + Levi n z ps x ξ := by
  have hph1 : Ck n z 1 (fun y => (ph y : ℂ)) := fun e he => (hph e he).of_le (by norm_num)
  have hps1 : Ck n z 1 (fun y => (ps y : ℂ)) := fun e he => (hps e he).of_le (by norm_num)
  have e1 : (fun y => ((ph y + ps y : ℝ) : ℂ)) = fun y => (ph y : ℂ) + (ps y : ℂ) := by
    funext y; exact Complex.ofReal_add _ _
  have h1 : ∀ k, db n z k (fun y => ((ph y + ps y : ℝ) : ℂ)) =
      fun y => db n z k (fun y => (ph y : ℂ)) y + db n z k (fun y => (ps y : ℂ)) y := by
    intro k; funext y; rw [e1]; exact db_add n z _ _ hph1 hps1 k y
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((ph y + ps y : ℝ) : ℂ))) x =
      d n z j (db n z k (fun y => (ph y : ℂ))) x + d n z j (db n z k (fun y => (ps y : ℂ))) x := by
    intro j k; rw [h1 k]; exact d_add n z _ _ (Ck.db n z 1 k _ hph) (Ck.db n z 1 k _ hps) j x
  simp only [Levi, h2, add_mul, Finset.sum_add_distrib]

theorem levi_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) (ph : M → ℝ) (hph : CkR n z 2 ph) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => c * ph y) x ξ = (c : ℂ) * Levi n z ph x ξ := by
  have hph1 : Ck n z 1 (fun y => (ph y : ℂ)) := fun e he => (hph e he).of_le (by norm_num)
  have e1 : (fun y => ((c * ph y : ℝ) : ℂ)) = fun y => (c : ℂ) * (ph y : ℂ) := by
    funext y; exact Complex.ofReal_mul _ _
  have h1 : ∀ k, db n z k (fun y => ((c * ph y : ℝ) : ℂ)) =
      fun y => (c : ℂ) * db n z k (fun y => (ph y : ℂ)) y := by
    intro k; funext y; rw [e1]; exact db_const_mul n z _ _ hph1 k y
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((c * ph y : ℝ) : ℂ))) x =
      (c : ℂ) * d n z j (db n z k (fun y => (ph y : ℂ))) x := by
    intro j k; rw [h1 k]; exact d_const_mul n z _ _ (Ck.db n z 1 k _ hph) j x
  simp only [Levi, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem levi_normSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ) (hg : Holo n z g) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ‖g y‖ ^ 2) x ξ = ((‖dDot n z g x ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hs : Smooth n z g := Holo.smooth n z g hg
  have hC : ∀ k, Ck n z k g := fun k => Smooth.ck n z k g hs
  have hconj : ∀ k, Ck n z k (fun y => (starRingEnd ℂ) (g y)) := fun k => Ck.conj n z k g (hC k)
  have e0 : (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) = fun y => g y * (starRingEnd ℂ) (g y) := by
    funext y; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdb : ∀ k, db n z k (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) =
      fun y => g y * (starRingEnd ℂ) (d n z k g y) := by
    intro k; funext y
    rw [e0, db_mul n z _ _ (hC 1) (hconj 1) k y, Holo.db_eq_zero n z g hg k y, db_conj]
    ring
  have hdb0 : ∀ j, db n z j g = fun _ => 0 := fun j => funext (Holo.db_eq_zero n z g hg j)
  have hd : ∀ j k, d n z j (db n z k (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ))) x =
      d n z j g x * (starRingEnd ℂ) (d n z k g x) := by
    intro j k
    rw [hdb k, d_mul n z _ _ (hC 1) (Ck.conj n z 1 _ (Ck.d n z 1 k g (hC _))) j x, d_conj,
      ← d_db_comm n z g (hC 2) k j x, hdb0 j, d_const]
    simp
  simp only [Levi, hd, dDot]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [map_mul]
  ring

end

end ReciprocityTheory.L2DbarEstimates

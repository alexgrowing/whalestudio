import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology Set
open scoped ContDiff

noncomputable section

theorem exists_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (x : M) :
    ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
  obtain ⟨e, hx, he⟩ := hz x
  exact ⟨e, fun y _ => congrFun he y, hx⟩

theorem chart_z_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : V n) (hy : y ∈ e.target) :
    z (e.symm y) = y := by
  rw [he (e.map_target hy), e.right_inv hy]

theorem chart_symm_eventuallyEq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e₁ e₂ : OpenPartialHomeomorph M (V n)) (h₁ : IsChart n z e₁) (h₂ : IsChart n z e₂)
    (x : M) (hx₁ : x ∈ e₁.source) (hx₂ : x ∈ e₂.source) :
    (e₁.symm : V n → M) =ᶠ[𝓝 (z x)] e₂.symm := by
  have h1 : z x = e₁ x := h₁ hx₁
  have h2 : z x = e₂ x := h₂ hx₂
  have t1 : ∀ᶠ y in 𝓝 (z x), e₁.symm y ∈ e₂.source := by
    rw [h1]
    refine (e₁.continuousAt_symm (e₁.map_source hx₁)).preimage_mem_nhds ?_
    rw [e₁.left_inv hx₁]
    exact e₂.open_source.mem_nhds hx₂
  have t2 : ∀ᶠ y in 𝓝 (z x), y ∈ e₁.target := by
    rw [h1]; exact e₁.open_target.mem_nhds (e₁.map_source hx₁)
  have t3 : ∀ᶠ y in 𝓝 (z x), y ∈ e₂.target := by
    rw [h2]; exact e₂.open_target.mem_nhds (e₂.map_source hx₂)
  filter_upwards [t1, t2, t3] with y hy1 hy2 hy3
  apply e₂.injOn hy1 (e₂.map_target hy3)
  rw [e₂.right_inv hy3, ← h₂ hy1, h₁ (e₁.map_target hy2), e₁.right_inv hy2]

theorem wd_congr (n : ℕ) (j : Fin n) (g₁ g₂ : V n → ℂ) (y : V n) (h : g₁ =ᶠ[𝓝 y] g₂) :
    wd n j g₁ y = wd n j g₂ y := by
  simp only [wd, h.fderiv_eq]

theorem wdb_congr (n : ℕ) (j : Fin n) (g₁ g₂ : V n → ℂ) (y : V n) (h : g₁ =ᶠ[𝓝 y] g₂) :
    wdb n j g₁ y = wdb n j g₂ y := by
  simp only [wdb, h.fderiv_eq]

theorem d_eq_wd {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ) (x : M)
    (hx : x ∈ e.source) :
    d n z j f x = wd n j (f ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold d
  rw [dif_pos h]
  apply wd_congr
  have := chart_symm_eventuallyEq n z _ e (Classical.choose_spec h).1 he x (Classical.choose_spec h).2 hx
  filter_upwards [this] with y hy
  simp only [Function.comp_apply, hy]

theorem db_eq_wdb {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ) (x : M)
    (hx : x ∈ e.source) :
    db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold db
  rw [dif_pos h]
  apply wdb_congr
  have := chart_symm_eventuallyEq n z _ e (Classical.choose_spec h).1 he x (Classical.choose_spec h).2 hx
  filter_upwards [this] with y hy
  simp only [Function.comp_apply, hy]

theorem d_comp_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ)
    (y : V n) (hy : y ∈ e.target) :
    d n z j f (e.symm y) = wd n j (f ∘ e.symm) y := by
  rw [d_eq_wd n z e he j f (e.symm y) (e.map_target hy), chart_z_symm n z e he y hy]

theorem db_comp_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ)
    (y : V n) (hy : y ∈ e.target) :
    db n z j f (e.symm y) = wdb n j (f ∘ e.symm) y := by
  rw [db_eq_wdb n z e he j f (e.symm y) (e.map_target hy), chart_z_symm n z e he y hy]

theorem levi_eq_leviV {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (ph : M → ℝ) (x : M)
    (hx : x ∈ e.source) (ξ : Fin n → ℂ) :
    Levi n z ph x ξ = leviV n (fun y => (ph (e.symm y) : ℂ)) (z x) ξ := by
  unfold Levi leviV
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [d_eq_wd n z e he j _ x hx]
  have hT : e.target ∈ 𝓝 (z x) := by
    rw [he hx]; exact e.open_target.mem_nhds (e.map_source hx)
  have key : wd n j (db n z k (fun y => (ph y : ℂ)) ∘ e.symm) (z x) =
      wd n j (wdb n k (fun y => (ph (e.symm y) : ℂ))) (z x) := by
    apply wd_congr
    filter_upwards [hT] with y hy
    exact db_comp_symm n z e he k _ y hy
  rw [key]

theorem Smooth.continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Smooth n z f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
    (hf e he).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  refine (h1.comp (e.continuousAt hx)).congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.left_inv hy]

theorem Holo.smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Holo n z f) : Smooth n z f := by
  intro e he
  exact (contDiffOn_of_differentiableOn n _ _ e.open_target (hf e he)).restrict_scalars ℝ

private theorem contDiffOn_fderiv_apply_of_contDiffOn_infty {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (v : V n) : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) U :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const

private theorem contDiffOn_wd_wdb_of_contDiffOn_infty {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) :
    ContDiffOn ℝ ∞ (wd n j g) U ∧ ContDiffOn ℝ ∞ (wdb n j g) U := by
  constructor
  · unfold wd
    exact ((contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _).sub
      (contDiffOn_const.mul (contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _))).div_const 2
  · unfold wdb
    exact ((contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _).add
      (contDiffOn_const.mul (contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _))).div_const 2

theorem Smooth.d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (hf : Smooth n z f) : Smooth n z (d n z j f) := by
  intro e he
  exact (contDiffOn_wd_wdb_of_contDiffOn_infty e.open_target (hf e he) j).1.congr fun y hy => d_comp_symm n z e he j f y hy

theorem Smooth.db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (hf : Smooth n z f) : Smooth n z (db n z j f) := by
  intro e he
  exact (contDiffOn_wd_wdb_of_contDiffOn_infty e.open_target (hf e he) j).2.congr fun y hy => db_comp_symm n z e he j f y hy

private theorem wdb_eq_zero_of_complex_differentiableAt {n : ℕ} (j : Fin n) {g : V n → ℂ} {y : V n}
    (hg : DifferentiableAt ℂ g y) : wdb n j g y = 0 := by
  unfold wdb
  rw [hg.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul,
    ← mul_assoc, Complex.I_mul_I]
  ring

theorem Holo.db_eq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Holo n z f) (j : Fin n) (x : M) : db n z j f x = 0 := by
  unfold db
  split_ifs with h
  · obtain ⟨hc, hxc⟩ := Classical.choose_spec h
    apply wdb_eq_zero_of_complex_differentiableAt
    rw [hc hxc]
    exact (hf _ hc).differentiableAt
      ((Classical.choose h).open_target.mem_nhds ((Classical.choose h).map_source hxc))
  · rfl

theorem Smooth.ck {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ)
    (hf : Smooth n z f) : Ck n z k f := by
  intro e he
  exact contDiffOn_infty.1 (hf e he) k

theorem SmoothR.ckR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℝ)
    (hf : SmoothR n z f) : CkR n z k f := by
  intro e he
  exact contDiffOn_infty.1 (hf e he) k

theorem Ck.mono {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k l : ℕ) (hkl : k ≤ l)
    (f : M → ℂ) (hf : Ck n z l f) : Ck n z k f := by
  intro e he
  exact (hf e he).of_le (by exact_mod_cast hkl)

theorem Ck.continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
    (hf e he).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  refine (h1.comp (e.continuousAt hx)).congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.left_inv hy]

private theorem contDiffOn_wd_wdb_of_contDiffOn_succ {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ} (k : ℕ)
    (hg : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g U) (j : Fin n) :
    ContDiffOn ℝ k (wd n j g) U ∧ ContDiffOn ℝ k (wdb n j g) U := by
  have hF : ∀ v : V n, ContDiffOn ℝ k (fun y => fderiv ℝ g y v) U := fun v =>
    (hg.fderiv_of_isOpen hU (Nat.cast_succ k).ge).clm_apply contDiffOn_const
  constructor
  · unfold wd
    exact ((hF _).sub (contDiffOn_const.mul (hF _))).div_const 2
  · unfold wdb
    exact ((hF _).add (contDiffOn_const.mul (hF _))).div_const 2

theorem Ck.d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (j : Fin n)
    (f : M → ℂ) (hf : Ck n z (k + 1) f) : Ck n z k (d n z j f) := by
  intro e he
  exact (contDiffOn_wd_wdb_of_contDiffOn_succ e.open_target k (hf e he) j).1.congr fun y hy => d_comp_symm n z e he j f y hy

theorem Ck.db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (j : Fin n)
    (f : M → ℂ) (hf : Ck n z (k + 1) f) : Ck n z k (db n z j f) := by
  intro e he
  exact (contDiffOn_wd_wdb_of_contDiffOn_succ e.open_target k (hf e he) j).2.congr fun y hy => db_comp_symm n z e he j f y hy

end

end ReciprocityTheory.L2DbarEstimates

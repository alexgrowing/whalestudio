import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ExistsChartPartition

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

theorem integral_fderiv_apply_eq_zero (n : ℕ) (H : V n → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) (v : V n) : ∫ y, fderiv ℝ H y v = 0 := by
  have hi : Integrable (fun y => fderiv ℝ H y v) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := fun _ => (1 : ℂ))
    (g := H) (v := v) (by simp) (by simpa using hi)
    (by simpa using hH.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => hH.differentiable one_ne_zero x)
  simpa using this

theorem integral_wd_eq_zero (n : ℕ) (j : Fin n) (H : V n → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) : ∫ y, wd n j H y = 0 := by
  unfold wd
  have i1 : Integrable (fun y => fderiv ℝ H y (bas n j)) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => fderiv ℝ H y (Complex.I • bas n j)) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)
  rw [integral_div, integral_sub i1 (i2.const_mul Complex.I), integral_const_mul,
    integral_fderiv_apply_eq_zero n H hH hc, integral_fderiv_apply_eq_zero n H hH hc]
  simp

theorem integral_wdb_eq_zero (n : ℕ) (j : Fin n) (H : V n → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) : ∫ y, wdb n j H y = 0 := by
  unfold wdb
  have i1 : Integrable (fun y => fderiv ℝ H y (bas n j)) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => fderiv ℝ H y (Complex.I • bas n j)) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)
  rw [integral_div, integral_add i1 (i2.const_mul Complex.I), integral_const_mul,
    integral_fderiv_apply_eq_zero n H hH hc, integral_fderiv_apply_eq_zero n H hH hc]
  simp

theorem integrable_of_continuous {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (vol n z) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  exact hf.integrable_of_hasCompactSupport hc

theorem integrable_of_continuous_real {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (vol n z) := by
  have h := integrable_of_continuous n z hz (fun x => (f x : ℂ)) (Complex.continuous_ofReal.comp hf)
    (hc.comp_left Complex.ofReal_zero)
  simpa using h.re

theorem Smooth.integrable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Smooth n z f) (hc : HasCompactSupport f) :
    Integrable f (vol n z) := integrable_of_continuous n z hz f (Smooth.continuous n z hz f hf) hc

theorem chart_extend {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (h : M → ℂ) (hh : Ck n z 1 h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ e.source) :
    ∃ H : V n → ℂ, ContDiff ℝ 1 H ∧ HasCompactSupport H ∧
      (∀ y ∈ e.target, H =ᶠ[𝓝 y] h ∘ e.symm) ∧ (∀ y ∉ e.target, H =ᶠ[𝓝 y] fun _ => 0) := by
  have hKc : IsCompact (e '' tsupport h) := hc.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  have hKt : e '' tsupport h ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have hout : ∀ w, w ∉ e '' tsupport h → e.target.indicator (h ∘ e.symm) w = 0 := by
    intro w hw
    by_cases hwt : w ∈ e.target
    · rw [Set.indicator_of_mem hwt, Function.comp_apply]
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hw ⟨e.symm w, hmem, e.right_inv hwt⟩
    · exact Set.indicator_of_notMem hwt _
  have hin : ∀ y ∈ e.target, e.target.indicator (h ∘ e.symm) =ᶠ[𝓝 y] h ∘ e.symm := fun y hy =>
    Filter.eventually_of_mem (e.open_target.mem_nhds hy) fun w hw => Set.indicator_of_mem hw _
  have hzero : ∀ y ∉ e '' tsupport h, e.target.indicator (h ∘ e.symm) =ᶠ[𝓝 y] fun _ => 0 :=
    fun y hy => Filter.eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds hy) fun w hw => hout w hw
  refine ⟨e.target.indicator (h ∘ e.symm), ?_, HasCompactSupport.intro hKc hout, hin,
    fun y hy => hzero y fun hyK => hy (hKt hyK)⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · exact ((hh e he).contDiffAt (e.open_target.mem_nhds hy)).congr_of_eventuallyEq (hin y hy)
  · exact contDiffAt_const.congr_of_eventuallyEq (hzero y fun hyK => hy (hKt hyK))

theorem wd_zero_fun (n : ℕ) (j : Fin n) (y : V n) : wd n j (fun _ => (0 : ℂ)) y = 0 := by
  simp [wd]

theorem wdb_zero_fun (n : ℕ) (j : Fin n) (y : V n) : wdb n j (fun _ => (0 : ℂ)) y = 0 := by
  simp [wdb]

private theorem d_db_eq_zero_of_not_mem_tsupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f : M → ℂ) (x : M) (hx : x ∉ tsupport f) :
    d n z j f x = 0 ∧ db n z j f x = 0 := by
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  rw [d_eq_wd n z e he j f x hxe, db_eq_wdb n z e he j f x hxe]
  have hzero : f ∘ e.symm =ᶠ[𝓝 (z x)] fun _ => 0 := by
    have h1 : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
    rw [he hxe]
    have h2 : ∀ᶠ y in 𝓝 (e x), e.symm y ∈ (tsupport f)ᶜ :=
      (e.continuousAt_symm (e.map_source hxe)).preimage_mem_nhds (by rw [e.left_inv hxe]; exact h1)
    filter_upwards [h2] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := f) hy
  exact ⟨(wd_congr n j _ _ _ hzero).trans (wd_zero_fun n j _),
    (wdb_congr n j _ _ _ hzero).trans (wdb_zero_fun n j _)⟩

theorem integral_db_chart_eq_zero {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (h : M → ℂ) (hh : Ck n z 1 h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ e.source) :
    ∫ x, db n z j h x ∂vol n z = 0 := by
  have hcont : Continuous (db n z j h) := Ck.continuous n z hz 0 _ (Ck.db n z 0 j h hh)
  have hzero : ∀ x, x ∉ e.source → db n z j h x = 0 := fun x hx =>
    (d_db_eq_zero_of_not_mem_tsupport n z hz j h x fun h' => hx (hs h')).2
  rw [integral_vol_chart n z hz e he _ hcont.measurable hzero]
  obtain ⟨H, hH1, hHc, hHt, hHo⟩ := chart_extend n z e he h hh hc hs
  have h1 : ∫ y in e.target, db n z j h (e.symm y) = ∫ y in e.target, wdb n j H y := by
    refine setIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_
    rw [db_comp_symm n z e he j h y hy]
    exact wdb_congr n j _ _ y (hHt y hy).symm
  have h2 : ∫ y in e.target, wdb n j H y = ∫ y, wdb n j H y := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    exact (wdb_congr n j _ _ y (hHo y hy)).trans (wdb_zero_fun n j y)
  rw [h1, h2, integral_wdb_eq_zero n j H hH1 hHc]

theorem Ck.finset_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (F : ι → M → ℂ) (hF : ∀ i, Ck n z 1 (F i)) :
    Ck n z 1 (fun y => ∑ i ∈ s, F i y) := by
  intro e he
  exact ContDiffOn.sum fun i _ => hF i e he

private theorem wd_wdb_finset_sum {ι : Type*} {n : ℕ} (s : Finset ι) (G : ι → V n → ℂ) (y : V n)
    (hG : ∀ i ∈ s, DifferentiableAt ℝ (G i) y) (j : Fin n) :
    wd n j (fun w => ∑ i ∈ s, G i w) y = ∑ i ∈ s, wd n j (G i) y ∧
      wdb n j (fun w => ∑ i ∈ s, G i w) y = ∑ i ∈ s, wdb n j (G i) y := by
  have hF : fderiv ℝ (fun w => ∑ i ∈ s, G i w) y = ∑ i ∈ s, fderiv ℝ (G i) y := by
    have H := HasFDerivAt.sum (u := s) (A := G) fun i hi => (hG i hi).hasFDerivAt
    try simp only [Finset.sum_fn] at H
    exact H.fderiv
  constructor
  · simp only [wd, hF, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_div]
  · simp only [wdb, hF, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]

theorem d_finset_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (F : ι → M → ℂ) (hF : ∀ i, Ck n z 1 (F i)) (j : Fin n) (x : M) :
    d n z j (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, d n z j (F i) x := by
  unfold d
  split_ifs with h
  · obtain ⟨hc, hxc⟩ := Classical.choose_spec h
    have hzx : z x ∈ (Classical.choose h).target := by
      rw [hc hxc]; exact (Classical.choose h).map_source hxc
    exact (wd_wdb_finset_sum s (fun i => F i ∘ (Classical.choose h).symm) (z x)
      (fun i _ => ((hF i _ hc).contDiffAt ((Classical.choose h).open_target.mem_nhds hzx)).differentiableAt
        one_ne_zero) j).1
  · simp

theorem db_finset_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (F : ι → M → ℂ) (hF : ∀ i, Ck n z 1 (F i)) (j : Fin n) (x : M) :
    db n z j (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, db n z j (F i) x := by
  unfold db
  split_ifs with h
  · obtain ⟨hc, hxc⟩ := Classical.choose_spec h
    have hzx : z x ∈ (Classical.choose h).target := by
      rw [hc hxc]; exact (Classical.choose h).map_source hxc
    exact (wd_wdb_finset_sum s (fun i => F i ∘ (Classical.choose h).symm) (z x)
      (fun i _ => ((hF i _ hc).contDiffAt ((Classical.choose h).open_target.mem_nhds hzx)).differentiableAt
        one_ne_zero) j).2
  · simp

theorem exists_chart_decomp {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∃ (N : ℕ) (e : Fin N → OpenPartialHomeomorph M (V n)) (h : Fin N → M → ℂ),
      (∀ i, IsChart n z (e i)) ∧ (∀ i, Ck n z 1 (h i)) ∧ (∀ i, HasCompactSupport (h i)) ∧
      (∀ i, tsupport (h i) ⊆ (e i).source) ∧ g = fun x => ∑ i, h i x := by
  obtain ⟨N, e, χ, he, hχs, -, hχsub, -, -, hχ1⟩ :=
    exists_chart_partition n z hz (tsupport g) univ hc isOpen_univ (subset_univ _)
  refine ⟨N, e, fun i x => (χ i x : ℂ) * g x, he, fun i => Ck.mul n z 1 _ _ (Smooth.ck n z 1 _ (hχs i)) hg,
    fun i => hc.mul_left, fun i => ?_, ?_⟩
  · refine (tsupport_mul_subset_left (f := fun x => (χ i x : ℂ)) (g := g)).trans ?_
    refine (tsupport_comp_subset Complex.ofReal_zero (χ i)).trans ?_
    exact (hχsub i).trans inter_subset_left
  · funext x
    by_cases hx : x ∈ tsupport g
    · rw [← Finset.sum_mul, ← Complex.ofReal_sum, hχ1 x hx]; simp
    · have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]

theorem integral_db_eq_zero {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (j : Fin n) (g : M → ℂ) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∫ x, db n z j g x ∂vol n z = 0 := by
  obtain ⟨N, e, h, he, hh, hc', hs, rfl⟩ := exists_chart_decomp n z hz g hg hc
  have dint : ∀ i, Integrable (fun x => db n z j (h i) x) (vol n z) := fun i =>
    integrable_of_continuous n z hz _ (Ck.continuous n z hz 0 _ (Ck.db n z 0 j (h i) (hh i)))
      ((hc' i).mono' fun x hx => by
        by_contra hx'
        exact hx (d_db_eq_zero_of_not_mem_tsupport n z hz j _ x hx').2)
  have hsum : (fun x => db n z j (fun x => ∑ i, h i x) x) = fun x => ∑ i, db n z j (h i) x :=
    funext fun x => db_finset_sum n z Finset.univ h (fun i => hh i) j x
  rw [hsum, integral_finset_sum _ fun i _ => dint i]
  exact Finset.sum_eq_zero fun i _ =>
    integral_db_chart_eq_zero n z hz (e i) (he i) j (h i) (hh i) (hc' i) (hs i)

private theorem wd_wdb_mul {n : ℕ} {u v : V n → ℂ} {y : V n} (hu : DifferentiableAt ℝ u y)
    (hv : DifferentiableAt ℝ v y) (j : Fin n) :
    wd n j (fun w => u w * v w) y = wd n j u y * v y + u y * wd n j v y ∧
      wdb n j (fun w => u w * v w) y = wdb n j u y * v y + u y * wdb n j v y := by
  have hF : fderiv ℝ (fun w => u w * v w) y = u y • fderiv ℝ v y + v y • fderiv ℝ u y :=
    (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  constructor <;>
    simp only [wd, wdb, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] <;> ring

private theorem d_db_mul_of_ck_one {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y * g y) x = d n z j f x * g x + f x * d n z j g x ∧
      db n z j (fun y => f y * g y) x = db n z j f x * g x + f x * db n z j g x := by
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  have hT : e.target ∈ 𝓝 (z x) := by
    rw [he hxe]; exact e.open_target.mem_nhds (e.map_source hxe)
  have du : DifferentiableAt ℝ (f ∘ e.symm) (z x) :=
    ((hf e he).contDiffAt hT).differentiableAt one_ne_zero
  have dv : DifferentiableAt ℝ (g ∘ e.symm) (z x) :=
    ((hg e he).contDiffAt hT).differentiableAt one_ne_zero
  have hx' : e.symm (z x) = x := by rw [he hxe, e.left_inv hxe]
  rw [d_eq_wd n z e he j _ x hxe, d_eq_wd n z e he j f x hxe, d_eq_wd n z e he j g x hxe,
    db_eq_wdb n z e he j _ x hxe, db_eq_wdb n z e he j f x hxe, db_eq_wdb n z e he j g x hxe]
  have key := wd_wdb_mul du dv j
  simp only [Function.comp_apply, hx'] at key
  exact key

theorem integral_db_mul {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∫ x, db n z j f x * g x ∂vol n z = -∫ x, f x * db n z j g x ∂vol n z := by
  have hfg1 : Ck n z 1 (fun y => f y * g y) := fun e he => (hf e he).mul (hg e he)
  have h0 := integral_db_eq_zero n z hz j (fun y => f y * g y) hfg1 hc.mul_left
  have dcs : HasCompactSupport (db n z j g) := hc.mono' fun x hx => by
    by_contra hx'
    exact hx (d_db_eq_zero_of_not_mem_tsupport n z hz j _ x hx').2
  have i1 : Integrable (fun x => db n z j f x * g x) (vol n z) :=
    integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 0 _ (Ck.db n z 0 j f hf)).mul (Ck.continuous n z hz 1 g hg)) hc.mul_left
  have i2 : Integrable (fun x => f x * db n z j g x) (vol n z) :=
    integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 1 f hf).mul (Ck.continuous n z hz 0 _ (Ck.db n z 0 j g hg))) dcs.mul_left
  have hprod : (fun x => db n z j (fun y => f y * g y) x) =
      fun x => db n z j f x * g x + f x * db n z j g x :=
    funext fun x => (d_db_mul_of_ck_one n z hz f g hf hg j x).2
  rw [hprod, integral_add i1 i2] at h0
  linear_combination h0

end

end ReciprocityTheory.L2DbarEstimates

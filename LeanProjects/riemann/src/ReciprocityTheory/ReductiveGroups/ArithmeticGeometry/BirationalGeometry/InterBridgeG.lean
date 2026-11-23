import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology Function

variable {e : ℕ}

def jacN (Q : (Fin e → ℂ) → (Fin e → ℂ)) (u : Fin e → ℂ) : ℝ :=
  ‖LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2

def fibSum (D : Set (Fin e → ℂ)) (Q : (Fin e → ℂ) → (Fin e → ℂ)) (h : (Fin e → ℂ) → ℝ)
    (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ u ∈ D ∩ Q ⁻¹' {y}, h u / jacN Q u

theorem abs_det_restrictScalars (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    |(f.restrictScalars ℝ).det| = ‖LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h : (f.restrictScalars ℝ).det =
      Complex.normSq (LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) := by
    show LinearMap.det ((f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

theorem piece_change {D : Set (Fin e → ℂ)} (hD : MeasurableSet D) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQd : ∀ u ∈ D, DifferentiableAt ℂ Q u)
    (hdet : ∀ u ∈ D, LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hinj : InjOn Q D) {h : (Fin e → ℂ) → ℝ} (hh : IntegrableOn h D) :
    Integrable (fibSum D Q h) ∧ ∫ y, fibSum D Q h y = ∫ u in D, h u ∧
      ∫ y, ‖fibSum D Q h y‖ = ∫ u in D, ‖h u‖ := by
  have hf' : ∀ u ∈ D, HasFDerivWithinAt Q ((fderiv ℂ Q u).restrictScalars ℝ) D u :=
    fun u hu => ((hQd u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hJpos : ∀ u ∈ D, 0 < jacN Q u := fun u hu =>
    pow_pos (norm_pos_iff.mpr (hdet u hu)) 2
  have hval : ∀ u ∈ D, fibSum D Q h (Q u) = h u / jacN Q u := by
    intro u hu
    have : D ∩ Q ⁻¹' {Q u} = {u} := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨hv, hq⟩ => hinj hv hu hq, fun hv => by subst hv; exact ⟨hu, rfl⟩⟩
    simp only [fibSum, this, finsum_mem_singleton]
  have hzero : ∀ y, y ∉ Q '' D → fibSum D Q h y = 0 := by
    intro y hy
    have : D ∩ Q ⁻¹' {y} = ∅ := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      exact fun hv hq => hy ⟨v, hv, hq⟩
    simp [fibSum, this]
  have hdetJ : ∀ u, |((fderiv ℂ Q u).restrictScalars ℝ).det| = jacN Q u := fun u =>
    abs_det_restrictScalars _
  have hkey : EqOn (fun u => |((fderiv ℂ Q u).restrictScalars ℝ).det| • fibSum D Q h (Q u)) h D := by
    intro u hu
    simp only [hval u hu, hdetJ, smul_eq_mul]
    field_simp [(hJpos u hu).ne']
  have hkeyn : EqOn (fun u => |((fderiv ℂ Q u).restrictScalars ℝ).det| • ‖fibSum D Q h (Q u)‖)
      (fun u => ‖h u‖) D := by
    intro u hu
    simp only [hval u hu, hdetJ, smul_eq_mul, norm_div, Real.norm_of_nonneg (hJpos u hu).le]
    field_simp [(hJpos u hu).ne']
  have hint_on : IntegrableOn (fibSum D Q h) (Q '' D) := by
    rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hf' hinj]
    exact hh.congr_fun (fun u hu => (hkey hu).symm) hD
  have hint : Integrable (fibSum D Q h) := hint_on.integrable_of_forall_notMem_eq_zero hzero
  refine ⟨hint, ?_, ?_⟩
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj]
    exact setIntegral_congr_fun hD hkey
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Q '' D)
      (fun y hy => by rw [hzero y hy, norm_zero]),
      integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj]
    exact setIntegral_congr_fun hD hkeyn

theorem exists_inj_cover {O : Set (Fin e → ℂ)} {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (hO : IsOpen O) :
    ∃ W : ℕ → Set (Fin e → ℂ), (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ O) ∧ (∀ n, InjOn Q (W n)) ∧
      ⋃ n, W n = O := by
  classical
  set s : Set (Set (Fin e → ℂ)) :=
    insert ∅ {b | b ∈ TopologicalSpace.countableBasis (Fin e → ℂ) ∧ b ⊆ O ∧ InjOn Q b}
  have hs : s.Countable :=
    ((TopologicalSpace.countable_countableBasis _).mono fun b hb => hb.1).insert ∅
  have hmem : ∀ n, Set.enumerateCountable hs ∅ n ∈ s := Set.enumerateCountable_mem hs
    (Set.mem_insert _ _)
  refine ⟨Set.enumerateCountable hs ∅, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · rcases hmem n with h | h
    · rw [h]; exact isOpen_empty
    · exact TopologicalSpace.isOpen_of_mem_countableBasis h.1
  · rcases hmem n with h | h
    · rw [h]; exact empty_subset _
    · exact h.2.1
  · rcases hmem n with h | h
    · rw [h]; exact injOn_empty _
    · exact h.2.2
  · refine Subset.antisymm (iUnion_subset fun n => ?_) fun u hu => ?_
    · rcases hmem n with h | h
      · rw [h]; exact empty_subset _
      · exact h.2.1
    obtain ⟨hQa, hQd⟩ := hQ u hu
    set Ce := (fderiv ℂ Q u).toContinuousLinearEquivOfDetNeZero hQd
    have hCe : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ Q u :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hQd
    have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
      rw [hCe]; exact hQa.hasStrictFDerivAt
    set F := hstrict.toOpenPartialHomeomorph Q
    have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
    have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
    obtain ⟨b, hbB, hub, hbsub⟩ := (TopologicalSpace.isBasis_countableBasis (Fin e → ℂ)).exists_subset_of_mem_open
      (⟨hus, hu⟩ : u ∈ F.source ∩ O) (F.open_source.inter hO)
    have hbs : b ∈ s := Or.inr ⟨hbB, fun v hv => (hbsub hv).2, by
      rw [← hFc]; exact F.injOn.mono fun v hv => (hbsub hv).1⟩
    obtain ⟨n, hn⟩ := Set.subset_range_enumerate hs ∅ hbs
    exact mem_iUnion.mpr ⟨n, hn ▸ hub⟩

theorem integrable_tsum_of_summable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ n, Integrable (F n) μ) (hs : Summable fun n => ∫ y, ‖F n y‖ ∂μ) :
    Integrable (fun y => ∑' n, F n y) μ := by
  have hmeas : ∀ n, AEMeasurable (fun y => ‖F n y‖ₑ) μ := fun n => (hF n).aemeasurable.enorm
  have hlin : ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have : ∀ n, ∫⁻ y, ‖F n y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖F n y‖ ∂μ) := fun n =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF n)).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ y ∂μ, ∑' n, ‖F n y‖ₑ < ⊤ := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hlin
  have hsum : ∀ᵐ y ∂μ, Summable fun n => F n y := by
    filter_upwards [hae] with y hy
    refine Summable.of_norm ?_
    have : (∑' n, (‖F n y‖₊ : ENNReal)) ≠ ⊤ := hy.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp this)
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ n ∈ Finset.range N, F n y)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hF n).1) ?_, ?_⟩
  · filter_upwards [hsum] with y hy
    exact hy.hasSum.tendsto_sum_nat
  · refine lt_of_le_of_lt (lintegral_mono fun y => enorm_tsum_le_tsum_enorm) ?_
    exact lt_top_iff_ne_top.mpr hlin

theorem tsum_finsum_disjointed {α : Type*} {D : ℕ → Set α} (hd : Pairwise (Disjoint on D))
    {O : Set α} (hU : ⋃ n, D n = O) {G : Set α} (hG : (O ∩ G).Finite) (f : α → ℝ) :
    ∑' n, ∑ᶠ u ∈ D n ∩ G, f u = ∑ᶠ u ∈ O ∩ G, f u := by
  classical
  have hsub : ∀ n, D n ⊆ O := fun n => hU ▸ subset_iUnion D n
  have hterm : ∀ n, ∑ᶠ u ∈ D n ∩ G, f u = ∑ u ∈ hG.toFinset, if u ∈ D n then f u else 0 := by
    intro n
    rw [finsum_mem_eq_finite_toFinset_sum f (hG.subset fun u hu => ⟨hsub n hu.1, hu.2⟩),
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    ext u
    simp only [Finite.mem_toFinset, Finset.mem_filter, mem_inter_iff]
    exact ⟨fun h => ⟨⟨hsub n h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have hfun : ∀ u ∈ hG.toFinset, ∃ n0 : ℕ,
      (fun n => if u ∈ D n then f u else 0) = fun n => if n = n0 then f u else 0 := by
    intro u hu
    have huO : u ∈ O := (hG.mem_toFinset.mp hu).1
    obtain ⟨n0, hn0⟩ := mem_iUnion.mp (hU ▸ huO : u ∈ ⋃ n, D n)
    refine ⟨n0, funext fun n => ?_⟩
    by_cases hn : n = n0
    · subst hn; simp [hn0]
    · have : u ∉ D n := fun h => (hd hn).le_bot ⟨h, hn0⟩
      simp [this, hn]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun u hu => ?_), finsum_mem_eq_finite_toFinset_sum f hG]
  · refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨n0, h⟩ := hfun u hu
    rw [h, tsum_ite_eq]
  · obtain ⟨n0, h⟩ := hfun u hu
    rw [h]
    exact (hasSum_ite_eq n0 (f u)).summable

theorem area_open {O : Set (Fin e → ℂ)} (hO : IsOpen O) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : IntegrableOn h O) (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) :
    Integrable (fibSum O Q h) ∧ ∫ u in O, h u = ∫ y, fibSum O Q h y := by
  obtain ⟨W, hWo, hWO, hWinj, hWU⟩ := exists_inj_cover hQ hO
  set D := disjointed W with hDdef
  have hDm : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed fun n => (hWo n).measurableSet
  have hDsub : ∀ n, D n ⊆ W n := disjointed_subset W
  have hDU : ⋃ n, D n = O := iUnion_disjointed.trans hWU
  have hDd : Pairwise (Disjoint on D) := disjoint_disjointed W
  have hDO : ∀ n, D n ⊆ O := fun n => (hDsub n).trans (hWO n)
  have hp : ∀ n, Integrable (fibSum (D n) Q h) ∧ ∫ y, fibSum (D n) Q h y = ∫ u in D n, h u ∧
      ∫ y, ‖fibSum (D n) Q h y‖ = ∫ u in D n, ‖h u‖ := fun n =>
    piece_change (hDm n) (fun u hu => (hQ u (hDO n hu)).1.differentiableAt)
      (fun u hu => (hQ u (hDO n hu)).2) ((hWinj n).mono (hDsub n)) (hh.mono_set (hDO n))
  have hhO : IntegrableOn h (⋃ n, D n) := by rw [hDU]; exact hh
  have hs1 := hasSum_integral_iUnion hDm hDd hhO
  have hs2 := hasSum_integral_iUnion hDm hDd hhO.norm
  have hn2 : ∀ n, ∫ y, ‖fibSum (D n) Q h y‖ = ∫ u in D n, ‖h u‖ := fun n => (hp n).2.2
  have hn1 : ∀ n, ∫ y, fibSum (D n) Q h y = ∫ u in D n, h u := fun n => (hp n).2.1
  have hsumm : Summable fun n => ∫ y, ‖fibSum (D n) Q h y‖ := by
    simp_rw [hn2]; exact hs2.summable
  have htsum : ∫ y, ∑' n, fibSum (D n) Q h y = ∑' n, ∫ y, fibSum (D n) Q h y :=
    (integral_tsum_of_summable_integral_norm (fun n => (hp n).1) hsumm).symm
  have hae : (fun y => ∑' n, fibSum (D n) Q h y) =ᵐ[volume] fibSum O Q h := by
    filter_upwards [hfin] with y hy
    simp only [fibSum]
    exact tsum_finsum_disjointed hDd hDU hy (fun u => h u / jacN Q u)
  refine ⟨(integrable_tsum_of_summable (fun n => (hp n).1) hsumm).congr hae, ?_⟩
  rw [← integral_congr_ae hae, htsum]
  simp_rw [hn1]
  rw [hs1.tsum_eq, hDU]

end ReciprocityTheory.ChartRestriction.G.Geo

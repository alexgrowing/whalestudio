import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MeasureTheory Set Filter Function ReciprocityTheory.ChartRestriction.G.Geo

namespace LintegralFibSum

variable {e : ℕ}

theorem measurable_jacN (Q : (Fin e → ℂ) → (Fin e → ℂ)) : Measurable (jacN Q) := by
  unfold jacN
  exact ((continuous_norm.comp ContinuousLinearMap.continuous_det).measurable.comp
    (measurable_fderiv ℂ Q)).pow_const 2

theorem fibSum_nonneg (D : Set (Fin e → ℂ)) (Q : (Fin e → ℂ) → (Fin e → ℂ)) {h : (Fin e → ℂ) → ℝ}
    (hh : ∀ u, 0 ≤ h u) (y : Fin e → ℂ) : 0 ≤ fibSum D Q h y :=
  finsum_nonneg fun u => finsum_nonneg fun _ => div_nonneg (hh u) (by unfold jacN; positivity)

theorem lintegral_fibSum_piece {D : Set (Fin e → ℂ)} (hD : MeasurableSet D) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQd : ∀ u ∈ D, DifferentiableAt ℂ Q u)
    (hdet : ∀ u ∈ D, LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hinj : InjOn Q D) {h : (Fin e → ℂ) → ℝ} (hm : Measurable fun u : D => h u) :
    Measurable (fun y => ENNReal.ofReal (fibSum D Q h y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum D Q h y) = ∫⁻ u in D, ENNReal.ofReal (h u) := by
  have hf' : ∀ u ∈ D, HasFDerivWithinAt Q ((fderiv ℂ Q u).restrictScalars ℝ) D u :=
    fun u hu => ((hQd u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hJpos : ∀ u ∈ D, 0 < jacN Q u := fun u hu => pow_pos (norm_pos_iff.mpr (hdet u hu)) 2
  have hval : ∀ u ∈ D, fibSum D Q h (Q u) = h u / jacN Q u := by
    intro u hu
    have : D ∩ Q ⁻¹' {Q u} = {u} := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨hw, hq⟩ => hinj hw hu hq, fun hw => by subst hw; exact ⟨hu, rfl⟩⟩
    simp only [fibSum, this, finsum_mem_singleton]
  have hzero : ∀ y, y ∉ Q '' D → fibSum D Q h y = 0 := by
    intro y hy
    have : D ∩ Q ⁻¹' {y} = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      exact fun hw hq => hy ⟨w, hw, hq⟩
    simp [fibSum, this]
  have hE := measurableEmbedding_of_fderivWithin hD hf' hinj
  have hext : (fun y => ENNReal.ofReal (fibSum D Q h y)) =
      extend (D.domRestrict Q) (fun u : D => ENNReal.ofReal (h u / jacN Q u)) 0 := by
    funext y
    by_cases hy : ∃ u : D, D.domRestrict Q u = y
    · obtain ⟨u, rfl⟩ := hy
      rw [hE.injective.extend_apply]
      exact congrArg ENNReal.ofReal (hval u u.2)
    · rw [extend_apply' _ _ _ hy, hzero y fun ⟨u, hu, hq⟩ => hy ⟨⟨u, hu⟩, hq⟩]
      simp
  refine ⟨?_, ?_⟩
  · rw [hext]
    exact hE.measurable_extend (ENNReal.measurable_ofReal.comp
      (hm.div ((measurable_jacN Q).comp measurable_subtype_coe))) measurable_const
  · rw [← setLIntegral_eq_of_support_subset (s := Q '' D) (fun y hy => by
        by_contra h'
        exact hy (show ENNReal.ofReal (fibSum D Q h y) = 0 by rw [hzero y h', ENNReal.ofReal_zero])),
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hf' hinj]
    refine setLIntegral_congr_fun hD fun u hu => ?_
    have hJ : |((fderiv ℂ Q u).restrictScalars ℝ).det| = jacN Q u := abs_det_restrictScalars _
    rw [hval u hu, hJ, ← ENNReal.ofReal_mul (hJpos u hu).le]
    congr 1
    field_simp [(hJpos u hu).ne']

theorem lintegral_fibSum_open {O : Set (Fin e → ℂ)} (hO : IsOpen O) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : ∀ u, 0 ≤ h u) (hm : Measurable fun u : O => h u)
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) :
    AEMeasurable (fun y => ENNReal.ofReal (fibSum O Q h y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum O Q h y) = ∫⁻ u in O, ENNReal.ofReal (h u) := by
  obtain ⟨W, hWo, hWO, hWinj, hWU⟩ := exists_inj_cover hQ hO
  set D := disjointed W with hDdef
  have hDm : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed fun n => (hWo n).measurableSet
  have hDsub : ∀ n, D n ⊆ W n := disjointed_subset W
  have hDU : ⋃ n, D n = O := iUnion_disjointed.trans hWU
  have hDd : Pairwise (Disjoint on D) := disjoint_disjointed W
  have hDO : ∀ n, D n ⊆ O := fun n => (hDsub n).trans (hWO n)
  have hp : ∀ n, Measurable (fun y => ENNReal.ofReal (fibSum (D n) Q h y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum (D n) Q h y) = ∫⁻ u in D n, ENNReal.ofReal (h u) := fun n =>
    lintegral_fibSum_piece (hDm n) (fun u hu => (hQ u (hDO n hu)).1.differentiableAt)
      (fun u hu => (hQ u (hDO n hu)).2) ((hWinj n).mono (hDsub n))
      (hm.comp (f := fun u : D n => (⟨u.1, hDO n u.2⟩ : O)) measurable_subtype_coe.subtype_mk)
  have hae : (fun y => ENNReal.ofReal (fibSum O Q h y)) =ᵐ[volume]
      fun y => ∑' n, ENNReal.ofReal (fibSum (D n) Q h y) := by
    filter_upwards [hfin] with y hy
    have hT : {n | (D n ∩ Q ⁻¹' {y}).Nonempty}.Finite := by
      refine (hy.biUnion fun u _ => (show {n | u ∈ D n}.Subsingleton from
        fun n hn m hm => by_contra fun hnm => Set.disjoint_left.mp (hDd hnm) hn hm).finite).subset ?_
      rintro n ⟨u, hu, hq⟩
      exact mem_iUnion₂.mpr ⟨u, ⟨hDO n hu, hq⟩, hu⟩
    have hsum : Summable fun n => fibSum (D n) Q h y :=
      summable_of_ne_finset_zero (s := hT.toFinset) fun n hn => by
        have : D n ∩ Q ⁻¹' {y} = ∅ := by
          rw [Set.Finite.mem_toFinset] at hn
          exact not_nonempty_iff_eq_empty.mp hn
        simp [fibSum, this]
    show ENNReal.ofReal (∑ᶠ u ∈ O ∩ Q ⁻¹' {y}, h u / jacN Q u) = _
    rw [← tsum_finsum_disjointed hDd hDU hy (fun u => h u / jacN Q u)]
    exact ENNReal.ofReal_tsum_of_nonneg (f := fun n => fibSum (D n) Q h y)
      (fun n => fibSum_nonneg _ _ hh y) hsum
  refine ⟨(Measurable.tsum fun n => (hp n).1).aemeasurable.congr hae.symm, ?_⟩
  rw [lintegral_congr_ae hae, lintegral_tsum fun n => (hp n).1.aemeasurable,
    tsum_congr fun n => (hp n).2, ← lintegral_iUnion hDm hDd, hDU]

end LintegralFibSum

end GroundTheory.Heights₂.Heights.LowerBoundFree

import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffHypInclAt

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff Manifold

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem slice_mInt {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
    {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
    (B : FinHolAtlas e W) (hB : HoloMap B A Subtype.val) (Φ : Fin e → LocPot X)
    (hΦ : ∀ k, IsPotential A (Φ k)) (hψ : IsCompatChart A ψ)
    (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) (x : X) {V : Set X}
    (hV : IsOpen V) (hVψ : V ⊆ ψ.source) (hVΦ : ∀ k, V ⊆ (Φ k).U x)
    (hxW : x ∉ W → V ∩ W = ∅) {v : X → ℝ} (hv : A.Smooth v) (hvV : tsupport v ⊆ V) :
    mInt B (fun k => (Φ k).pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) =
      ∫ z, chartExt ψ v (hypInclAt i z) * densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) z := by
  by_cases hx : x ∈ W
  · have hne : Nonempty (ChartPartition B) := existsPartition B
    unfold mInt
    rw [dif_pos hne]
    unfold integralWith
    have hj := fun j => slice_chart B hB Φ hΦ hψ hWψ x hx hV hVψ hVΦ hv hvV hne.some j
    rw [Finset.sum_congr rfl (fun j _ => (hj j).2)]
    rw [← integral_finsetSum _ (fun j _ => (hj j).1)]
    congr 1
    funext z
    by_cases ht : hypInclAt i z ∈ ψ.target
    · simp only [Set.indicator_of_mem (show z ∈ hypInclAt i ⁻¹' ψ.target from ht)]
      obtain ⟨hpW, -, -⟩ := symm_hyp_mem hWψ ht
      rw [chartExt, Set.indicator_of_mem ht]
      simp only [sliceF, ← Finset.sum_mul]
      have h1 : ∑ j, extW W (hne.some.χ j) (ψ.symm (hypInclAt i z)) = 1 := by
        simp only [extW, hpW, dif_pos]
        exact hne.some.sum_eq_one _
      rw [h1, one_mul]
      rfl
    · simp only [Set.indicator_of_notMem (show z ∉ hypInclAt i ⁻¹' ψ.target from ht),
        Finset.sum_const_zero, chartExt, Set.indicator_of_notMem ht, zero_mul]
  · have hV0 := hxW hx
    have hv0 : ∀ p ∈ W, v p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport fun h => by
      have : p ∈ V ∩ W := ⟨hvV h, hp⟩
      rw [hV0] at this; exact this
    rw [mInt_zero_fun _ _ (g := v ∘ Subtype.val) (fun q : W => hv0 q q.2)]
    symm
    have : (fun z => chartExt ψ v (hypInclAt i z) * densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) z) =
        fun _ => 0 := by
      funext z
      by_cases ht : hypInclAt i z ∈ ψ.target
      · obtain ⟨hpW, -, -⟩ := symm_hyp_mem hWψ ht
        simp [chartExt, Set.indicator_of_mem ht, hv0 _ hpW]
      · simp [chartExt, Set.indicator_of_notMem ht]
    rw [this, integral_zero]

section Helpers

omit [T2Space X] [CompactSpace X]

theorem analyticAt_compat_fun {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : Fin e → ℂ}
    (hy : y ∈ ψ.target) (hyU : ψ.symm y ∈ U) : AnalyticAt ℂ (g ∘ ψ.symm) y := by
  obtain ⟨j, hj⟩ : ∃ j, ψ.symm y ∈ (A.chart j).source := A.cover (ψ.symm y)
  have h1 : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) y := (hψ j).2 y ⟨hy, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) y) :=
    hg j _ ⟨(A.chart j).map_source hj, by simpa [Function.comp, (A.chart j).left_inv hj] using hyU⟩
  refine (h2.comp h1).congr ?_
  filter_upwards [ψ.continuousAt_symm hy ((A.chart j).open_source.mem_nhds hj)] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem exists_cutoff {n : ℕ} {K U : Set (Fin n → ℂ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ ρ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ ρ ∧ IsCompact (tsupport ρ) ∧ tsupport ρ ⊆ U ∧
      ∃ O, IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ρ y = 1 := by
  have key : ∀ x, ∃ f : (Fin n → ℂ) → ℝ, tsupport f ⊆ U ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧
      (∀ y, 0 ≤ f y) ∧ (x ∈ K → f x = 1) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x (hKU hx)
      let b : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩
      refine ⟨b, ?_, b.hasCompactSupport, b.contDiff, fun y => b.nonneg, fun _ => ?_⟩
      · rw [b.tsupport_eq]
        exact (Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hrU
      · exact b.one_of_mem_closedBall (Metric.mem_closedBall_self (by show (0:ℝ) ≤ r / 4; linarith))
    · refine ⟨0, by simp, HasCompactSupport.zero, contDiff_const, fun _ => le_rfl, fun h => (hx h).elim⟩
  choose f hfU hfc hfd hf0 hf1 using key
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | 1 / 2 < f x y}) (fun x hx =>
    (isOpen_lt continuous_const (hfd x).continuous).mem_nhds (by
      show (1 : ℝ) / 2 < f x x
      rw [hf1 x hx]
      norm_num))
  have hσ : ContDiff ℝ ∞ (fun y => 2 * ∑ i ∈ t, f i y) :=
    contDiff_const.mul (ContDiff.sum fun i _ => hfd i)
  have hCc : IsCompact (⋃ i ∈ t, tsupport (f i)) := t.isCompact_biUnion fun i _ => hfc i
  have hCU : (⋃ i ∈ t, tsupport (f i)) ⊆ U := Set.iUnion₂_subset fun i _ => hfU i
  have hsuppC : Function.support (fun y => Real.smoothTransition (2 * ∑ i ∈ t, f i y)) ⊆
      ⋃ i ∈ t, tsupport (f i) := by
    intro y hy
    by_contra hyC
    apply hy
    have h0 : ∀ i ∈ t, f i y = 0 := fun i hi => by
      by_contra h
      exact hyC (Set.mem_biUnion hi (subset_tsupport _ h))
    show Real.smoothTransition (2 * ∑ i ∈ t, f i y) = 0
    rw [Finset.sum_eq_zero h0, mul_zero]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  have hts : tsupport (fun y => Real.smoothTransition (2 * ∑ i ∈ t, f i y)) ⊆ ⋃ i ∈ t, tsupport (f i) :=
    closure_minimal hsuppC hCc.isClosed
  refine ⟨fun y => Real.smoothTransition (2 * ∑ i ∈ t, f i y), Real.smoothTransition.contDiff.comp hσ,
    hCc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hCU, {y | 1 < 2 * ∑ i ∈ t, f i y},
    isOpen_lt continuous_const hσ.continuous, ?_, fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy)⟩
  intro x hx
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hcov hx)
  have : f i x ≤ ∑ j ∈ t, f j x := Finset.single_le_sum (fun j _ => hf0 j x) hi
  simp only [Set.mem_setOf_eq] at hix ⊢
  linarith

theorem contDiff_mul_of_tsupport {n : ℕ} {ρ f : (Fin n → ℂ) → ℝ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun y => ρ y * f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hρ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hy))
  · have hyρ : y ∉ tsupport ρ := fun h => hy (hρU h)
    have h0 : (fun z => ρ z * f z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyρ] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq h0

end Helpers

end

end ReciprocityTheory.AnForm.M.PLAux

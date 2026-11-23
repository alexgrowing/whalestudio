import Mathlib
import Formalism.PeriodIntegrals.QuotNuSigma

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PI.UnitaryGroupMassFormula.QuotNuSigma

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem pos_open_one (A : Set G) (μA : Measure G) (h0 : μA ≠ 0) (hc : μA Aᶜ = 0)
    (hinv : ∀ s ∈ A, μA.map (fun x => s * x) = μA) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < μA U := by
  by_contra hpos
  have hU0 : μA U = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hpos)
  let F : A → Set G := fun s => (fun x => (s : G)⁻¹ * x) ⁻¹' U
  have hFo : ∀ s, IsOpen (F s) := fun s => hU.preimage (continuous_const.mul continuous_id)
  have hF0 : ∀ s, μA (F s) = 0 := by
    intro s
    have hm := congrArg (fun m : Measure G => m (F s)) (hinv s s.2)
    rw [← hm, Measure.map_apply (measurable_const_mul _) (hFo s).measurableSet]
    have hpre : (fun x => (s : G) * x) ⁻¹' F s = U := by
      ext x
      simp [F]
    rw [hpre, hU0]
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable F hFo
  have hcov : A ⊆ ⋃ s ∈ T, F s := by
    intro a ha
    rw [hTU]
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, by simp [F, h1]⟩
  have hnull : μA (⋃ s ∈ T, F s) = 0 := (measure_biUnion_null_iff hT).2 fun s _ => hF0 s
  have huniv : μA Set.univ = 0 := by
    refine measure_mono_null (fun x _ => ?_) (measure_union_null hnull hc)
    by_cases hx : x ∈ A
    · exact Or.inl (hcov hx)
    · exact Or.inr hx
  exact h0 (Measure.measure_univ_eq_zero.1 huniv)

theorem pos_open_one_mul (A B : Set G) (μA μB : Measure G) [SigmaFinite μB]
    (hA0 : μA ≠ 0) (hAc : μA Aᶜ = 0) (hAi : ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB0 : μB ≠ 0) (hBc : μB Bᶜ = 0) (hBi : ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < ((μA.prod μB).map (fun p : G × G => p.1 * p.2)) U := by
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1)
  have hApos := pos_open_one A μA hA0 hAc hAi V hVo hV1
  have hBpos := pos_open_one B μB hB0 hBc hBi V hVo hV1
  have hsub : V ×ˢ V ⊆ (fun p : G × G => p.1 * p.2) ⁻¹' U := fun p hp =>
    hVV (Set.mul_mem_mul hp.1 hp.2)
  calc (0 : ℝ≥0∞) < μA V * μB V := ENNReal.mul_pos hApos.ne' hBpos.ne'
    _ = (μA.prod μB) (V ×ˢ V) := (Measure.prod_prod V V).symm
    _ ≤ (μA.prod μB) ((fun p : G × G => p.1 * p.2) ⁻¹' U) := measure_mono hsub
    _ ≤ _ := Measure.le_map_apply measurable_mul.aemeasurable U

theorem sigmaFinite_of_weil [LocallyCompactSpace G] [T2Space G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G)
    (hA : SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB : SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (hW : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) :
    SigmaFinite ν := by
  obtain ⟨hAσ, hA0, hAc, hAi⟩ := hA
  obtain ⟨hBσ, hB0, hBc, hBi⟩ := hB
  have := hAσ
  have := hBσ
  set ρ := (μA.prod μB).map (fun p : G × G => p.1 * p.2) with hρ
  have hK : ∀ x : G, ∃ K, IsCompact K ∧ K ∈ nhds x := fun x => exists_compact_mem_nhds x
  choose K hKc hKn using hK
  have hmeasK : ∀ x, MeasurableSet (K x) := fun x => (hKc x).isClosed.measurableSet
  let h : G → G → ℝ≥0∞ := fun x y => ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ
  have hhm : ∀ x, Measurable (h x) := by
    intro x
    have hq : Measurable fun q : G × G => (K x).indicator (1 : G → ℝ≥0∞) (q.2 * q.1) :=
      (measurable_one.indicator (hmeasK x)).comp (measurable_snd.mul measurable_fst)
    exact hq.lintegral_prod_right'
  have hint : ∀ x, ∫⁻ y, h x y ∂ν = μG (K x) := by
    intro x
    show ∫⁻ y, ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ ∂ν = μG (K x)
    rw [← hW _ (measurable_one.indicator (hmeasK x)), lintegral_indicator_one (hmeasK x)]
  have hpos : ∀ x y, y ∈ interior (K x) → 0 < h x y := by
    intro x y hy
    let O := (fun s : G => s * y) ⁻¹' interior (K x)
    have hOo : IsOpen O := isOpen_interior.preimage (continuous_id.mul continuous_const)
    have hO1 : (1 : G) ∈ O := by simp [O, hy]
    have hρO : 0 < ρ O := pos_open_one_mul A B μA μB hA0 hAc hAi hB0 hBc hBi O hOo hO1
    have hle : ∫⁻ s, O.indicator 1 s ∂ρ ≤ ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ := by
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ O
      · have hs' : s * y ∈ K x := interior_subset hs
        simp [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
      · simp [hs]
    rw [lintegral_indicator_one hOo.measurableSet] at hle
    exact lt_of_lt_of_le hρO hle
  obtain ⟨T, hT, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x => interior (K x)) (fun _ => isOpen_interior)
  have := hT.to_subtype
  let E : T × ℕ → Set G := fun p => {y | ((p.2 : ℝ≥0∞) + 1)⁻¹ ≤ h p.1 y}
  refine Measure.sigmaFinite_of_countable (S := Set.range E) (Set.countable_range E) ?_ ?_
  · rintro _ ⟨⟨x, n⟩, rfl⟩
    have hne0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have hneT : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simp)
    calc ν (E (x, n)) ≤ (∫⁻ y, h x y ∂ν) / ((n : ℝ≥0∞) + 1)⁻¹ :=
          meas_ge_le_lintegral_div (hhm x).aemeasurable hne0 hneT
      _ < ⊤ := by
        rw [hint]
        exact ENNReal.div_lt_top (hKc x).measure_lt_top.ne hne0
  · refine Set.eq_univ_of_forall fun y => ?_
    have hy : y ∈ ⋃ x ∈ T, interior (K x) := by
      rw [hTU]
      exact Set.mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hKn y)⟩
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x y hyx).ne'
    refine Set.mem_sUnion.2 ⟨E (⟨x, hxT⟩, n), ⟨_, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ h x y
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

end PI.UnitaryGroupMassFormula.QuotNuSigma

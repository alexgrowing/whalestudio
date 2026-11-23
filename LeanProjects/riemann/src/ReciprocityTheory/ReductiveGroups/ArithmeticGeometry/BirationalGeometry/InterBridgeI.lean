import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeH

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem pushForward_null' [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  rw [mInt, dif_pos hne, integralWith]
  generalize hne.some = Pt
  have hnull : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume) ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null
        (show goodT A q j ∩ (A.chart j).symm ⁻¹' S ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' S from
          fun u hu => ⟨hu.1.1, hu.2⟩) (hS j)
  have hfinj : ∀ j, ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)),
      (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [compl_mem_ae_iff.2 (hnull j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u)) ∧
      ∫ u in goodT A q j, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u = ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y := fun j =>
    area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ g hg j).mono_set (fun u hu => hu.1)) (hfinj j)
  have htarget : ∀ j, ∫ u in (A.chart j).target, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u = ∫ u in goodT A q j, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u := by
    intro j
    apply setIntegral_congr_set
    rw [ae_eq_set]
    refine ⟨measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j), ?_⟩
    rw [diff_eq_empty.2 (fun u hu => hu.1)]
    exact measure_empty
  have hj : ∀ j y, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) →
      fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y =
        ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * (g x * pushDens A Φ q x) := by
    intro j y hy
    unfold fibSum
    rw [goodT_fibre_eq A q S hq j hy, finsum_mem_image ((A.chart j).injOn.mono inter_subset_left)]
    calc _ = ∑ᶠ x ∈ (A.chart j).source ∩ (q ⁻¹' {y} \ S), Pt.χ j x * (g x * pushDens A Φ q x) :=
          finsum_mem_congr rfl (fun x hx => fib_term A Φ hΦ q S hq Pt g j hx.1 hx.2.2)
      _ = _ := by
          apply finsum_mem_inter_support_eq
          ext x
          simp only [mem_inter_iff, Function.mem_support]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩
            exact ⟨h2, h3⟩
          · rintro ⟨h2, h3⟩
            exact ⟨⟨Pt.tsupport_subset j (subset_tsupport _ (left_ne_zero_of_mul h3)), h2⟩, h3⟩
  have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)),
      ∀ j, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) := by
    rw [ae_all_iff]
    intro j
    exact compl_mem_ae_iff.2 (hnull j)
  calc ∑ j, ∫ u in (A.chart j).target, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u
      = ∑ j, ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y :=
        Finset.sum_congr rfl (fun j _ => (htarget j).trans (harea j).2)
    _ = ∫ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y :=
        (integral_finset_sum _ (fun j _ => (harea j).1)).symm
    _ = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
        apply integral_congr_ae
        filter_upwards [hae] with y hy
        have hF := hfin y
        calc ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y
            = ∑ j, ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * (g x * pushDens A Φ q x) :=
              Finset.sum_congr rfl (fun j _ => hj j y (hy j))
          _ = ∑ j, ∑ x ∈ hF.toFinset, Pt.χ j x * (g x * pushDens A Φ q x) :=
              Finset.sum_congr rfl (fun j _ => finsum_mem_eq_finite_toFinset_sum _ hF)
          _ = ∑ x ∈ hF.toFinset, g x * pushDens A Φ q x := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun x _ => ?_)
              rw [← Finset.sum_mul, Pt.sum_eq_one, one_mul]
          _ = ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x :=
              (finsum_mem_eq_finite_toFinset_sum _ hF).symm

end ReciprocityTheory.ChartRestriction.G.Geo

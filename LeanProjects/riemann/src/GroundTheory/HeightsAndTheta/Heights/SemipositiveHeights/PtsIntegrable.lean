import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterHironaka
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo

section PushForward

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem pushForward_integrable [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x) := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set Pt := hne.some with hPt
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u with hhj
  set Qj : Fin A.n → (Fin e → ℂ) → (Fin e → ℂ) := fun j => q ∘ (A.chart j).symm with hQj
  set N : Fin A.n → Set (Fin e → ℂ) :=
    fun j => Qj j '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) with hNdef
  have hN : ∀ j, volume (N j) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null (inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j)
  have hfib : ∀ j, ∀ y ∉ N j, goodT A q j ∩ Qj j ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) :=
    fun j y hy => goodT_fibre_eq A q S hq j hy
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ Qj j ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [hfib j y hy]
    exact ((hfin y).subset inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (Qj j) (hj j)) := fun j =>
    (area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ g hg j).mono_set fun u hu => hu.1) (hfinj j)).1
  refine (integrable_finsetSum Finset.univ fun j _ => harea j).congr ?_
  have hNall : ∀ᵐ y, ∀ j, y ∉ N j :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hN j)
  filter_upwards [hNall] with y hy
  have hterm : ∀ j, fibSum (goodT A q j) (Qj j) (hj j) y =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * (g x * pushDens A Φ q x) := by
    intro j
    unfold fibSum
    rw [hfib j y (hy j), finsum_mem_image ((A.chart j).injOn.mono inter_subset_left)]
    refine (finsum_mem_congr (g := fun x => Pt.χ j x * (g x * pushDens A Φ q x)) rfl
      fun x hx => ?_).trans ?_
    · exact fib_term A Φ hΦ q S hq Pt g j hx.1 hx.2.2
    · refine finsum_mem_inter_support_eq' _ _ _ fun x hx => ?_
      have hχ : Pt.χ j x ≠ 0 := left_ne_zero_of_mul hx
      have hxs : x ∈ (A.chart j).source := Pt.tsupport_subset j (subset_tsupport _ hχ)
      exact ⟨fun h => h.2, fun h => ⟨hxs, h⟩⟩
  simp_rw [hterm]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, Pt.sum_eq_one x, one_mul]

end PushForward

theorem PtsIntegrable.of_resExists (hE : ResExistsStatement) : PtsIntegrableStatement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  exact (pushForward_integrable R.A (fun j => potOf R (L j)) (fun j => potOf_isPotential R (L j) (hL j))
    (brQ R Ψ) (brBad R Ψ) (brBad_null R Ψ hP hΨ) (brGood R Ψ) (brFib_finite R Ψ hP hΨ) _
    (brIntegrable R L A s hP hL hA hs)).congr ((brFibreSum_ae R Ψ L A s hP hΨ hL hA hs).mono fun y hy => hy.symm)

end GroundTheory.Heights₂.Heights.ForSecondHalf

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

section FibreMeas

variable {e : ℕ}

theorem fibSum_eq_sub_of_finite {O : Set (Fin e → ℂ)} {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (h : (Fin e → ℂ) → ℝ) (y : Fin e → ℂ) (hy : (O ∩ Q ⁻¹' {y}).Finite) :
    fibSum O Q (fun u => max (h u) 0) y - fibSum O Q (fun u => max (-h u) 0) y = fibSum O Q h y := by
  unfold fibSum
  rw [← finsum_mem_sub_distrib _ _ hy]
  refine finsum_mem_congr rfl fun u _ => ?_
  rw [← sub_div, max_zero_sub_max_neg_zero_eq_self]

theorem aemeasurable_fibSum_of_nonneg {O : Set (Fin e → ℂ)} (hO : IsOpen O)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : ∀ u, 0 ≤ h u) (hm : Measurable h)
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) : AEMeasurable (fibSum O Q h) := by
  have h1 := (LintegralFibSum.lintegral_fibSum_open hO hQ hh
    (hm.comp measurable_subtype_coe) hfin).1
  refine h1.ennreal_toReal.congr (Eventually.of_forall fun y => ?_)
  exact ENNReal.toReal_ofReal (LintegralFibSum.fibSum_nonneg _ _ hh y)

theorem aestronglyMeasurable_fibSum {O : Set (Fin e → ℂ)} (hO : IsOpen O)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hm : AEStronglyMeasurable h (volume.restrict O))
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) : AEStronglyMeasurable (fibSum O Q h) volume := by
  have hmm : Measurable (hm.mk h) := hm.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ u, u ∈ O → h u = hm.mk h u :=
    (ae_restrict_iff' hO.measurableSet).mp hm.ae_eq_mk
  have hnull : volume (O ∩ {u | h u ≠ hm.mk h u}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    rintro u ⟨huO, hne⟩ hu
    exact hne (hu huO)
  have himg : volume (Q '' (O ∩ {u | h u ≠ hm.mk h u})) = 0 := by
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hnull
    intro u hu
    exact ((hQ u hu.1).1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  have hp : AEMeasurable (fibSum O Q fun u => max (hm.mk h u) 0) :=
    aemeasurable_fibSum_of_nonneg hO hQ (fun u => le_max_right _ _) (hmm.max measurable_const) hfin
  have hn : AEMeasurable (fibSum O Q fun u => max (-hm.mk h u) 0) :=
    aemeasurable_fibSum_of_nonneg hO hQ (fun u => le_max_right _ _) (hmm.neg.max measurable_const) hfin
  refine (hp.sub hn).aestronglyMeasurable.congr ?_
  filter_upwards [hfin, measure_eq_zero_iff_ae_notMem.mp himg] with y hy hyn
  show fibSum O Q (fun u => max (hm.mk h u) 0) y - fibSum O Q (fun u => max (-hm.mk h u) 0) y = _
  rw [fibSum_eq_sub_of_finite _ y hy]
  unfold fibSum
  refine finsum_mem_congr rfl fun u hu => ?_
  have : h u = hm.mk h u := by
    by_contra hne
    exact hyn ⟨u, ⟨hu.1, hne⟩, hu.2⟩
  rw [this]

end FibreMeas

theorem aestronglyMeasurable_fibreSum_pushDens : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → (∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u) (volume.restrict (A.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) volume := by
  intro e X _ _ _ A Φ q S G hS hq hfin hsm hG
  classical
  obtain ⟨Pt⟩ := existsPartition A
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * (G ((A.chart j).symm u) * locDens A Φ j u) with hhj
  have hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null
        (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j)
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have hχc : ∀ j, ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
    intro j
    have := (Pt.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hjm : ∀ j, AEStronglyMeasurable (hj j) (volume.restrict (goodT A q j)) := fun j =>
    (((hχc j).aestronglyMeasurable (A.chart j).open_target.measurableSet).mul (hG j)).mono_measure
      (Measure.restrict_mono (fun u hu => hu.1) le_rfl)
  have hsum := sum_fibSum_ae A q S hN hq hfin Pt hj (fun x => G x * pushDens A Φ q x) (by
    intro j x hx hxS
    have hd := locDens_div_jacN A Φ q S hq hsm j hx hxS
    simp only [hhj, (A.chart j).left_inv hx]
    rw [← hd]
    ring)
  exact (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
    aestronglyMeasurable_fibSum (isOpen_goodT A q j) (fun u hu => hu.2) (hjm j) (hfinj j)).congr hsum

end GlobalTheory.CompanionTheory.Ar.Giv.Push

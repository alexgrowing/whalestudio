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

open LintegralFibSum

theorem lintegral_absFibre_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (hGm : ∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u)
      (volume.restrict (A.chart j).target))
    (Pt : ChartPartition A) :
    ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|) =
      ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal
        |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| := by
  classical
  set Qj : Fin A.n → (Fin e → ℂ) → (Fin e → ℂ) := fun j => q ∘ (A.chart j).symm with hQj
  set h : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| with hh
  have hms : ∀ j, MeasurableSet (A.chart j).target := fun j => (A.chart j).open_target.measurableSet
  have hdiff : ∀ j (s : Set (Fin e → ℂ)), s ⊆ goodT A q j → volume s = 0 →
      volume (Qj j '' s) = 0 := by
    intro j s hs h0
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ h0
    intro u hu
    exact ((hs hu).2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  have hN : ∀ j, volume (Qj j '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := fun j =>
    hdiff j _ Set.inter_subset_left
      (measure_mono_null (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j))
  have hTn : ∀ j, volume ((A.chart j).target \ goodT A q j) = 0 := fun j =>
    measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j)
  have hgt : ∀ j, goodT A q j =ᵐ[volume] (A.chart j).target := by
    intro j
    refine ae_eq_set.mpr ⟨?_, hTn j⟩
    have : goodT A q j \ (A.chart j).target = ∅ := Set.diff_eq_empty.mpr fun u hu => hu.1
    rw [this]
    exact measure_empty
  have hAE : ∀ j, AEMeasurable (h j) (volume.restrict (A.chart j).target) := by
    intro j
    have hχ : ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
      have := (Pt.smooth j j).continuousOn
      rw [Set.preimage_univ, Set.inter_univ] at this
      exact this
    have h1 := hχ.aestronglyMeasurable (μ := volume) (hms j)
    have h2 := (h1.mul (hGm j)).norm
    refine h2.aemeasurable.congr (ae_of_all _ fun u => ?_)
    simp only [hh, Real.norm_eq_abs, Pi.mul_apply, mul_assoc]
  set h' : Fin A.n → (Fin e → ℂ) → ℝ := fun j u => |(hAE j).mk (h j) u| with hh'
  have hm' : ∀ j, Measurable (h' j) := fun j =>
    continuous_abs.measurable.comp (hAE j).measurable_mk
  have heq : ∀ j, ∀ᵐ u, u ∈ (A.chart j).target → h j u = h' j u := by
    intro j
    filter_upwards [(ae_restrict_iff' (hms j)).mp (hAE j).ae_eq_mk] with u hu ht
    have h0 : 0 ≤ h j u := abs_nonneg _
    show h j u = |(hAE j).mk (h j) u|
    rw [← hu ht, abs_of_nonneg h0]
  have hD : ∀ j, volume (Qj j '' (goodT A q j ∩ {u | h j u ≠ h' j u})) = 0 := fun j =>
    hdiff j _ Set.inter_subset_left
      (measure_mono_null (t := {u | ¬ (u ∈ (A.chart j).target → h j u = h' j u)})
        (fun u hu hc => hu.2 (hc hu.1.1)) (ae_iff.mp (heq j)))
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ Qj j ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [show goodT A q j ∩ Qj j ⁻¹' {y} = _ from goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have hlow : ∀ j, AEMeasurable (fun y => ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y) =
        ∫⁻ u in goodT A q j, ENNReal.ofReal (h' j u) := fun j =>
    lintegral_fibSum_open (isOpen_goodT A q j) (fun u hu => hu.2) (fun u => abs_nonneg _)
      ((hm' j).comp measurable_subtype_coe) (hfinj j)
  have hsame : ∀ᵐ y, ∀ j, fibSum (goodT A q j) (Qj j) (h j) y =
      fibSum (goodT A q j) (Qj j) (h' j) y := by
    refine ae_all_iff.mpr fun j => ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hD j)] with y hy
    unfold fibSum
    refine finsum_mem_congr rfl fun u hu => ?_
    have : h j u = h' j u := by
      by_contra hne
      exact hy ⟨u, ⟨hu.1, hne⟩, hu.2⟩
    rw [this]
  have hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
        Pt.χ j x * |G x * pushDens A Φ q x| := by
    intro j x hx hxS
    have hJ : 0 ≤ jacN (q ∘ (A.chart j).symm) (A.chart j x) := by unfold jacN; positivity
    have hd := locDens_div_jacN A Φ q S hq hsm j hx hxS
    calc h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x)
        = |Pt.χ j x * G x * (locDens A Φ j (A.chart j x) /
            jacN (q ∘ (A.chart j).symm) (A.chart j x))| := by
          simp only [hh, (A.chart j).left_inv hx]
          rw [← mul_div_assoc, abs_div, abs_of_nonneg hJ]
      _ = Pt.χ j x * |G x * pushDens A Φ q x| := by
          rw [hd, mul_assoc, abs_mul, abs_of_nonneg (Pt.nonneg j x)]
  have hae := sum_fibSum_ae A q S hN hq hfin Pt h (fun x => |G x * pushDens A Φ q x|) hterm
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|)
      = ∫⁻ y, ∑ j, ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae, hsame] with y hy hs
        rw [← hy, ENNReal.ofReal_sum_of_nonneg fun j _ =>
          fibSum_nonneg _ _ (fun u => abs_nonneg _) y]
        exact Finset.sum_congr rfl fun j _ => by rw [hs j]
    _ = ∑ j, ∫⁻ u in goodT A q j, ENNReal.ofReal (h' j u) := by
        rw [lintegral_finsetSum' _ fun j _ => (hlow j).1]
        exact Finset.sum_congr rfl fun j _ => (hlow j).2
    _ = ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal (h j u) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [setLIntegral_congr (hgt j)]
        refine lintegral_congr_ae ?_
        filter_upwards [(ae_restrict_iff' (hms j)).mpr (heq j)] with u hu
        rw [hu]

end GlobalTheory.CompanionTheory.Ar.Giv.Push

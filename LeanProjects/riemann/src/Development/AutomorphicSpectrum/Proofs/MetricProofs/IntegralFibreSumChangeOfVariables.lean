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

theorem integrable_mInt_fibreSum {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (hG : MIntegrable A Φ G) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧
      mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A Φ G = integralWith A hne.some Φ G := by unfold mInt; rw [dif_pos hne]
  set Pt := hne.some with hPt
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u with hhj
  have hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1)
        (hS j)
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j)) ∧
      ∫ u in goodT A q j, hj j u = ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y :=
    fun j => area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ G hG j).mono_set fun u hu => hu.1) (hfinj j)
  have hset : ∀ j, ∫ u in (A.chart j).target, hj j u = ∫ u in goodT A q j, hj j u := by
    intro j
    refine setIntegral_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j)
    · rw [Set.sdiff_eq_empty.mpr fun u hu => hu.1]; exact measure_empty
  have hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      hj j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
        Pt.χ j x * (G x * pushDens A Φ q x) := by
    intro j x hx hxS
    simp only [hhj, (A.chart j).left_inv hx]
    rw [mul_div_assoc, locDens_div_jacN A Φ q S hq hsm j hx hxS, mul_assoc]
  have hae := sum_fibSum_ae A q S hN hq hfin Pt hj (fun x => G x * pushDens A Φ q x) hterm
  refine ⟨(integrable_finsetSum Finset.univ fun j _ => (harea j).1).congr hae, ?_⟩
  rw [hm]
  unfold integralWith
  have hsum : ∑ j, ∫ u in (A.chart j).target, hj j u =
      ∫ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y := by
    rw [integral_finsetSum _ fun j _ => (harea j).1]
    exact Finset.sum_congr rfl fun j _ => (hset j).trans (harea j).2
  exact hsum.trans (integral_congr_ae hae)

end GlobalTheory.CompanionTheory.Ar.Giv.Push

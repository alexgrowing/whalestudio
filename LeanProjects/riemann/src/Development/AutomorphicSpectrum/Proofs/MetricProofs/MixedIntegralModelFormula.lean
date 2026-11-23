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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartIntegralPotentialLocallyFiniteStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothLocalPotentialLiftStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteFibresOfAnalyticLocalDiffeoStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableFibreCountOfLocalDiffeoStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralFibreSumChangeOfVariablesStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem push_chart_integrals : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → (∀ j, AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (volume.restrict (M.atlas.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) volume ∧ (∀ Pt : ChartPartition M.atlas, ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w|) = ∑ j, ∫⁻ u in (M.atlas.chart j).target, ENNReal.ofReal |Pt.χ j ((M.atlas.chart j).symm u) * G₀ ((M.atlas.chart j).symm u) * locDens M.atlas (Φ) j u|) ∧ (MIntegrable M.atlas Φ G₀ → Integrable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) ∧ ptsIntegralAt P Q (fun i z => c i * Real.log ((B i).h z)) g = mInt M.atlas Φ G₀) := by
  intro K _ ι _ P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg hG
  have hS : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelBad M Q (Yᶜ ∪ Z)) = 0 := by
    intro j
    rw [modelBad, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (hnull j) (GlobalTheory.T.volume_modelCrit_chart_eq_zero K ι P n M Q j hP hQ)
  have hq := modelQ_good_of_notMem M Q (Yᶜ ∪ Z)
  have hfin : ∀ y, (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)).Finite := fun y =>
    (ModelFibreFinite.proof K ι P n M Q hP hQ y).subset (Set.sdiff_subset_sdiff_right Set.subset_union_right)
  have hYof : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), x ∈ Y := fun x hx => by
    by_contra h
    exact hx (Or.inl (Or.inl h))
  have hsm : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), ∀ i k, x ∈ (M.atlas.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) := by
    intro x hx i k hk
    have hxk : (M.atlas.chart k).symm (M.atlas.chart k x) = x := (M.atlas.chart k).left_inv hk
    have hmem : M.atlas.chart k x ∈ (M.atlas.chart k).target ∩ (M.atlas.chart k).symm ⁻¹' ((Φ i).U x ∩ Y) :=
      ⟨(M.atlas.chart k).map_source hk, by
        rw [Set.mem_preimage, hxk]; exact ⟨(Φ i).mem_U x, hYof x hx⟩⟩
    have hop := (M.atlas.chart k).isOpen_inter_preimage_symm (((Φ i).isOpen_U x).inter hY)
    exact ((hΦs i x k).contDiffAt (hop.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  have hYnull : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Yᶜ) = 0 := fun j =>
    measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.subset_union_left)) (hnull j)
  have hm : ∀ j, AEStronglyMeasurable (fun u => G₀ ((M.atlas.chart j).symm u) * locDens M.atlas Φ j u)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    let _ : MeasurableSpace M.Xc := borel M.Xc
    have : BorelSpace M.Xc := ⟨rfl⟩
    refine AEStronglyMeasurable.mul (hG j) ?_
    rw [MeasOff.restrict_target_eq M.atlas hYnull j]
    exact ((GlobalTheory.T.smooth_local_potential_lift K ι P n M Y c B Φ j hY hΦs hΦt).aestronglyMeasurable
      (MeasOff.isOpen_ov M.atlas hY j).measurableSet)
  have hae := GlobalTheory.T.chart_integral_potential_locally_finite K ι P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg
  have e1 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), G₀ x * pushDens M.atlas Φ (modelQ M Q) x := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl ht
  have e2 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w| =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), |G₀ x * pushDens M.atlas Φ (modelQ M Q) x| := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl fun x hx => by rw [ht x hx]
  refine ⟨(GlobalTheory.T.measurable_fibre_count_of_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm).congr (e1.mono fun y hy => hy.symm),
    fun Pt => ?_, fun hI => ?_⟩
  · rw [lintegral_congr_ae (e2.mono fun y hy => congrArg ENNReal.ofReal hy)]
    exact GlobalTheory.T.finite_fibres_of_analytic_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm Pt
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_fibre_sum_change_of_variables M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hI
    refine ⟨h1.congr (e1.mono fun y hy => hy.symm), ?_⟩
    rw [h2]
    exact integral_congr_ae (e1.mono fun y hy => hy)

end GlobalTheory.CompanionTheory.Ar.Giv

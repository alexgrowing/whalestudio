import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartMongeAmpereL1Hypotheses
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Filter Topology Set
open scoped ENNReal
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure ChartPartition locDens)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

namespace ChartMongeAmpereL1Measure

theorem aestronglyMeasurable_map_symm {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (b : OpenPartialHomeomorph X (Fin D → ℂ)) {M : Set (Fin D → ℂ)}
    (hM : MeasurableSet M) (hMt : M ⊆ b.target) {g : X → ℝ}
    (hg : AEStronglyMeasurable (fun z => g (b.symm z)) (volume.restrict M)) :
    AEStronglyMeasurable g ((volume.restrict M).map b.symm) := by
  classical
  set ψ : X → (Fin D → ℂ) := b.source.piecewise b (fun _ => 0) with hψ
  have hψm : Measurable ψ :=
    b.continuousOn.measurable_piecewise continuousOn_const b.open_source.measurableSet
  set bad : Set (Fin D → ℂ) := {z | g (b.symm z) ≠ hg.mk _ z} with hbad
  have hbad0 : (volume.restrict M) bad = 0 := ae_iff.1 hg.ae_eq_mk
  set N := toMeasurable (volume.restrict M) bad with hN
  have hN0 : (volume.restrict M) N = 0 := by rw [hN, measure_toMeasurable]; exact hbad0
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  set S : Set X := ψ ⁻¹' (N ∪ Mᶜ) ∪ b.sourceᶜ with hS
  have hSm : MeasurableSet S :=
    (hψm (hNm.union hM.compl)).union b.open_source.measurableSet.compl
  have hsymm : AEMeasurable b.symm (volume.restrict M) :=
    (b.continuousOn_symm.mono hMt).aemeasurable hM
  refine ⟨fun x => hg.mk _ (ψ x), hg.stronglyMeasurable_mk.comp_measurable hψm, ?_⟩
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (t := S) ?_ ?_
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    by_contra hxS
    simp only [hS, mem_union, mem_preimage, mem_compl_iff, not_or, not_not] at hxS
    obtain ⟨⟨hxN, hxM⟩, hxs⟩ := hxS
    have hψx : ψ x = b x := by simp [hψ, hxs]
    rw [hψx] at hxN hxM hx
    have hxb : g (b.symm (b x)) = hg.mk _ (b x) := by
      by_contra h
      exact hxN (subset_toMeasurable _ _ h)
    rw [b.left_inv hxs] at hxb
    exact hx hxb
  · rw [Measure.map_apply_of_aemeasurable hsymm hSm, Measure.restrict_apply' hM]
    refine measure_mono_null (t := N ∩ M) ?_ ?_
    · rintro z ⟨hz, hzM⟩
      refine ⟨?_, hzM⟩
      have hzs : b.symm z ∈ b.source := b.map_target (hMt hzM)
      have hψz : ψ (b.symm z) = z := by simp [hψ, hzs, b.right_inv (hMt hzM)]
      simp only [hS, mem_preimage, mem_union, mem_compl_iff, hψz] at hz
      rcases hz with (hz | hz) | hz
      · exact hz
      · exact absurd hzM hz
      · exact absurd hzs hz
    · rwa [← Measure.restrict_apply hNm]

theorem lintegral_chart_change {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (a b : OpenPartialHomeomorph X (Fin D → ℂ))
    (hab : AnalyticOnNhd ℂ (a ∘ b.symm) (b.target ∩ b.symm ⁻¹' a.source))
    {K M : Set X} (hK : IsClosed K) (hKa : K ⊆ a.source) (hM : IsOpen M)
    (hMb : closure M ⊆ b.source) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ F : X → ℝ≥0∞,
      ∫⁻ y in a.target, (K ∩ M).indicator F (a.symm y) ≤
        B * ∫⁻ z in b.target ∩ b.symm ⁻¹' M, F (b.symm z) := by
  set τ : (Fin D → ℂ) → (Fin D → ℂ) := a ∘ b.symm with hτ
  set O := b.target ∩ b.symm ⁻¹' a.source with hO
  have hOo : IsOpen O := b.isOpen_inter_preimage_symm a.open_source
  set J : (Fin D → ℂ) → ℝ := fun z => Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det with hJ
  have hJc : ContinuousOn J O := by
    have hfd : ContinuousOn (fun z => fderiv ℂ τ z) O :=
      (hab.contDiffOn (n := 1) hOo.uniqueDiffOn).continuousOn_fderiv_of_isOpen hOo le_rfl
    have hjac : ContinuousOn (fun z => ReciprocityTheory.AnForm.A.jacC τ z) O := by
      refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
      exact (continuous_apply i).comp_continuousOn (hfd.clm_apply continuousOn_const)
    exact Complex.continuous_normSq.comp_continuousOn
      ((continuous_id.matrix_det).comp_continuousOn hjac)
  set L := b '' (K ∩ closure M) with hL
  have hLc : IsCompact L :=
    (hK.inter isClosed_closure).isCompact.image_of_continuousOn
      (b.continuousOn.mono (inter_subset_right.trans hMb))
  have hLO : L ⊆ O := by
    rintro _ ⟨x, ⟨hxK, hxM⟩, rfl⟩
    refine ⟨b.map_source (hMb hxM), ?_⟩
    simp only [mem_preimage, b.left_inv (hMb hxM)]
    exact hKa hxK
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn (hJc.mono hLO)
  set U := b.target ∩ b.symm ⁻¹' (a.source ∩ M) with hU
  have hUo : IsOpen U := b.isOpen_inter_preimage_symm (a.open_source.inter hM)
  have hUO : U ⊆ O := fun z hz => ⟨hz.1, hz.2.1⟩
  have hinj : InjOn τ U := by
    intro z hz z' hz' h
    have h1 : b.symm z = b.symm z' := a.injOn hz.2.1 hz'.2.1 h
    rw [← b.right_inv hz.1, ← b.right_inv hz'.1, h1]
  set V := a.target ∩ a.symm ⁻¹' M with hV
  have hVo : IsOpen V := a.isOpen_inter_preimage_symm hM
  have hτU : τ '' U = V := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨a.map_source hz.2.1, ?_⟩
      simp only [hτ, Function.comp_apply, mem_preimage, a.left_inv hz.2.1]
      exact hz.2.2
    · rintro ⟨hy, hyM⟩
      have hys : a.symm y ∈ b.source := subset_closure.trans hMb hyM
      refine ⟨b (a.symm y), ⟨b.map_source hys, ?_⟩, ?_⟩
      · simp only [mem_preimage, b.left_inv hys]
        exact ⟨a.map_target hy, hyM⟩
      · simp only [hτ, Function.comp_apply, b.left_inv hys, a.right_inv hy]
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun F => ?_⟩
  set f : (Fin D → ℂ) → ℝ≥0∞ := fun y => (K ∩ M).indicator F (a.symm y) with hf
  have h1 : ∫⁻ y in a.target, f y ≤ ∫⁻ y in V, f y := by
    have hc : ∫⁻ y in a.target, f y = ∫⁻ y in a.target, V.indicator f y := by
      refine setLIntegral_congr_fun a.open_target.measurableSet fun y hy => ?_
      by_cases hyM : a.symm y ∈ M
      · rw [indicator_of_mem (show y ∈ V from ⟨hy, hyM⟩)]
      · rw [indicator_of_notMem (fun h : y ∈ V => hyM h.2)]
        simp [hf, indicator_of_notMem (fun h : a.symm y ∈ K ∩ M => hyM h.2)]
    rw [hc, ← lintegral_indicator hVo.measurableSet]
    exact setLIntegral_le_lintegral _ _
  refine h1.trans ?_
  rw [← hτU, ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ U hUo
    (hab.mono hUO) hinj f]
  calc ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) * f (τ z)
      ≤ ∫⁻ z in U, ENNReal.ofReal C * F (b.symm z) := by
        refine setLIntegral_mono' hUo.measurableSet fun z hz => ?_
        have hfz : f (τ z) = (K ∩ M).indicator F (b.symm z) := by
          simp only [hf, hτ, Function.comp_apply, a.left_inv hz.2.1]
        rw [hfz]
        by_cases hzK : b.symm z ∈ K ∩ M
        · rw [indicator_of_mem hzK]
          have hzL : z ∈ L := ⟨b.symm z, ⟨hzK.1, subset_closure hzK.2⟩, b.right_inv hz.1⟩
          have := hC z hzL
          rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)] at this
          gcongr
        · rw [indicator_of_notMem hzK, mul_zero]
          exact zero_le
    _ = ENNReal.ofReal C * ∫⁻ z in U, F (b.symm z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ z in b.target ∩ b.symm ⁻¹' M, F (b.symm z) :=
        by gcongr; exact fun z hz => ⟨hz.1, hz.2.2⟩

theorem density_bound {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : FinHolAtlas D X) (Q : ChartPartition A) (Φ : Fin D → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ y ∈ (A.chart j).target,
      ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y) ≤
        (tsupport (Q.χ j)).indicator (fun _ => c) ((A.chart j).symm y) := by
  obtain ⟨hKc, hKT⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j)
    (isClosed_tsupport (Q.χ j)) (Q.tsupport_subset j)
  obtain ⟨C, hC⟩ :=
    hKc.exists_bound_of_continuousOn ((ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j).mono hKT)
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun y hy => ?_⟩
  by_cases hx : (A.chart j).symm y ∈ tsupport (Q.χ j)
  · rw [indicator_of_mem hx]
    apply ENNReal.ofReal_le_ofReal
    have hyK : y ∈ (A.chart j) '' tsupport (Q.χ j) := ⟨_, hx, (A.chart j).right_inv hy⟩
    have h1 := hC y hyK
    have h0 := Q.nonneg j ((A.chart j).symm y)
    have h2 := ReciprocityTheory.AnForm.M.chi_le_one Q j ((A.chart j).symm y)
    rw [Real.norm_eq_abs] at h1
    calc Q.χ j ((A.chart j).symm y) * locDens A Φ j y
        ≤ Q.χ j ((A.chart j).symm y) * |locDens A Φ j y| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ 1 * C := mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul,
      ENNReal.ofReal_zero]

theorem maMeasure_le_smul_sum {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas D X) (P : PotentialCharts A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      maMeasure A Φ ≤ C • ∑ k, (volume.restrict (P.chartMid k)).map (P.chart k).symm := by
  by_cases hne : Nonempty (ChartPartition A)
  swap
  · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    simp [maMeasure, dif_neg hne]
  set Q := hne.some with hQ
  choose c hc hcb using fun j => density_bound A Q Φ hΦ j
  choose B hB hBb using fun (j : Fin A.n) (k : Fin P.N) =>
    lintegral_chart_change (A.chart j) (P.chart k) ((P.compat k j).2) (isClosed_tsupport (Q.χ j))
      (Q.tsupport_subset j) (P.isOpen_mid k) (P.closure_mid k)
  refine ⟨∑ j, ∑ k, c j * B j k, ?_, ?_⟩
  · exact ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (hc j) (hB j k)
  rw [Measure.le_iff]
  intro s hs
  set F : X → ℝ≥0∞ := s.indicator 1 with hF
  have hFm : Measurable F := measurable_const.indicator hs
  have hν : ∀ k, ((volume.restrict (P.chartMid k)).map (P.chart k).symm) s =
      ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) := by
    intro k
    have hMm : MeasurableSet (P.chartMid k) :=
      ((P.chart k).isOpen_inter_preimage_symm (P.isOpen_mid k)).measurableSet
    have hsy : AEMeasurable (P.chart k).symm (volume.restrict (P.chartMid k)) :=
      ((P.chart k).continuousOn_symm.mono inter_subset_left).aemeasurable hMm
    rw [← lintegral_indicator_one hs, ← hF, lintegral_map' hFm.aemeasurable hsy]
  have hμ : ∀ j, ReciprocityTheory.AnForm.M.chartMeasure A Q Φ j s ≤
      ∑ k, c j * B j k * ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) := by
    intro j
    have hTm := (A.chart j).open_target.measurableSet
    have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable hTm
    have hsymm' := hsymm.mono_ac (withDensity_absolutelyContinuous
      (volume.restrict (A.chart j).target)
      fun y => ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y))
    have hw : AEMeasurable (fun y => ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y))
        (volume.restrict (A.chart j).target) :=
      (((ReciprocityTheory.AnForm.M.chi_comp_continuousOn Q j).mul
        (ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j)).aemeasurable hTm).ennreal_ofReal
    have hpiece : ∀ k, AEMeasurable
        (fun y => (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y))
        (volume.restrict (A.chart j).target) := fun k =>
      (hFm.indicator ((isClosed_tsupport _).measurableSet.inter
        (P.isOpen_mid k).measurableSet)).comp_aemeasurable hsymm
    calc ReciprocityTheory.AnForm.M.chartMeasure A Q Φ j s
        = ∫⁻ y in (A.chart j).target, ENNReal.ofReal (Q.χ j ((A.chart j).symm y) *
            locDens A Φ j y) * F ((A.chart j).symm y) := by
          unfold ReciprocityTheory.AnForm.M.chartMeasure
          rw [← lintegral_indicator_one hs, ← hF, lintegral_map' hFm.aemeasurable hsymm']
          exact lintegral_withDensity_eq_lintegral_mul₀ hw (hFm.comp_aemeasurable hsymm)
      _ ≤ ∫⁻ y in (A.chart j).target,
            ∑ k, c j * (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y) := by
          refine setLIntegral_mono' hTm fun y hy => ?_
          have h1 := hcb j y hy
          by_cases hx : (A.chart j).symm y ∈ tsupport (Q.χ j)
          · rw [indicator_of_mem hx] at h1
            obtain ⟨k0, hk0⟩ := P.cover ((A.chart j).symm y)
            have hk0' := P.inner_subset_mid k0 hk0
            calc _ ≤ c j * F ((A.chart j).symm y) := by gcongr
              _ = c j * (tsupport (Q.χ j) ∩ P.mid k0).indicator F ((A.chart j).symm y) := by
                rw [indicator_of_mem (show (A.chart j).symm y ∈ tsupport (Q.χ j) ∩ P.mid k0
                  from ⟨hx, hk0'⟩)]
              _ ≤ _ := Finset.single_le_sum (f := fun k =>
                  c j * (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y))
                  (fun _ _ => zero_le) (Finset.mem_univ k0)
          · rw [indicator_of_notMem hx] at h1
            have : ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y) = 0 :=
              le_antisymm h1 zero_le
            rw [this, zero_mul]
            exact zero_le
      _ = ∑ k, c j * ∫⁻ y in (A.chart j).target,
            (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y) := by
          rw [lintegral_finsetSum' _ fun k _ => (hpiece k).const_mul (c j)]
          exact Finset.sum_congr rfl fun k _ => lintegral_const_mul' _ _ (hc j)
      _ ≤ ∑ k, c j * B j k * ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [mul_assoc]
          gcongr
          exact hBb j k F
  rw [ReciprocityTheory.AnForm.M.maMeasure_eq_sum A Φ hne, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  simp only [hν]
  calc ∑ j, ReciprocityTheory.AnForm.M.chartMeasure A hne.some Φ j s
      ≤ ∑ j, ∑ k, c j * B j k * ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) :=
        Finset.sum_le_sum fun j _ => hμ j
    _ ≤ ∑ j, ∑ k, c j * B j k * ∑ k', ∫⁻ z in P.chartMid k', F ((P.chart k').symm z) := by
        gcongr with j _ k _
        exact Finset.single_le_sum (f := fun k' => ∫⁻ z in P.chartMid k', F ((P.chart k').symm z))
          (fun _ _ => zero_le) (Finset.mem_univ k)
    _ = _ := by simp_rw [Finset.sum_mul]

end ChartMongeAmpereL1Measure

theorem ChartMongeAmpereL1Measure.proof : ChartMongeAmpereL1Measure.Statement := by
  intro X _ _ _ _ _ D A P om hom _hpos g t₀ ht₀ hg
  set μ := maMeasure A (fun _ : Fin D => om) with hμ
  obtain ⟨C, hC, hle⟩ :=
    ChartMongeAmpereL1Measure.maMeasure_le_smul_sum A P (fun _ => om) (fun _ => hom)
  set ν := ∑ k, (volume.restrict (P.chartMid k)).map (P.chart k).symm with hν
  have hMm : ∀ k, MeasurableSet (P.chartMid k) := fun k =>
    ((P.chart k).isOpen_inter_preimage_symm (P.isOpen_mid k)).measurableSet
  have hsy : ∀ k, AEMeasurable (P.chart k).symm (volume.restrict (P.chartMid k)) := fun k =>
    ((P.chart k).continuousOn_symm.mono inter_subset_left).aemeasurable (hMm k)
  have hnn : ∀ t, 0 ≤ ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)| := fun t =>
    Finset.sum_nonneg fun k _ => integral_nonneg fun y => abs_nonneg _
  have key : ∀ t, 0 < t → t < t₀ → Integrable (g t) μ ∧
      ∫ x, |g t x| ∂μ ≤ C.toReal * ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)| := by
    intro t ht ht'
    have hI : ∀ k, IntegrableOn (fun y => g t ((P.chart k).symm y)) (P.chartMid k) :=
      fun k => (hg k).1 t ht ht'
    have hmk : ∀ k, AEStronglyMeasurable (g t)
        ((volume.restrict (P.chartMid k)).map (P.chart k).symm) := fun k =>
      ChartMongeAmpereL1Measure.aestronglyMeasurable_map_symm (P.chart k) (hMm k) inter_subset_left
        (hI k).aestronglyMeasurable
    have hmν : AEStronglyMeasurable (g t) ν := by
      rw [hν, ← Measure.sum_fintype]
      exact aestronglyMeasurable_sum_measure_iff.2 hmk
    have hmμ : AEStronglyMeasurable (g t) μ := (hmν.smul_measure C).mono_measure hle
    have hlin : ∫⁻ x, ‖g t x‖ₑ ∂μ ≤
        C * ∑ k, ENNReal.ofReal (∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) := by
      calc ∫⁻ x, ‖g t x‖ₑ ∂μ ≤ ∫⁻ x, ‖g t x‖ₑ ∂(C • ν) := lintegral_mono' hle le_rfl
        _ = C * ∑ k, ∫⁻ x, ‖g t x‖ₑ ∂((volume.restrict (P.chartMid k)).map (P.chart k).symm) := by
          rw [lintegral_smul_measure, hν, lintegral_finsetSum_measure, smul_eq_mul]
        _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [lintegral_map' (hmk k).enorm (hsy k), ← ofReal_integral_norm_eq_lintegral_enorm (hI k)]
          simp only [Real.norm_eq_abs]
    have hfin : C * ∑ k, ENNReal.ofReal (∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) =
        ENNReal.ofReal (C.toReal * ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC,
        ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg fun y => abs_nonneg _]
    rw [hfin] at hlin
    have hInt : Integrable (g t) μ := ⟨hmμ, lt_of_le_of_lt hlin ENNReal.ofReal_lt_top⟩
    refine ⟨hInt, ?_⟩
    have h1 : ENNReal.ofReal (∫ x, |g t x| ∂μ) = ∫⁻ x, ‖g t x‖ₑ ∂μ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hInt]
      simp only [Real.norm_eq_abs]
    rw [← h1] at hlin
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (hnn t))).1 hlin
  refine ⟨fun t ht ht' => (key t ht ht').1, ?_⟩
  have hlim : Tendsto (fun t => C.toReal * ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)|)
      (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_finsetSum Finset.univ fun k _ => (hg k).2).const_mul C.toReal
    simpa using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 t₀ := Ioo_mem_nhdsGT ht₀
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun t => integral_nonneg fun x => abs_nonneg _
  · exact hev.mono fun t ht => (key t ht.1 ht.2).2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

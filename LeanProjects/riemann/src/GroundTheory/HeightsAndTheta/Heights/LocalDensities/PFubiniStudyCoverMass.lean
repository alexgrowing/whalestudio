import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsFSDensity
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsChartPartition
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsCoverInt
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

abbrev coverFSPot (e : ℕ) (z : Fin e → ℂ) : ℝ := (1 / 2) * Real.log (1 + ∑ i, ‖z i‖ ^ 2)

theorem coverFSPot_contDiff (e : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (coverFSPot e) := by
  unfold coverFSPot
  refine contDiff_const.mul (ContDiff.log (contDiff_const.add
    (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))) fun z => ?_)
  positivity

theorem coverFS_local {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)} {d : ℕ}
    (hH : FubiniStudyCoverMass.Hyp A P q M₀ Δ d) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x)
    (hm : (A.chart j).symm y ∈ M₀) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) y ∧ ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G y ∧
      P.φ x ∘ (A.chart j).symm =ᶠ[𝓝 y]
        fun y' => (coverFSPot e ∘ (q ∘ (A.chart j).symm)) y' + (G y').re := by
  obtain ⟨-, hM, -, -, hq, -, -, -, -, hloc⟩ := hH
  refine ⟨analyticAt_pi_iff.2 fun i => hq i j y ⟨hy, hm⟩, ?_⟩
  obtain ⟨W, hWo, hyW, G, hG, heq⟩ := hloc x _ ⟨hx, hm⟩
  refine ⟨G ∘ (A.chart j).symm, hG j y ⟨hy, hyW⟩, ?_⟩
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U x ∩ M₀)) :=
    (A.chart j).isOpen_inter_preimage_symm ((hWo.inter (P.isOpen_U x)).inter hM)
  filter_upwards [hO.mem_nhds ⟨hy, ⟨hyW, hx⟩, hm⟩] with y' hy'
  exact heq _ hy'.2

theorem coverFS_contDiffAt {e : ℕ} {τ : (Fin e → ℂ) → (Fin e → ℂ)} {y : Fin e → ℂ}
    (hτ : AnalyticAt ℂ τ y) : ContDiffAt ℝ 2 (coverFSPot e ∘ τ) y :=
  (coverFSPot_contDiff e).contDiffAt.comp y hτ.restrictScalars.contDiffAt

theorem fubiniStudyCover_levi_nonneg (hFS : FubiniStudyChartDensity.Statement) {e : ℕ} {X : Type}
    [TopologicalSpace X] {A : FinHolAtlas e X} {P : LocPot X} {q : X → Fin e → ℂ} {M₀ : Set X}
    {Δ : Set (Fin e → ℂ)} {d : ℕ} (hH : FubiniStudyCoverMass.Hyp A P q M₀ Δ d) (x : X)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hx : (A.chart j).symm y ∈ P.U x) (hm : (A.chart j).symm y ∈ M₀) (w : Fin e → ℂ) :
    0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w := by
  obtain ⟨hτ, G, hG, hev⟩ := coverFS_local hH x j hy hx hm
  have hg : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hG.restrictScalars.contDiffAt
  have hsum : (fun y' => (coverFSPot e ∘ (q ∘ (A.chart j).symm)) y' + (G y').re) =
      fun y' => (coverFSPot e ∘ (q ∘ (A.chart j).symm)) y' + 1 * (G y').re := by
    funext y'; rw [one_mul]
  rw [levi_congr hev, hsum, levi_add_smul 1 (coverFS_contDiffAt hτ) hg, levi_re_analytic hG,
    mul_zero, add_zero, levi_comp w hτ (coverFSPot_contDiff e).contDiffAt]
  exact (hFS e _ _).1

theorem coverFS_locDens (hFS : FubiniStudyChartDensity.Statement) {e : ℕ} {X : Type}
    [TopologicalSpace X] {A : FinHolAtlas e X} {P : LocPot X} {q : X → Fin e → ℂ} {M₀ : Set X}
    {Δ : Set (Fin e → ℂ)} {d : ℕ} (hH : FubiniStudyCoverMass.Hyp A P q M₀ Δ d) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hm : (A.chart j).symm y ∈ M₀) :
    locDens A (fun _ => P) j y =
      (e.factorial : ℝ) / (Real.pi ^ e * (1 + ∑ i, ‖q ((A.chart j).symm y) i‖ ^ 2) ^ (e + 1)) *
        ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  obtain ⟨hτ, G, hG, hev⟩ := coverFS_local hH ((A.chart j).symm y) j hy (P.mem_U _) hm
  have h1 : locDens A (fun _ => P) j y =
      maDens (fun _ => P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y := rfl
  have h2 : maDens (fun _ => P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y =
      maDens (fun _ => coverFSPot e ∘ (q ∘ (A.chart j).symm)) y := by
    rw [maDens_congr_eventuallyEq (fun _ => hev)]
    exact maDens_congr_hessC _ _ y fun _ =>
      ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ G y (coverFS_contDiffAt hτ) hG
  have h3 := ReciprocityTheory.AnForm.A.maDens_comp (fun _ => coverFSPot e) (q ∘ (A.chart j).symm) y hτ
    fun _ => (coverFSPot_contDiff e).contDiffAt
  rw [h1, h2, h3, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq]
  congr 1
  exact (hFS e _ 0).2

theorem FubiniStudyCoverMass.proof (hFS : FubiniStudyChartDensity.Statement)
    (hPart : ChartPartitionExists.Statement) (hCov : CoverChartLIntegral.Statement) :
    FubiniStudyCoverMass.Statement := by
  intro e X _ _ _ _ A P q M₀ Δ d hH
  have hH' := hH
  obtain ⟨hP, hM, hAn, hInt, hq, hΔc, hΔ0, hcov, hdeg, -⟩ := hH'
  refine ⟨?_, ?_⟩
  ·
    intro x j y hy w
    by_contra hneg
    have hneg' := not_le.1 hneg
    have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
      (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
    have hc : ContinuousAt (fun y' => levi (P.φ x ∘ (A.chart j).symm) y' w) y := by
      have h := (continuousOn_levi hU (potSmoothOn A P hP x j)).continuousAt
        ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hy (Set.mem_univ w)))
      have hpair : ContinuousAt (fun y' : Fin e → ℂ => (y', w)) y :=
        continuousAt_id.prodMk continuousAt_const
      exact ContinuousAt.comp (f := fun y' : Fin e → ℂ => (y', w)) h hpair
    have hev : ∀ᶠ y' in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) y' w < 0 ∧
        y' ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
      (hc.eventually (gt_mem_nhds hneg')).and (hU.mem_nhds hy)
    have hfr : ∃ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ M₀ := by
      intro hno
      obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 (hno.and ((A.chart j).open_target.mem_nhds hy.1))
      have himg : IsOpen ((A.chart j).symm '' N) :=
        (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2
      have hsub : (A.chart j).symm '' N ⊆ interior M₀ᶜ :=
        interior_maximal (by rintro _ ⟨z, hz, rfl⟩; exact (hNsub hz).1) himg
      rw [hInt] at hsub
      exact hsub ⟨y, hyN, rfl⟩
    obtain ⟨y', hm, hlt, hyU⟩ := (hfr.and_eventually hev).exists
    exact absurd (fubiniStudyCover_levi_nonneg hFS hH x j hyU.1 hyU.2 hm w) (not_le.2 hlt)
  ·
    have hχ : Nonempty (ChartPartition A) := hPart A
    set χ := hχ.some with hχdef
    have hmass : maMeasure A (fun _ => P) Set.univ = ∑ j, ∫⁻ y in (A.chart j).target,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y) * locDens A (fun _ => P) j y) := by
      rw [maMeasure, dif_pos hχ, Measure.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Measure.map_apply_of_aemeasurable ?_ MeasurableSet.univ, Set.preimage_univ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact ((A.chart j).continuousOn_symm.aemeasurable
        (A.chart j).open_target.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)
    have hpiece : ∀ j, ∫⁻ y in (A.chart j).target,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y) * locDens A (fun _ => P) j y) =
        ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀,
          ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
            ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
              (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) *
            (fun z => ENNReal.ofReal (CP.fsVolumeDensity (N := e) 0 z)) (q ((A.chart j).symm y)) := by
      intro j
      have hae : ((A.chart j).target : Set (Fin e → ℂ)) =ᵐ[volume]
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀ : Set (Fin e → ℂ)) := by
        refine ae_eq_set.2 ⟨measure_mono_null ?_ (analyticNull A M₀ᶜ hAn hInt j), ?_⟩
        · rintro y ⟨hy, hyV⟩
          exact ⟨(A.chart j).symm y, ⟨fun hm => hyV ⟨hy, hm⟩, (A.chart j).map_target hy⟩,
            (A.chart j).right_inv hy⟩
        · rw [Set.sdiff_eq_empty.2 Set.inter_subset_left, measure_empty]
      rw [setLIntegral_congr hae]
      refine setLIntegral_congr_fun ((A.chart j).isOpen_inter_preimage_symm hM).measurableSet
        fun y hy => ?_
      rw [coverFS_locDens hFS hH j hy.1 hy.2]
      beta_reduce
      rw [CP.fsVolumeDensity_eq,
        ENNReal.ofReal_mul (χ.nonneg j _), ENNReal.ofReal_mul (by positivity)]
      simp only [normSqSum]
      ring
    have hmeas : Measurable fun z => ENNReal.ofReal (CP.fsVolumeDensity (N := e) 0 z) :=
      (CP.measurable_fsVolumeDensity 0).ennreal_ofReal
    rw [hmass, Finset.sum_congr rfl fun j _ => hpiece j,
      hCov A χ q M₀ Δ d ⟨hM, hq, hΔc, hcov, hdeg⟩ _ hmeas,
      setLIntegral_congr (ae_eq_univ.2 (by rwa [compl_compl])), Measure.restrict_univ,
      CP.lintegral_fsVolumeDensity, mul_one]

end

end GroundTheory.Heights₂.Heights.FourB

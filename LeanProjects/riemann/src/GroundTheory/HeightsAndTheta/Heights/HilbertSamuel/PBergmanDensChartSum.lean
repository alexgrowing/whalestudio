import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensChartSum
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
open scoped ENNReal ContDiff ComplexConjugate Matrix

noncomputable section

namespace BergmanDensChartSum

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem weight_contDiffOn {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ ∞ (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  (W.smooth j j).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

theorem trans_source_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).source =
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]

theorem trans_target_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).target =
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source := by
  rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target]

theorem trans_analytic (j k : Fin A.n) :
    AnalyticOnNhd ℂ ((A.chart j).symm.trans (A.chart k))
      ((A.chart j).symm.trans (A.chart k)).source := by
  rw [trans_source_eq, OpenPartialHomeomorph.coe_trans]
  exact A.holo j k

theorem hessC_weight_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    hessC (W.φ j ∘ (A.chart j).symm) y =
      (jacC ((A.chart j).symm.trans (A.chart k)) y)ᵀ *
        hessC (W.φ k ∘ (A.chart k).symm) (((A.chart j).symm.trans (A.chart k)) y) *
        (jacC ((A.chart j).symm.trans (A.chart k)) y).map (starRingEnd ℂ) := by
  set T := (A.chart j).symm.trans (A.chart k) with hT
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
    rwa [← trans_source_eq]
  have hyS : (A.chart j).symm y ∈ (A.chart j).source ∩ (A.chart k).source :=
    ⟨(A.chart j).map_target hy'.1, hy'.2⟩
  have hTan : AnalyticAt ℂ T y := trans_analytic j k y hy
  have hTy : T y ∈ (A.chart k).target := T.map_source hy |> fun h => by
    rw [trans_target_eq] at h; exact h.1
  have hψ : ContDiffAt ℝ 2 (W.φ k ∘ (A.chart k).symm) (T y) :=
    ((weight_contDiffOn W k).contDiffAt ((A.chart k).open_target.mem_nhds hTy)).of_le
      (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)
  have hTc : ContDiffAt ℝ 2 T y := (hTan.contDiffAt (n := 2)).restrict_scalars ℝ
  have hφ : ContDiffAt ℝ 2 ((W.φ k ∘ (A.chart k).symm) ∘ T) y := hψ.comp y hTc
  set g : (Fin D → ℂ) → ℂ := fun w => L.g j k ((A.chart j).symm w) ^ 2 with hg
  have hgan : AnalyticAt ℂ g y := (L.holo j k j y ⟨hy'.1, hyS⟩).pow 2
  have hg0 : g y ≠ 0 := pow_ne_zero 2 (L.ne_zero j k _ hyS)
  have hev : (W.φ j ∘ (A.chart j).symm) =ᶠ[𝓝 y]
      fun w => ((W.φ k ∘ (A.chart k).symm) ∘ T) w + Real.log ‖g w‖ := by
    filter_upwards [T.open_source.mem_nhds hy] with w hw
    rw [trans_source_eq] at hw
    have hwS : (A.chart j).symm w ∈ (A.chart j).source ∩ (A.chart k).source :=
      ⟨(A.chart j).map_target hw.1, hw.2⟩
    simp only [Function.comp_apply, hT, OpenPartialHomeomorph.coe_trans, hg, norm_pow,
      (A.chart k).left_inv hw.2]
    exact W.compat j k _ hwS
  rw [hessCGerm _ _ y hev, hessC_add_log_norm _ g y hφ hgan hg0, hessC_comp _ _ y hTan hψ]

theorem chernTopDens_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    chernTopDens W j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      chernTopDens W k (((A.chart j).symm.trans (A.chart k)) y) := by
  unfold chernTopDens
  rw [hessC_weight_trans W j k hy]
  set J := jacC ((A.chart j).symm.trans (A.chart k)) y
  set H := hessC (W.φ k ∘ (A.chart k).symm) (((A.chart j).symm.trans (A.chart k)) y)
  set c : ℂ := ((1 / Real.pi : ℝ) : ℂ)
  have h1 : c • (Jᵀ * H * J.map (starRingEnd ℂ)) = Jᵀ * (c • H) * J.map (starRingEnd ℂ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have h2 : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h2,
    show J.det * (c • H).det * starRingEnd ℂ J.det = ((Complex.normSq J.det : ℝ) : ℂ) * (c • H).det by
      rw [← Complex.mul_conj]; ring,
    Complex.re_ofReal_mul]
  ring

variable [MeasurableSpace X] [BorelSpace X]

theorem lintegral_dens_trans (dV : SmoothVolume A) (j k : Fin A.n)
    (f : (Fin D → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source, f y * ENNReal.ofReal (dV.dens j y) =
      ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source,
        ENNReal.ofReal (Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det) *
          (f y * ENNReal.ofReal (dV.dens k (((A.chart j).symm.trans (A.chart k)) y))) := by
  classical
  set T := (A.chart j).symm.trans (A.chart k) with hT
  set S := (A.chart j).source ∩ (A.chart k).source with hS
  have hSo : IsOpen S := (A.chart j).open_source.inter (A.chart k).open_source
  have hSm : MeasurableSet S := hSo.measurableSet
  set p : X → Fin D → ℂ := S.piecewise (A.chart j) (fun _ => 0) with hp
  have hpm : Measurable p :=
    ContinuousOn.measurable_piecewise ((A.chart j).continuousOn.mono inter_subset_left)
      continuousOn_const hSm
  set g : X → ℝ≥0∞ := S.indicator (fun x => f (p x)) with hg
  have hgm : Measurable g := (hf.comp hpm).indicator hSm
  have hsame : ∀ i, (A.chart i).source ∩ S = S → ∫⁻ x in (A.chart i).source, g x ∂dV.μ =
      ∫⁻ x in S, f (p x) ∂dV.μ := by
    intro i hi
    rw [hg, lintegral_indicator hSm, Measure.restrict_restrict hSm, inter_comm, hi]
  have hL := dV.chart_lintegral j g hgm
  have hR := dV.chart_lintegral k g hgm
  rw [hsame j (inter_eq_right.2 inter_subset_left)] at hL
  rw [hsame k (inter_eq_right.2 inter_subset_right)] at hR
  have hTsrc := trans_source_eq (A := A) j k
  have hTtgt := trans_target_eq (A := A) j k
  have hLe : ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) =
      ∫⁻ y in T.source, f y * ENNReal.ofReal (dV.dens j y) := by
    have hsub : T.source ⊆ (A.chart j).target := hTsrc ▸ inter_subset_left
    conv_rhs => rw [← inter_eq_left.2 hsub, ← Measure.restrict_restrict T.open_source.measurableSet,
      ← lintegral_indicator T.open_source.measurableSet]
    refine setLIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    have hyj : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
    by_cases hk : (A.chart j).symm y ∈ (A.chart k).source
    · have hyT : y ∈ T.source := by rw [hTsrc]; exact ⟨hy, hk⟩
      simp [hg, hp, Set.indicator_of_mem hyT, Set.indicator_of_mem (show (A.chart j).symm y ∈ S
        from ⟨hyj, hk⟩), Set.piecewise_eq_of_mem _ _ _ (show (A.chart j).symm y ∈ S from ⟨hyj, hk⟩),
        (A.chart j).right_inv hy]
    · have hyT : y ∉ T.source := by rw [hTsrc]; exact fun h => hk h.2
      simp [hg, Set.indicator_of_notMem hyT, Set.indicator_of_notMem
        (show (A.chart j).symm y ∉ S from fun h => hk h.2)]
  have hRe : ∫⁻ z in (A.chart k).target, g ((A.chart k).symm z) * ENNReal.ofReal (dV.dens k z) =
      ∫⁻ z in T.target, f (T.symm z) * ENNReal.ofReal (dV.dens k z) := by
    have hsub : T.target ⊆ (A.chart k).target := hTtgt ▸ inter_subset_left
    conv_rhs => rw [← inter_eq_left.2 hsub, ← Measure.restrict_restrict T.open_target.measurableSet,
      ← lintegral_indicator T.open_target.measurableSet]
    refine setLIntegral_congr_fun (A.chart k).open_target.measurableSet fun z hz => ?_
    have hzk : (A.chart k).symm z ∈ (A.chart k).source := (A.chart k).map_target hz
    by_cases hj : (A.chart k).symm z ∈ (A.chart j).source
    · have hzT : z ∈ T.target := by rw [hTtgt]; exact ⟨hz, hj⟩
      rw [Set.indicator_of_mem hzT]
      simp [hg, hp, hT, Set.indicator_of_mem (show (A.chart k).symm z ∈ S
        from ⟨hj, hzk⟩), Set.piecewise_eq_of_mem _ _ _ (show (A.chart k).symm z ∈ S from ⟨hj, hzk⟩),
        OpenPartialHomeomorph.coe_trans_symm]
    · have hzT : z ∉ T.target := by rw [hTtgt]; exact fun h => hj h.2
      simp [hg, Set.indicator_of_notMem hzT, Set.indicator_of_notMem
        (show (A.chart k).symm z ∉ S from fun h => hj h.1)]
  rw [← hLe, ← hL, hR, hRe, ← T.image_source_eq_target,
    lintegral_image_eq_lintegral_normSq_det_mul T T.source T.open_source (trans_analytic j k)
      T.injOn]
  refine setLIntegral_congr_fun T.open_source.measurableSet fun y hy => ?_
  simp only [T.left_inv hy]

omit [MeasurableSpace X] [BorelSpace X] in

theorem jacC_trans_continuousOn (j k : Fin A.n) :
    ContinuousOn (jacC ((A.chart j).symm.trans (A.chart k)))
      ((A.chart j).symm.trans (A.chart k)).source := by
  have h := (trans_analytic (A := A) j k).fderiv.continuousOn
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  exact (continuous_apply a).comp_continuousOn
    ((ContinuousLinearMap.apply ℂ _ (Pi.single b 1)).continuous.comp_continuousOn h)

theorem dens_trans (dV : SmoothVolume A) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    dV.dens j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      dV.dens k (((A.chart j).symm.trans (A.chart k)) y) := by
  set T := (A.chart j).symm.trans (A.chart k) with hT
  have hU := T.open_source
  have hsub : T.source ⊆ (A.chart j).target := trans_source_eq (A := A) j k ▸ inter_subset_left
  have hc1 : ContinuousOn (dV.dens j) T.source := (dV.smooth j).continuousOn.mono hsub
  have hc2 : ContinuousOn (fun y => Complex.normSq (jacC T y).det * dV.dens k (T y)) T.source := by
    refine ContinuousOn.mul ?_ ?_
    · exact Complex.continuous_normSq.comp_continuousOn
        ((continuous_id.matrix_det).comp_continuousOn (jacC_trans_continuousOn j k))
    · refine (dV.smooth k).continuousOn.comp T.continuousOn fun z hz => ?_
      have := T.map_source hz
      rw [trans_target_eq] at this
      exact this.1
  have hae : (fun y => ENNReal.ofReal (dV.dens j y)) =ᵐ[volume.restrict T.source]
      fun y => ENNReal.ofReal (Complex.normSq (jacC T y).det * dV.dens k (T y)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀
      (ENNReal.measurable_ofReal.comp_aemeasurable (hc1.aemeasurable hU.measurableSet))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hc2.aemeasurable hU.measurableSet))
      fun s hs _ => ?_
    rw [← lintegral_indicator hs, ← lintegral_indicator hs]
    have h := lintegral_dens_trans dV j k (s.indicator 1) (measurable_one.indicator hs)
    have e1 : (fun z => s.indicator (fun y => ENNReal.ofReal (dV.dens j y)) z) =
        fun z => s.indicator 1 z * ENNReal.ofReal (dV.dens j z) := by
      funext z; by_cases hz : z ∈ s <;> simp [hz]
    have e2 : (fun z => s.indicator
        (fun y => ENNReal.ofReal (Complex.normSq (jacC T y).det * dV.dens k (T y))) z) =
        fun z => ENNReal.ofReal (Complex.normSq (jacC T z).det) *
          (s.indicator 1 z * ENNReal.ofReal (dV.dens k (T z))) := by
      funext z
      by_cases hz : z ∈ s <;> simp [hz, ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
    rw [e1, e2]
    exact h
  have hcont1 : ContinuousOn (fun y => ENNReal.ofReal (dV.dens j y)) T.source :=
    ENNReal.continuous_ofReal.comp_continuousOn hc1
  have hcont2 : ContinuousOn
      (fun y => ENNReal.ofReal (Complex.normSq (jacC T y).det * dV.dens k (T y))) T.source :=
    ENNReal.continuous_ofReal.comp_continuousOn hc2
  have heq := Measure.eqOn_open_of_ae_eq hae hU hcont1 hcont2 hy
  have hp1 : 0 ≤ dV.dens j y := (dV.pos j y (hsub hy)).le
  have hp2 : 0 ≤ Complex.normSq (jacC T y).det * dV.dens k (T y) := by
    have := T.map_source hy
    rw [trans_target_eq] at this
    exact mul_nonneg (Complex.normSq_nonneg _) (dV.pos k _ this.1).le
  exact (ENNReal.ofReal_eq_ofReal_iff hp1 hp2).1 heq

variable {L : HolLineBundle A}

def densIn (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) (x : X) : ℝ :=
  chernTopDens W j (A.chart j x) / ((D.factorial : ℝ) * dV.dens j (A.chart j x))

theorem densIn_eq (W : Weight L) (dV : SmoothVolume A) (j k : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source ∩ (A.chart k).source) :
    densIn W dV j x = densIn W dV k x := by
  have hy : A.chart j x ∈ ((A.chart j).symm.trans (A.chart k)).source := by
    rw [trans_source_eq]
    exact ⟨(A.chart j).map_source hx.1,
      Set.mem_preimage.2 (by rw [(A.chart j).left_inv hx.1]; exact hx.2)⟩
  have hT : ((A.chart j).symm.trans (A.chart k)) (A.chart j x) = A.chart k x := by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, (A.chart j).left_inv hx.1]
  have hc := chernTopDens_trans W j k hy
  have hd := dens_trans dV j k hy
  rw [hT] at hc hd
  set n := Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) (A.chart j x)).det
  have hpos : 0 < dV.dens j (A.chart j x) := dV.pos j _ ((A.chart j).map_source hx.1)
  have hn : n ≠ 0 := by
    intro h0; rw [hd, h0, zero_mul] at hpos; exact lt_irrefl 0 hpos
  unfold densIn
  rw [hc, hd, show (D.factorial : ℝ) * (n * dV.dens k (A.chart k x)) =
    n * ((D.factorial : ℝ) * dV.dens k (A.chart k x)) by ring, mul_div_mul_left _ _ hn]

omit [BorelSpace X] in

theorem densIn_continuousAt (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source) : ContinuousAt (densIn W dV j) x := by
  have hy : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hnhds : (A.chart j).target ∈ 𝓝 (A.chart j x) := (A.chart j).open_target.mem_nhds hy
  have hH : ContinuousAt (hessC (W.φ j ∘ (A.chart j).symm)) (A.chart j x) :=
    (hessC_continuousOn _ _ (A.chart j).open_target
      ((weight_contDiffOn W j).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp |
        exact WithTop.coe_le_coe.2 le_top))).continuousAt hnhds
  have hdet : Continuous fun M : Matrix (Fin D) (Fin D) ℂ =>
      (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • M).det).re := by fun_prop
  have hC : ContinuousAt (chernTopDens W j) (A.chart j x) := hdet.continuousAt.comp hH
  have hdens : ContinuousAt (dV.dens j) (A.chart j x) :=
    (dV.smooth j).continuousOn.continuousAt hnhds
  have hc := (A.chart j).continuousAt hx
  refine (hC.comp hc).div (continuousAt_const.mul (hdens.comp hc)) ?_
  exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos D).ne') (dV.pos j _ hy).ne'

theorem bergmanDens_continuous (W : Weight L) (dV : SmoothVolume A) :
    Continuous (bergmanDens W dV) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hev : densIn W dV (chartIdx A x) =ᶠ[𝓝 x] bergmanDens W dV := by
    filter_upwards [(A.chart (chartIdx A x)).open_source.mem_nhds hx] with x' hx'
    exact densIn_eq W dV _ _ ⟨hx', Classical.choose_spec (A.cover x')⟩
  exact (densIn_continuousAt W dV _ hx).congr hev

omit [MeasurableSpace X] [BorelSpace X] in

theorem continuous_of_smooth {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨j, hj⟩ := A.cover p
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p) := by
    refine (hf j).continuousOn.continuousAt ?_
    simp only [Set.preimage_univ, Set.inter_univ]
    exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
  refine (h1.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with q hq
  simp [(A.chart j).left_inv hq]

theorem restrict_source_eq (dV : SmoothVolume A) (j : Fin A.n) :
    dV.μ.restrict (A.chart j).source =
      ((volume.restrict (A.chart j).target).withDensity
        fun y => ENNReal.ofReal (dV.dens j y)).map (A.chart j).symm := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hsymm' : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (dV.dens j y)) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hd : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y))
      (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((dV.smooth j).continuousOn.aemeasurable hT)
  ext s hs
  have hi : Measurable (s.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hs
  have hi' : AEMeasurable (fun y => s.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y))
      (volume.restrict (A.chart j).target) :=
    hi.comp_aemeasurable hsymm
  calc dV.μ.restrict (A.chart j).source s
      = ∫⁻ x in (A.chart j).source, s.indicator (1 : X → ℝ≥0∞) x ∂dV.μ :=
        (lintegral_indicator_one hs).symm
    _ = ∫⁻ y in (A.chart j).target, s.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
          ENNReal.ofReal (dV.dens j y) := dV.chart_lintegral j _ hi
    _ = ∫⁻ y, s.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) ∂((volume.restrict
          (A.chart j).target).withDensity fun y => ENNReal.ofReal (dV.dens j y)) := by
        rw [lintegral_withDensity_eq_lintegral_mul₀ hd hi']
        refine lintegral_congr fun y => ?_
        simp only [Pi.mul_apply]
        ring
    _ = ∫⁻ x, s.indicator (1 : X → ℝ≥0∞) x ∂(((volume.restrict (A.chart j).target).withDensity
          fun y => ENNReal.ofReal (dV.dens j y)).map (A.chart j).symm) :=
        (lintegral_map' hi.aemeasurable hsymm').symm
    _ = _ := lintegral_indicator_one hs

theorem bergmanDens_symm (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart j).target) :
    bergmanDens W dV ((A.chart j).symm y) =
      chernTopDens W j y / ((D.factorial : ℝ) * dV.dens j y) := by
  have hx : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
  show densIn W dV (chartIdx A ((A.chart j).symm y)) ((A.chart j).symm y) = _
  have h : densIn W dV (chartIdx A ((A.chart j).symm y)) ((A.chart j).symm y) =
      densIn W dV j ((A.chart j).symm y) :=
    densIn_eq W dV _ j ⟨Classical.choose_spec (A.cover _), hx⟩
  rw [h, densIn, (A.chart j).right_inv hy]

theorem integral_chart_term (W : Weight L) (dV : SmoothVolume A) (P : ChartPartition A)
    (g : X → ℝ) (hg : Continuous g) (j : Fin A.n) :
    ∫ x, P.χ j x * g x * bergmanDens W dV x ∂dV.μ =
      (∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
        chernTopDens W j y) / (D.factorial : ℝ) := by
  have hFc : Continuous fun x => P.χ j x * g x * bergmanDens W dV x :=
    ((continuous_of_smooth (P.smooth j)).mul hg).mul (bergmanDens_continuous W dV)
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hsymm' : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (dV.dens j y)) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hd : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y))
      (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((dV.smooth j).continuousOn.aemeasurable hT)
  have hzero : ∀ x ∉ (A.chart j).source, P.χ j x * g x * bergmanDens W dV x = 0 := by
    intro x hx
    have h0 : P.χ j x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (P.tsupport_subset j h)
    simp [h0]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, restrict_source_eq dV j,
    integral_map hsymm' hFc.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hd (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_div]
  refine setIntegral_congr_fun hT fun y hy => ?_
  have hpos := dV.pos j y hy
  have hfac : (D.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos D).ne'
  simp only [bergmanDens_symm W dV j hy, smul_eq_mul, ENNReal.toReal_ofReal hpos.le]
  field_simp
  try ring

end BergmanDensChartSum

theorem BergmanDensChartSum.proof : BergmanDensChartSum.Statement := by
  intro D X _ _ _ _ _ A L W dV P g hg
  have := dV.isProb
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin A.n)),
      Integrable (fun x => P.χ j x * g x * bergmanDens W dV x) dV.μ :=
    fun j _ => (((BergmanDensChartSum.continuous_of_smooth (P.smooth j)).mul hg).mul
      (BergmanDensChartSum.bergmanDens_continuous W dV)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : (fun x => g x * bergmanDens W dV x) =
      fun x => ∑ j, P.χ j x * g x * bergmanDens W dV x := by
    funext x
    rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one x, one_mul]
  rw [hsum, integral_finsetSum _ hint, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => BergmanDensChartSum.integral_chart_term W dV P g hg j

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

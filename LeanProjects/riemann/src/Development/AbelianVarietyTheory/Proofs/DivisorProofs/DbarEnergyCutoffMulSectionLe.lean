import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.CutEnergy

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem wdb_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) : ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K := by
  set e := A.chart (C.idx a)
  have hg : ContDiffOn ℝ ∞ (fun w => ((χ (e.symm w) : ℝ) : ℂ)) e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ (C.idx a))
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
    hg.fderiv_of_isOpen e.open_target (by simp)
  have hc : ContinuousOn (fun v => ∑ j, ‖wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ)) v‖ ^ 2)
      e.target := by
    refine continuousOn_finset_sum _ fun j _ => ?_
    have : ContDiffOn ℝ ∞ (wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
      ((hd.clm_apply contDiffOn_const).add
        (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2
    exact (this.continuousOn.norm).pow 2
  obtain ⟨K, hK⟩ := (isCompact_closedBall (C.c a) (C.r a)).exists_bound_of_continuousOn
    (hc.mono (C.sub a))
  refine ⟨max K 0, le_max_right _ _, fun v hv => ?_⟩
  have := hK v hv
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _))

theorem pt_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K)
    (la : La) (W Z : Set Y) (h : ι → Y → ℂ) (hW : IsOpen W) (hsupp : tsupport χ ⊆ W)
    (hsec : A.IsSecOn (A.kap + la) W h)
    (hZ : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) (v : V n) (hv : v ∈ ball (C.c a) (C.r a)) :
    ENNReal.ofReal ((∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) (C.idx a) ∘
        (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal K * ((Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y))
          ((A.chart (C.idx a)).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
  set i := C.idx a
  set e := A.chart i
  set y := e.symm v
  set g : V n → ℂ := fun w => ((χ (e.symm w) : ℝ) : ℂ)
  have hvt : v ∈ e.target := C.sub a (ball_subset_closedBall hv)
  have hys : y ∈ e.source := e.map_target hvt
  have hgs : ContDiffOn ℝ ∞ g e.target := Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ i)
  have hgd : DifferentiableAt ℝ g v :=
    (hgs.differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hvt)

  have hzero : y ∉ Z ∩ W → ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = 0 := by
    intro hy j
    by_cases hyW : y ∈ W
    · have hyZ : y ∉ Z := fun hz => hy ⟨hz, hyW⟩
      have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hyW⟩
      have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
        (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
      have hg0 : wdb n j g v = 0 := by
        have hev : g =ᶠ[𝓝 v] fun _ => ((χ y : ℝ) : ℂ) := by
          have := (e.continuousAt_symm hvt).eventually (hZ y hyZ)
          filter_upwards [this] with w hw
          simp only [g]; rw [hw]
        rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
        exact wdb_of_differentiableAt (differentiableAt_const _)
      have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
        rfl
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH, hg0]
      ring
    · have hyt : y ∉ tsupport χ := fun ht => hyW (hsupp ht)
      have h0 := (notMem_tsupport_iff_eventuallyEq.mp hyt)
      have hev : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        have := (e.continuousAt_symm hvt).eventually h0
        filter_upwards [this] with w hw
        simp only [Function.comp_apply, Pi.zero_apply] at hw ⊢
        rw [hw]; simp
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
      exact wdb_of_differentiableAt (differentiableAt_const _)
  by_cases hy : y ∈ Z ∩ W
  · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
    have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hy.2⟩
    have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
      (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
    have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
      rfl
    have hw : ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = wdb n j g v * h i y := by
      intro j
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH]
      simp [y]
    have hsum : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) =
        ‖h i y‖ ^ 2 * ∑ j, ‖wdb n j g v‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw j, norm_mul, mul_pow]; ring
    have hnsq := api_nsq_eq A hsec hys hy.2
    rw [A.ph_add _ _ i y hys] at hnsq
    have hexp : Real.exp (-A.ph la i y) =
        Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul (by unfold WeightedAtlas.nsq; positivity),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsum, ← hnsq, hexp]
    have hS := hK v (ball_subset_closedBall hv)
    have h1 : 0 ≤ ‖h i y‖ ^ 2 * (Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
        Real.exp (A.ph A.kap i y)) := by positivity
    calc ‖h i y‖ ^ 2 * (∑ j, ‖wdb n j g v‖ ^ 2) *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))
        = (∑ j, ‖wdb n j g v‖ ^ 2) * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) := by ring
      _ ≤ K * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_right hS h1
      _ = K * (‖h i y‖ ^ 2 * Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
          Real.exp (A.ph A.kap i y)) := by ring
  · have : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hzero hy j]; simp
    rw [this, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

end

end GlobalTheory.CutEnergy

namespace GlobalTheory.CutEnergy

theorem dbarEnergy_cutoff_mul_section_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A C χ hχ
  choose K hK0 hK using fun a => wdb_bound A C χ hχ a
  refine ⟨∑ a, K a, Finset.sum_nonneg fun a _ => hK0 a, ?_⟩
  intro la W Z h hW hsupp hsec hZm hZ
  set G : Y → ℝ≥0∞ := (Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) with hGdef
  have hGm : Measurable G := by
    classical
    have h1 : Measurable (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) := by
      rw [← Set.piecewise_eq_indicator]
      exact ContinuousOn.measurable_piecewise
        (ENNReal.continuous_ofReal.comp_continuousOn (api_nsq_contOn A hW hsec))
        continuousOn_const hW.measurableSet
    have : G = Z.indicator (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) :=
      (Set.indicator_indicator _ _ _).symm
    rw [this]; exact h1.indicator hZm
  have hint : ∫⁻ y, G y ∂A.mu = ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu :=
    lintegral_indicator (hZm.inter hW.measurableSet) _
  rw [← hint, ENNReal.ofReal_sum_of_nonneg (fun a _ => hK0 a), Finset.sum_mul]
  unfold n1
  refine Finset.sum_le_sum fun a _ => ?_
  calc _ ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (K a) *
          (G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
        setLIntegral_mono' measurableSet_ball fun v hv =>
          pt_bound A C χ hχ a (K a) (hK0 a) (hK a) la W Z h hW hsupp hsec hZ v hv
    _ = ENNReal.ofReal (K a) * ∫⁻ v in ball (C.c a) (C.r a), G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
          gcongr
          exact A.aap_lintegral_chart_le _ G hGm _ (ball_subset_closedBall.trans (C.sub a))

end GlobalTheory.CutEnergy

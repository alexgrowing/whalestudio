import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNullB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y Set
open scoped ENNReal ContDiff

noncomputable section

section L2ExtNz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {Λ : La} {τ : ι → Y → ℂ}

theorem nz_coeff_ne_iff (hτ : A.IsSec Λ τ) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    τ i y ≠ 0 ↔ y ∈ nz A τ := by
  show τ i y ≠ 0 ↔ τ (A.pick y) y ≠ 0
  rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
  have hg := A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy
  constructor
  · intro h; exact mul_ne_zero hg h
  · intro h h0; exact h (by rw [h0, mul_zero])

theorem nz_isOpen_of_isSec (hτ : A.IsSec Λ τ) : IsOpen (nz A τ) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  have hc : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    simpa using fn_contOn_sec A hτ (A.pick y)
  refine ⟨(A.chart (A.pick y)).source ∩ τ (A.pick y) ⁻¹' {0}ᶜ, ?_,
    hc.isOpen_inter_preimage (A.chart _).open_source isOpen_compl_singleton, ⟨A.mem_pick y, hy⟩⟩
  rintro x ⟨hxs, hx⟩
  exact (nz_coeff_ne_iff A hτ hxs).1 hx

theorem nz_coeff_diff (hτ : A.IsSec Λ τ) (i : ι) :
    DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
  simpa using hτ.1 i

theorem nz_coeff_ne_iff' (hτ : A.IsSec Λ τ) {i : ι} {v : V n} (hv : v ∈ (A.chart i).target) :
    (τ i ∘ (A.chart i).symm) v ≠ 0 ↔ (A.chart i).symm v ∈ nz A τ :=
  nz_coeff_ne_iff A hτ ((A.chart i).map_target hv)

theorem nz_loc (hτ : A.IsSec Λ τ) {la : La} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la (nz A τ) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤)
    (i : ι) {v : V n} (hv : v ∈ (A.chart i).target) :
    ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∫⁻ u in Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) < ⊤ := by
  have hMo : IsOpen (nz A τ) := nz_isOpen_of_isSec A hτ
  obtain ⟨U, hU, hfin⟩ := hloc ((A.chart i).symm v)
  obtain ⟨U', hU'U, hU'o, hyU'⟩ := mem_nhds_iff.1 hU
  have hTo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U') :=
    (A.chart i).isOpen_inter_preimage_symm hU'o
  obtain ⟨r0, hr0, hB0⟩ := Metric.isOpen_iff.1 hTo v ⟨hv, hyU'⟩
  have hK : Metric.closedBall v (r0 / 2) ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U' :=
    (Metric.closedBall_subset_ball (by linarith)).trans hB0
  have hqc : ContinuousOn (fun u => Real.exp (A.ph la i ((A.chart i).symm u) -
      A.ph A.kap i ((A.chart i).symm u))) (Metric.closedBall v (r0 / 2)) :=
    (Real.continuous_exp.comp_continuousOn
      ((A.smooth_ph la i).continuousOn.sub (A.smooth_ph A.kap i).continuousOn)).mono
      (hK.trans inter_subset_left)
  obtain ⟨C, hC⟩ := (isCompact_closedBall v (r0 / 2)).exists_bound_of_continuousOn hqc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC v (Metric.mem_closedBall_self (by linarith)))
  have hBt : Metric.ball v (r0 / 2) ⊆ (A.chart i).target :=
    (Metric.ball_subset_closedBall.trans hK).trans inter_subset_left
  refine ⟨r0 / 2, by linarith, hBt, ?_⟩
  have hSm : MeasurableSet ((A.chart i).source ∩ nz A τ ∩ U') :=
    (((A.chart i).open_source.inter hMo).inter hU'o).measurableSet
  have hgc : ContinuousOn (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)))
      ((A.chart i).source ∩ nz A τ ∩ U') :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (((fn_contOn_sec A hFs i).mono inter_subset_left).norm.pow 2 |>.mul
        (Real.continuous_exp.comp_continuousOn
          ((fn_contOn_ph A la i).mono (inter_subset_left.trans inter_subset_left)).neg))
  have hmg : Measurable (((A.chart i).source ∩ nz A τ ∩ U').indicator
      (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)))) := by
    classical
    rw [← Set.piecewise_eq_indicator]
    exact hgc.measurable_piecewise continuousOn_const hSm
  have hmeas : MeasurableSet (Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0}) := by
    have : IsOpen (Metric.ball v (r0 / 2) ∩ (τ i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
      ((nz_coeff_diff A hτ i).continuousOn.mono hBt).isOpen_inter_preimage Metric.isOpen_ball
        isOpen_compl_singleton
    exact this.measurableSet
  calc ∫⁻ u in Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2)
      ≤ ∫⁻ u in Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal C * (fnRho A i u * ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) ((A.chart i).symm u)) := by
        refine setLIntegral_mono' hmeas fun u hu => ?_
        have hut : u ∈ (A.chart i).target := hBt hu.1
        have hsu : (A.chart i).symm u ∈ (A.chart i).source := (A.chart i).map_target hut
        have hM : (A.chart i).symm u ∈ nz A τ := (nz_coeff_ne_iff' A hτ hut).1 hu.2
        have hU' : (A.chart i).symm u ∈ U' := (hK (Metric.ball_subset_closedBall hu.1)).2
        have hmem : (A.chart i).symm u ∈ (A.chart i).source ∩ nz A τ ∩ U' := ⟨⟨hsu, hM⟩, hU'⟩
        rw [Set.indicator_of_mem (s := (A.chart i).source ∩ nz A τ ∩ U') hmem]
        unfold fnRho
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hC0]
        apply ENNReal.ofReal_le_ofReal
        have hq := hC u (Metric.ball_subset_closedBall hu.1)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hq
        have e0 : Real.exp (A.ph la i ((A.chart i).symm u) - A.ph A.kap i ((A.chart i).symm u)) *
            Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
            Real.exp (-A.ph la i ((A.chart i).symm u)) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; simp
        calc ‖F i ((A.chart i).symm u)‖ ^ 2
            = Real.exp (A.ph la i ((A.chart i).symm u) - A.ph A.kap i ((A.chart i).symm u)) *
              (Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
                (‖F i ((A.chart i).symm u)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm u)))) := by
              linear_combination (-‖F i ((A.chart i).symm u)‖ ^ 2) * e0
          _ ≤ _ := mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ ∫⁻ u in (A.chart i).target,
        ENNReal.ofReal C * (fnRho A i u * ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) ((A.chart i).symm u)) :=
        lintegral_mono_set (sdiff_subset.trans hBt)
    _ = ENNReal.ofReal C * ∫⁻ x in (A.chart i).source, ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) x ∂A.mu := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, fn_lint A i hmg]
    _ ≤ ENNReal.ofReal C * ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc _ ≤ ∫⁻ x, ((A.chart i).source ∩ nz A τ ∩ U').indicator
              (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) x ∂A.mu :=
              setLIntegral_le_lintegral _ _
          _ = ∫⁻ x in (A.chart i).source ∩ nz A τ ∩ U',
              ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)) ∂A.mu := lintegral_indicator hSm _
          _ = ∫⁻ x in (A.chart i).source ∩ nz A τ ∩ U',
              ENNReal.ofReal (A.nsq la F x) ∂A.mu :=
              setLIntegral_congr_fun hSm fun x hx => by rw [fn_nsq_eq A hFs hx.1.1 hx.1.2]
          _ ≤ _ := lintegral_mono_set fun x (hx : x ∈ (A.chart i).source ∩ nz A τ ∩ U') =>
              (⟨hU'U hx.2, hx.1.2⟩ : x ∈ U ∩ nz A τ)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem nz_sub_closure (hτ : A.IsSec Λ τ) (hdense : Dense (nz A τ)) (i : ι) {O : Set (V n)}
    (hO : IsOpen O) (hOt : O ⊆ (A.chart i).target) :
    O ⊆ closure (O ∩ {u | (τ i ∘ (A.chart i).symm) u ≠ 0}) := by
  intro p hp
  rw [_root_.mem_closure_iff]
  intro o ho hpo
  have hWo : IsOpen ((A.chart i).source ∩ A.chart i ⁻¹' (o ∩ O)) :=
    (A.chart i).continuousOn.isOpen_inter_preimage (A.chart i).open_source (ho.inter hO)
  have hpt := hOt hp
  have hmem : (A.chart i).symm p ∈ (A.chart i).source ∩ A.chart i ⁻¹' (o ∩ O) := by
    refine ⟨(A.chart i).map_target hpt, ?_⟩
    show A.chart i ((A.chart i).symm p) ∈ o ∩ O
    rw [(A.chart i).right_inv hpt]; exact ⟨hpo, hp⟩
  obtain ⟨x, hxW, hxM⟩ := hdense.inter_open_nonempty _ hWo ⟨_, hmem⟩
  refine ⟨A.chart i x, hxW.2.1, hxW.2.2, ?_⟩
  show (τ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0
  rw [nz_coeff_ne_iff' A hτ ((A.chart i).map_source hxW.1), (A.chart i).left_inv hxW.1]
  exact hxM

theorem l2_extension_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ la : La) (τ F : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.IsSecOn la (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq la F y) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec la G ∧ ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y := by
  intro n Y _ _ _ _ _ ι La _ A Λ la τ F hτ hdense hFs hfin
  have hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤ :=
    fun y => ⟨univ, univ_mem, by simpa using hfin⟩
  have hex : ∀ i, ∀ v ∈ (A.chart i).target, ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∃ U : V n → ℂ, DifferentiableOn ℂ U (Metric.ball v r) ∧
        EqOn U (F i ∘ (A.chart i).symm)
          (Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) := by
    intro i v hv
    obtain ⟨r, hr, hBt, hfin'⟩ := nz_loc A hτ hFs hloc i hv
    have hu : DifferentiableOn ℂ (F i ∘ (A.chart i).symm)
        (Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) :=
      (hFs.1 i).mono fun u (hu : u ∈ Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) =>
        ⟨hBt hu.1, (nz_coeff_ne_iff' A hτ (hBt hu.1)).1 hu.2⟩
    obtain ⟨U, hU, hUeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n v r (τ i ∘ (A.chart i).symm)
      (F i ∘ (A.chart i).symm) ((nz_coeff_diff A hτ i).mono hBt) hu hfin'
    exact ⟨r, hr, hBt, U, hU, hUeq⟩
  choose! R hR hRt U hU hUeq using hex
  have hagree : ∀ i, ∀ v ∈ (A.chart i).target,
      EqOn (fun u => U i u u) (U i v) (Metric.ball v (R i v)) := by
    intro i v hv u hu
    have hut := hRt i v hv hu
    have hO : IsOpen (Metric.ball v (R i v) ∩ Metric.ball u (R i u)) :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    have hOt : Metric.ball v (R i v) ∩ Metric.ball u (R i u) ⊆ (A.chart i).target :=
      inter_subset_left.trans (hRt i v hv)
    have key := Set.EqOn.of_subset_closure
      (s := (Metric.ball v (R i v) ∩ Metric.ball u (R i u)) ∩
        {x | (τ i ∘ (A.chart i).symm) x ≠ 0})
      (f := U i v) (g := U i u) ?_ ((hU i v hv).continuousOn.mono inter_subset_left)
      ((hU i u hut).continuousOn.mono inter_subset_right) inter_subset_left
      (nz_sub_closure A hτ hdense i hO hOt)
    · exact (key ⟨hu, Metric.mem_ball_self (hR i u hut)⟩).symm
    · intro x hx
      rw [hUeq i v hv ⟨hx.1.1, hx.2⟩, hUeq i u hut ⟨hx.1.2, hx.2⟩]
  have hGcd : ∀ i, DifferentiableOn ℂ (fun u => U i u u) (A.chart i).target := by
    intro i v hv
    have hev : (fun u => U i u u) =ᶠ[𝓝 v] U i v :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds v (hR i v hv)) (hagree i v hv)
    exact (((hU i v hv).differentiableAt (Metric.ball_mem_nhds v (hR i v hv))).congr_of_eventuallyEq
      hev).differentiableWithinAt
  have hGcF : ∀ i, ∀ v ∈ (A.chart i).target, (A.chart i).symm v ∈ nz A τ →
      U i v v = F i ((A.chart i).symm v) := by
    intro i v hv hM
    exact hUeq i v hv ⟨Metric.mem_ball_self (hR i v hv), (nz_coeff_ne_iff' A hτ hv).2 hM⟩
  have hGF : ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source →
      U i (A.chart i y) (A.chart i y) = F i y := by
    intro i y hyM hys
    rw [hGcF i _ ((A.chart i).map_source hys) (by rw [(A.chart i).left_inv hys]; exact hyM),
      (A.chart i).left_inv hys]
  refine ⟨fun i y => U i (A.chart i y) (A.chart i y), ⟨fun i => ?_, ?_⟩, hGF⟩
  · refine ((hGcd i).mono inter_subset_left).congr fun u hu => ?_
    simp [(A.chart i).right_inv hu.1]
  · intro i j y _ hyi hyj
    have hcont : ∀ k, ContinuousOn (fun y => U k (A.chart k y) (A.chart k y)) (A.chart k).source :=
      fun k => (hGcd k).continuousOn.comp (A.chart k).continuousOn
        fun x hx => (A.chart k).map_source hx
    have hgc : ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
      refine ((A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono inter_subset_left)
        fun x hx => ?_).congr fun x hx => ?_
      · show A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source
        refine ⟨(A.chart i).map_source hx.1, ?_⟩
        show (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
        rw [(A.chart i).left_inv hx.1]; exact hx.2
      · simp [(A.chart i).left_inv hx.1]
    have hO : IsOpen ((A.chart i).source ∩ (A.chart j).source) :=
      (A.chart i).open_source.inter (A.chart j).open_source
    refine Set.EqOn.of_subset_closure
      (s := ((A.chart i).source ∩ (A.chart j).source) ∩ nz A τ)
      (f := fun y => U i (A.chart i y) (A.chart i y))
      (g := fun y => A.g la i j y * U j (A.chart j y) (A.chart j y)) ?_
      ((hcont i).mono inter_subset_left) (hgc.mul ((hcont j).mono inter_subset_right))
      inter_subset_left (hdense.open_subset_closure_inter hO) ⟨hyi, hyj⟩
    intro x hx
    simp only
    rw [hGF i x hx.2 hx.1.1, hGF j x hx.2 hx.1.2]
    exact hFs.2 i j x hx.2 hx.1.1 hx.1.2

end L2ExtNz

end

end GlobalTheory.OTY

import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem nsq_eq_chart (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold nsq
  set j := A.pick y
  have hj : y ∈ (A.chart j).source := A.mem_pick y
  have h1 : s i y = A.g la i j y * s j y := hs.2 i j y trivial hy hj
  have h2 : A.ph la j y = A.ph la i y - Real.log (‖A.g la i j y‖ ^ 2) := A.ph_trans la i j y hy hj
  have hg : 0 < ‖A.g la i j y‖ ^ 2 := by
    have := A.g_ne la i j y hy hj
    positivity
  rw [h1, h2, norm_mul, mul_pow, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring

theorem continuousOn_sec (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    (i : ι) : ContinuousOn (s i) (A.chart i).source := by
  have h1 : ContinuousOn (s i ∘ (A.chart i).symm) (A.chart i).target := by
    have := (hs.1 i).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousOn ((s i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]

theorem continuousOn_ph (A : WeightedAtlas n Y ι La) (la : La) (i : ι) :
    ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 : ContinuousOn (A.ph la i ∘ (A.chart i).symm) (A.chart i).target :=
    (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]

theorem continuous_nsq (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s) :
    Continuous (A.nsq la s) := by
  rw [continuous_iff_continuousAt]
  intro y
  set i := A.pick y
  have hU : (A.chart i).source ∈ 𝓝 y := (A.chart i).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun x => ‖s i x‖ ^ 2 * Real.exp (-A.ph la i x)) (A.chart i).source :=
    ((A.continuousOn_sec hs i).norm.pow 2).mul ((A.continuousOn_ph la i).neg.rexp)
  refine (hc.continuousAt hU).congr ?_
  filter_upwards [hU] with x hx
  exact (A.nsq_eq_chart hs hx).symm

theorem continuous_sqn (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    (hw : ∀ k, A.IsSec la (w k)) : Continuous (A.sqn la w) := by
  unfold sqn
  exact continuous_finsetSum _ (fun k _ => A.continuous_nsq (hw k))

theorem nsq_nonneg (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (y : Y) :
    0 ≤ A.nsq la s y := by
  unfold nsq; positivity

theorem sqn_nonneg (A : WeightedAtlas n Y ι La) (la : La) {N : ℕ} (w : Fin N → ι → Y → ℂ) (y : Y) :
    0 ≤ A.sqn la w y := by
  unfold sqn; exact Finset.sum_nonneg (fun k _ => A.nsq_nonneg la (w k) y)

theorem isSec_sum (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    {h : κ → ι → Y → ℂ} (hh : ∀ q ∈ F, A.IsSec la (h q)) :
    A.IsSec la (fun i y => ∑ q ∈ F, h q i y) := by
  refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
  · have : (fun y => ∑ q ∈ F, h q i y) ∘ (A.chart i).symm =
        fun v => ∑ q ∈ F, (h q i ∘ (A.chart i).symm) v := by
      funext v; simp
    rw [this]
    exact DifferentiableOn.fun_sum (fun q hq => (hh q hq).1 i)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q hq => (hh q hq).2 i j y hy hi hj)

theorem nsq_sum_le (A : WeightedAtlas n Y ι La) (la : La) {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (y : Y) :
    A.nsq la (fun i y => ∑ q ∈ F, h q i y) y ≤ (F.card : ℝ) * ∑ q ∈ F, A.nsq la (h q) y := by
  unfold nsq
  have h1 : ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 ≤ (F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
  have he : 0 ≤ Real.exp (-A.ph la (A.pick y) y) := (Real.exp_pos _).le
  calc ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y) y)
      ≤ ((F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2) * Real.exp (-A.ph la (A.pick y) y) :=
        mul_le_mul_of_nonneg_right h1 he
    _ = _ := by rw [mul_assoc, Finset.sum_mul]

theorem mu_singleton (A : WeightedAtlas n Y ι La) (hn : 1 ≤ n) (P : Y) : A.mu {P} = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [A.mu_chart (A.pick P) {P} (measurableSet_singleton P)
    (Set.singleton_subset_iff.2 (A.mem_pick P)), Set.image_singleton]
  exact setLIntegral_measure_zero _ _ (measure_singleton _)

theorem lintegral_chart_le (A : WeightedAtlas n Y ι La) (i : ι) (y0 : Y) {W : Set (V n)}
    (hW : IsOpen W) (hWt : W ⊆ (A.chart i).target) (c : ℝ≥0∞)
    (hc : ∀ v ∈ W, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) ≤ c)
    (ψ : V n → ℝ≥0∞) (hψ : Continuous ψ) :
    ∫⁻ x in (A.chart i).source ∩ A.chart i ⁻¹' W, ψ (A.chart i x) ∂A.mu ≤
      c * ∫⁻ v in W, ψ v := by
  classical
  set e := A.chart i
  set U := e.source ∩ e ⁻¹' W with hUdef
  have hUo : IsOpen U := e.isOpen_inter_preimage hW
  have hUm : MeasurableSet U := hUo.measurableSet
  set φ : V n → Y := W.piecewise e.symm (fun _ => y0) with hφdef
  have hφ : Measurable φ :=
    ContinuousOn.measurable_piecewise (e.continuousOn_symm.mono hWt) continuousOn_const
      hW.measurableSet
  have himg : ∀ B : Set Y, e '' (B ∩ U) = φ ⁻¹' B ∩ W := by
    intro B
    ext v
    constructor
    · rintro ⟨x, ⟨hxB, hxs, hxW⟩, rfl⟩
      refine ⟨?_, hxW⟩
      show φ (e x) ∈ B
      rw [show φ (e x) = e.symm (e x) from Set.piecewise_eq_of_mem _ _ _ hxW, e.left_inv hxs]
      exact hxB
    · rintro ⟨hvB, hvW⟩
      rw [Set.mem_preimage, show φ v = e.symm v from Set.piecewise_eq_of_mem _ _ _ hvW] at hvB
      have hvt := hWt hvW
      refine ⟨e.symm v, ⟨hvB, e.map_target hvt, ?_⟩, e.right_inv hvt⟩
      show e (e.symm v) ∈ W
      rwa [e.right_inv hvt]
  set ν : Measure (V n) := c • (volume.restrict W)
  have hle : A.mu.restrict U ≤ Measure.map φ ν := by
    rw [Measure.le_iff]
    intro B hB
    rw [Measure.restrict_apply hB, Measure.map_apply hφ hB,
      A.mu_chart i (B ∩ U) (hB.inter hUm) (Set.inter_subset_right.trans Set.inter_subset_left),
      himg B]
    have hm : MeasurableSet (φ ⁻¹' B ∩ W) := (hφ hB).inter hW.measurableSet
    calc ∫⁻ v in φ ⁻¹' B ∩ W, ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))
        ≤ ∫⁻ _ in φ ⁻¹' B ∩ W, c := setLIntegral_mono' hm (fun v hv => hc v hv.2)
      _ = ν (φ ⁻¹' B) := by
        rw [setLIntegral_const, Measure.smul_apply, Measure.restrict_apply (hφ hB), smul_eq_mul,
          mul_comm]
  set Φ : Y → ℝ≥0∞ := U.piecewise (fun x => ψ (e x)) (fun _ => 0) with hΦdef
  have hΦ : Measurable Φ :=
    ContinuousOn.measurable_piecewise (hψ.comp_continuousOn (e.continuousOn.mono
      Set.inter_subset_left)) continuousOn_const hUm
  calc ∫⁻ x in U, ψ (e x) ∂A.mu = ∫⁻ x in U, Φ x ∂A.mu :=
        setLIntegral_congr_fun hUm (fun x hx => by simp [Φ, Set.piecewise_eq_of_mem _ _ _ hx])
    _ ≤ ∫⁻ x, Φ x ∂(Measure.map φ ν) := lintegral_mono' hle le_rfl
    _ = ∫⁻ v, Φ (φ v) ∂ν := lintegral_map hΦ hφ
    _ = c * ∫⁻ v in W, Φ (φ v) := lintegral_smul_measure _ _
    _ = c * ∫⁻ v in W, ψ v := by
        congr 1
        refine setLIntegral_congr_fun hW.measurableSet (fun v hv => ?_)
        have hvt := hWt hv
        have hU : e.symm v ∈ U := ⟨e.map_target hvt, by
          show e (e.symm v) ∈ W
          rwa [e.right_inv hvt]⟩
        simp only [φ, Φ, Set.piecewise_eq_of_mem _ _ _ hv, Set.piecewise_eq_of_mem _ _ _ hU,
          e.right_inv hvt]

end WeightedAtlas

theorem lintegral_ball_rpow_lt_top {n : ℕ} (hMVI : MVIntStatement n) (hn : 1 ≤ n) (vP : V n)
    {r : ℝ} (hr : r ≤ 1) {a : ℝ} (ha : a < n) :
    ∫⁻ v in Metric.ball vP r, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) < ⊤ := by
  have h0 := (hMVI hn a).2 ha
  have h1 : ∫⁻ v in Metric.ball vP r, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) ≤
      ∫⁻ v in Metric.ball vP 1, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) :=
    lintegral_mono_set (Metric.ball_subset_ball hr)
  have h2 : ∫⁻ v in Metric.ball vP 1, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) =
      ∫⁻ y in Metric.ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * a) := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← lintegral_sub_right_eq_self ((Metric.ball (0 : V n) 1).indicator
        (fun y => ENNReal.ofReal ‖y‖ ^ (-2 * a))) vP]
    congr 1
    funext v
    by_cases hv : v ∈ Metric.ball vP 1
    · have hv' : v - vP ∈ Metric.ball (0 : V n) 1 := by
        rw [mem_ball_zero_iff]; rwa [Metric.mem_ball, dist_eq_norm] at hv
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv']
    · have hv' : v - vP ∉ Metric.ball (0 : V n) 1 := by
        rw [mem_ball_zero_iff]; rwa [Metric.mem_ball, dist_eq_norm] at hv
      rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv']
  exact lt_of_le_of_lt h1 (h2 ▸ h0)

end

end ReciprocityTheory.L2DbarEstimates.Y

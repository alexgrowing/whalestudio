import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxK

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem aap_continuous_nsq (la : La) (u : ι → Y → ℂ)
    (hcoc : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → u i y = A.g la i j y * u j y)
    (hc : ∀ i, ContinuousOn (u i ∘ (A.chart i).symm) (A.chart i).target) :
    Continuous (A.nsq la u) := by
  have hloc : ∀ i y, y ∈ (A.chart i).source →
      A.nsq la u y = ‖u i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    intro i y hy
    have hg := A.g_ne la (A.pick y) i y (A.mem_pick y) hy
    have ht := A.ph_trans la (A.pick y) i y (A.mem_pick y) hy
    have hg2 : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
    have hp : A.ph la (A.pick y) y = A.ph la i y + Real.log (‖A.g la (A.pick y) i y‖ ^ 2) := by
      linarith
    unfold nsq
    rw [hcoc (A.pick y) i y (A.mem_pick y) hy, hp, norm_mul, mul_pow, neg_add, Real.exp_add,
      Real.exp_neg (Real.log _), Real.exp_log hg2]
    field_simp
  rw [continuous_iff_continuousAt]
  intro y0
  have hy0 : y0 ∈ (A.chart (A.pick y0)).source := A.mem_pick y0
  have hs : (A.chart (A.pick y0)).source ∈ 𝓝 y0 := (A.chart (A.pick y0)).open_source.mem_nhds hy0
  have hu : ContinuousOn (u (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (hc (A.pick y0)).comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hph : ContinuousOn (A.ph la (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (A.smooth_ph la (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hf : ContinuousOn (fun y => ‖u (A.pick y0) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y0) y))
      (A.chart (A.pick y0)).source :=
    (hu.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  exact (hf.congr fun y hy => hloc (A.pick y0) y hy).continuousAt hs

theorem continuous_nsq_of_isSec {la : La} {u : ι → Y → ℂ} (hu : A.IsSec la u) :
    Continuous (A.nsq la u) := by
  exact A.aap_continuous_nsq la u (fun i j y hi hj => hu.2 i j y (Set.mem_univ y) hi hj)
    (fun i => (hu.1 i).continuousOn.mono fun v hv => ⟨hv, Set.mem_univ _⟩)

theorem continuous_sqn_of_isSec {N : ℕ} {la : La} {w : Fin N → ι → Y → ℂ} (hw : ∀ k, A.IsSec la (w k)) :
    Continuous (A.sqn la w) := by
  show Continuous fun y => ∑ k, A.nsq la (w k) y
  exact continuous_finset_sum _ fun k _ => A.continuous_nsq_of_isSec (hw k)

theorem int_h_le {Sf : Finset Y} (D : CutData A Sf) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) {ps1 : Y → ℝ}
    (hps1 : A.SmoothFn ps1) (η : ℝ) (hTS : ∀ P ∈ Sf, ∀ y ∈ D.T P, 0 < A.sqn L s y) (Ch : ℝ) :
    ∃ Hb : ℝ≥0∞, Hb < ⊤ ∧ ∀ δ : ℝ, 0 < δ →
      ∫⁻ y, (⋃ P ∈ Sf, D.T P).indicator (fun _ => ENNReal.ofReal Ch) y *
        ENNReal.ofReal (Real.exp (-A.psD L w s ps1 η δ y)) ∂A.mu ≤ Hb := by
  classical
  have hTeq : ∀ P, D.T P = (A.chart (A.pick P)).symm ''
      (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
    fun P => rfl
  have hS : ∀ P, IsCompact
      (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
    fun P => (isCompact_closedBall _ _).diff isOpen_ball
  have hStgt : ∀ P ∈ Sf, ∀ v ∈ closedBall (A.chart (A.pick P) P) (D.r2 P) \
      ball (A.chart (A.pick P) P) (D.r1 P), v ∈ (A.chart (A.pick P)).target :=
    fun P hP v hv => (D.8 P hP hv.1).1
  have hTc : ∀ P ∈ Sf, IsCompact (D.T P) := by
    intro P hP
    rw [hTeq P]
    exact (hS P).image_of_continuousOn
      ((A.chart (A.pick P)).continuousOn_symm.mono fun v hv => hStgt P hP v hv)
  have hμT : ∀ P ∈ Sf, A.mu (D.T P) < ⊤ := by
    intro P hP
    have hTs : D.T P ⊆ (A.chart (A.pick P)).source := by
      rw [hTeq P]
      rintro _ ⟨v, hv, rfl⟩
      exact (A.chart (A.pick P)).map_target (hStgt P hP v hv)
    rw [A.mu_chart (A.pick P) (D.T P) (hTc P hP).isClosed.measurableSet hTs]
    have himg : (A.chart (A.pick P)) '' D.T P =
        closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P) := by
      rw [hTeq P, Set.image_image]
      exact (Set.image_congr fun v hv => (A.chart (A.pick P)).right_inv (hStgt P hP v hv)).trans
        (Set.image_id' _)
    rw [himg]
    have hcont : ContinuousOn
        (fun v => Real.exp (A.ph A.kap (A.pick P) ((A.chart (A.pick P)).symm v)))
        (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
      Real.continuous_exp.comp_continuousOn
        ((A.smooth_ph A.kap (A.pick P)).continuousOn.mono fun v hv => hStgt P hP v hv)
    obtain ⟨C', hC'⟩ := (hS P).exists_bound_of_continuousOn hcont
    calc ∫⁻ v in closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick P) ((A.chart (A.pick P)).symm v)))
        ≤ ∫⁻ v in closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P),
          ENNReal.ofReal C' :=
          setLIntegral_mono' (hS P).isClosed.measurableSet fun v hv =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC' v hv))
      _ = ENNReal.ofReal C' * volume
          (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS P).measure_lt_top
  obtain ⟨K, hK⟩ : ∃ K, K = ⋃ P ∈ Sf, D.T P := ⟨_, rfl⟩
  rw [← hK]
  have hKc : IsCompact K := by
    rw [hK]
    exact Sf.isCompact_biUnion hTc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hμK : A.mu K < ⊤ := by
    rw [hK]
    exact (measure_biUnion_finset_le Sf _).trans_lt (ENNReal.sum_lt_top.mpr fun P hP => hμT P hP)
  have hsK : ∀ y ∈ K, 0 < A.sqn L s y := by
    intro y hy
    rw [hK, Set.mem_iUnion₂] at hy
    obtain ⟨P, hP, hyP⟩ := hy
    exact hTS P hP y hyP
  have hps1c : Continuous ps1 := by
    rw [continuous_iff_continuousAt]
    intro y0
    have hy0 := A.mem_pick y0
    have h1 := (hps1 (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    have h2 : ContinuousOn ps1 (A.chart (A.pick y0)).source :=
      h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
    exact h2.continuousAt ((A.chart (A.pick y0)).open_source.mem_nhds hy0)
  have hwc : Continuous (A.sqn L w) := A.continuous_sqn_of_isSec hD.sec_w
  have hsc : Continuous (A.sqn L s) := A.continuous_sqn_of_isSec hD.sec_s
  have hwpos : ∀ y, 0 < A.sqn L w y := by
    intro y
    obtain ⟨k, hk⟩ := hD.no_common_zero y
    have hle : A.nsq L (w k) y ≤ A.sqn L w y :=
      Finset.single_le_sum (f := fun k => A.nsq L (w k) y)
        (fun j _ => by simp only [nsq]; positivity) (Finset.mem_univ k)
    have hpos : 0 < A.nsq L (w k) y := by
      simp only [nsq]
      exact mul_pos (pow_pos (norm_pos_iff.mpr hk) 2) (Real.exp_pos _)
    linarith
  have hGc : ContinuousOn (fun y => Real.exp (-ps1 y - η * Real.log (A.sqn L w y) -
      (n : ℝ) * Real.log (A.sqn L s y))) K := by
    apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.sub
    · exact (hps1c.neg.sub (continuous_const.mul (hwc.log fun y => (hwpos y).ne'))).continuousOn
    · exact continuousOn_const.mul (hsc.continuousOn.log fun y hy => (hsK y hy).ne')
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hGc
  have hbound : ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → Real.exp (-A.psD L w s ps1 η δ y) ≤ C := by
    intro y hy δ hδ
    refine le_trans ?_ ((Real.le_norm_self _).trans (hC y hy))
    apply Real.exp_le_exp.mpr
    unfold psD
    have h1 : Real.log (A.sqn L s y) ≤ Real.log (A.sqn L s y + δ) :=
      Real.log_le_log (hsK y hy) (by linarith)
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine ⟨ENNReal.ofReal Ch * ENNReal.ofReal C * A.mu K,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hμK,
    fun δ hδ => ?_⟩
  calc ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal Ch) y *
        ENNReal.ofReal (Real.exp (-A.psD L w s ps1 η δ y)) ∂A.mu
      ≤ ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal Ch * ENNReal.ofReal C) y ∂A.mu := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ K
        · simp only [Set.indicator_of_mem hy]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hbound y hy δ hδ))
        · simp [hy]
    _ = ENNReal.ofReal Ch * ENNReal.ofReal C * A.mu K := lintegral_indicator_const hKm _

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y

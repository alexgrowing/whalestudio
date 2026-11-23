import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff

noncomputable section

variable {D : ℕ}

lemma measurable_indicator_usc {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) : Measurable (U.indicator φ) := by
  refine measurable_of_Iio fun a => ?_
  have hO : IsOpen {x | x ∈ U ∧ φ x < a} := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hx⟩
    have h1 := hφ x hxU _ hx
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h1
    filter_upwards [h1, hU.mem_nhds hxU] with y hy hyU using ⟨hyU, hy⟩
  have : U.indicator φ ⁻¹' Iio a = {x | x ∈ U ∧ φ x < a} ∪ (Uᶜ ∩ {_x | (0 : ℝ) < a}) := by
    ext x
    by_cases hx : x ∈ U <;> simp [hx, Set.indicator]
  rw [this]
  exact hO.measurableSet.union (hU.measurableSet.compl.inter (MeasurableSet.const _))

lemma smul_measurePreserving {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    MeasurePreserving (fun y : Fin D → ℂ => ζ • y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => ζ • y) := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  refine ⟨?_, (Homeomorph.smulOfNeZero ζ hζ0).measurableEmbedding⟩
  let c : Circle := ⟨ζ, by simp [Submonoid.unitSphere, hζ]⟩
  have h := volume_preserving_pi (ι := Fin D) (fun _ => (rotation c).measurePreserving)
  convert h using 1
  funext y i
  rw [Pi.smul_apply, smul_eq_mul, rotation_apply]

lemma circle_fubini {Φ : (Fin D → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦi : Integrable Φ)
    {k : (Fin D → ℂ) → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    {P : ℂ → (Fin D → ℂ) → (Fin D → ℂ)} (hP : Continuous (Function.uncurry P))
    (hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (P ζ) ∧ MeasurableEmbedding (P ζ)) :
    Integrable (fun y => k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1) ∧
    ∫ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1 =
      circleAverage (fun ζ => ∫ y, k y * Φ (P ζ y)) 0 1 := by
  obtain ⟨M, hM⟩ := hk.bounded_above_of_compact_support hkc
  set μθ : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμθ
  set f : ℝ → (Fin D → ℂ) → ℝ := fun θ y => k y * Φ (P (circleMap 0 1 θ) y) with hf
  have hcm : ∀ θ, ‖circleMap 0 1 θ‖ = 1 := fun θ => by simp
  have hfm : Measurable (Function.uncurry f) := by
    have h1 : Continuous fun q : ℝ × (Fin D → ℂ) => P (circleMap 0 1 q.1) q.2 :=
      hP.comp (((continuous_circleMap 0 1).comp continuous_fst).prodMk continuous_snd)
    exact (hk.measurable.comp measurable_snd).mul (hΦm.comp h1.measurable)
  have hsec : ∀ θ, Integrable (f θ) ∧ ∫ y, ‖f θ y‖ ≤ M * ∫ y, |Φ y| := by
    intro θ
    obtain ⟨he, hee⟩ := hPm _ (hcm θ)
    have hi : Integrable fun y => Φ (P (circleMap 0 1 θ) y) :=
      (he.integrable_comp_emb hee).2 hΦi
    have hint : Integrable (f θ) :=
      hi.bdd_mul hk.aestronglyMeasurable (Eventually.of_forall hM)
    refine ⟨hint, ?_⟩
    calc ∫ y, ‖f θ y‖ ≤ ∫ y, M * |Φ (P (circleMap 0 1 θ) y)| := by
          refine integral_mono hint.norm (hi.abs.const_mul M) fun y => ?_
          simp only [hf, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hM y) (abs_nonneg _)
      _ = M * ∫ y, |Φ y| := by
          rw [integral_const_mul, he.integral_comp hee (fun y => |Φ y|)]
  have hint : Integrable (Function.uncurry f) (μθ.prod volume) := by
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun θ => (hsec θ).1, ?_⟩
    refine Integrable.mono' (integrable_const (M * ∫ y, |Φ y|)) ?_
      (Eventually.of_forall fun θ => ?_)
    · exact hfm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hsec θ).2
  have hswap := integral_integral_swap hint
  have hpt : ∀ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1 =
      (2 * π)⁻¹ * ∫ θ, f θ y ∂μθ := by
    intro y
    rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le,
      mul_left_comm, ← integral_const_mul]
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]
    exact hint.integral_prod_right.const_mul _
  calc ∫ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1
      = ∫ y, (2 * π)⁻¹ * ∫ θ, f θ y ∂μθ := by simp_rw [hpt]
    _ = (2 * π)⁻¹ * ∫ θ, ∫ y, f θ y ∂volume ∂μθ := by rw [integral_const_mul, hswap]
    _ = circleAverage (fun ζ => ∫ y, k y * Φ (P ζ y)) 0 1 := by
        rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le]

section Moll

variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

lemma scaled_circle_inv {ε : ℝ} {c : ℂ} (hc : ‖c‖ = 1) (w : Fin D → ℂ) :
    ρ.scaled ε (c • w) = ρ.scaled ε w := by
  simp only [Mollifier.scaled]
  rw [smul_comm, ρ.circle_inv c _ hc]

lemma exists_thick (hU : IsOpen U) {ε : ℝ} (hε : 0 ≤ ε) {z : Fin D → ℂ} (hz : z ∈ shrink U ε) :
    ∃ δ > 0, closedBall z (ε + δ) ⊆ U := by
  obtain ⟨δ, hδ, h⟩ := (isCompact_closedBall z ε).exists_cthickening_subset_open hU hz
  rw [cthickening_closedBall hδ.le hε] at h
  exact ⟨δ, hδ, by rw [add_comm]; exact h⟩

lemma isOpen_shrink (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) : IsOpen (shrink U ε) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨δ, hδ, h⟩ := exists_thick hU hε.le hz
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  exact (closedBall_subset_closedBall' (by linarith)).trans h

lemma phiC (hU : IsOpen U) (hφ : IsPsh U φ) {C : Set (Fin D → ℂ)} (hC : IsCompact C)
    (hCU : C ⊆ U) : Measurable (C.indicator φ) ∧ Integrable (C.indicator φ) := by
  have e : C.indicator φ = C.indicator (U.indicator φ) := by
    ext x
    by_cases hx : x ∈ C
    · simp [hx, hCU hx]
    · simp [hx]
  refine ⟨e ▸ (measurable_indicator_usc hU hφ.1).indicator hC.isClosed.measurableSet, ?_⟩
  exact (integrable_indicator_iff hC.isClosed.measurableSet).2
    ((isPsh_locallyIntegrable_thm D U φ hU hφ).integrableOn_compact_subset hCU hC)

lemma molli_eq_C {ε : ℝ} (hε : 0 < ε) {C : Set (Fin D → ℂ)} {z : Fin D → ℂ}
    (hz : closedBall z ε ⊆ C) :
    molli ρ ε φ z = ∫ y, ρ.scaled ε y * C.indicator φ (z - y) := by
  rw [molli_congr ρ hε (U := C) hz (fun x hx => (indicator_of_mem hx φ).symm)]
  rfl

lemma integrable_kC {ε : ℝ} (hε : 0 < ε) {Φ : (Fin D → ℂ) → ℝ} (hΦ : Integrable Φ)
    (z : Fin D → ℂ) : Integrable fun y => ρ.scaled ε y * Φ (z - y) := by
  obtain ⟨M, hM⟩ := (scaled_contDiff ρ ε).continuous.bounded_above_of_compact_support
    (scaled_hasCompactSupport ρ hε)
  exact (hΦ.comp_sub_left z).bdd_mul (scaled_contDiff ρ ε).continuous.aestronglyMeasurable
    (Eventually.of_forall hM)

lemma mem_ball_sub {ε : ℝ} (hε : 0 < ε) {y : Fin D → ℂ} (hy : ρ.scaled ε y ≠ 0)
    (z : Fin D → ℂ) : z - y ∈ closedBall z ε := by
  rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
  exact (norm_lt_of_scaled_ne_zero ρ hε hy).le

lemma le_molli (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink U ε) : φ z ≤ molli ρ ε φ z := by
  set C := closedBall z ε with hCdef
  obtain ⟨hm, hi⟩ := phiC hU hφ (isCompact_closedBall z ε) hz
  have hP : Continuous (Function.uncurry fun (ζ : ℂ) (y : Fin D → ℂ) => z - ζ • y) :=
    continuous_const.sub (continuous_fst.smul continuous_snd)
  have hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (fun y : Fin D → ℂ => z - ζ • y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => z - ζ • y) := by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := smul_measurePreserving (D := D) hζ
    exact ⟨(Measure.measurePreserving_sub_left volume z).comp h1,
      (Homeomorph.subLeft z).measurableEmbedding.comp h2⟩
  obtain ⟨hFint, hF⟩ := circle_fubini hm hi (scaled_contDiff ρ ε).continuous
    (scaled_hasCompactSupport ρ hε) hP hPm
  have hrot : ∀ ζ ∈ sphere (0 : ℂ) |1|,
      (∫ y, ρ.scaled ε y * C.indicator φ (z - ζ • y)) = molli ρ ε φ z := by
    intro ζ hζ
    have hζ' : ‖ζ‖ = 1 := by simpa using hζ
    obtain ⟨h1, h2⟩ := smul_measurePreserving (D := D) hζ'
    have := h1.integral_comp h2 (fun u => ρ.scaled ε u * C.indicator φ (z - u))
    rw [molli_eq_C ρ hε (subset_refl _), ← this]
    congr 1
    funext y
    rw [scaled_circle_inv ρ hζ']
  rw [circleAverage_congr_sphere hrot, circleAverage_const] at hF
  rw [← hF]
  calc φ z = ∫ y, ρ.scaled ε y * φ z := by
        rw [integral_mul_const, integral_scaled ρ hε, one_mul]
    _ ≤ _ := by
      refine integral_mono ((integrable_scaled ρ hε).mul_const _) hFint fun y => ?_
      by_cases hy : ρ.scaled ε y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
      have hyε := (norm_lt_of_scaled_ne_zero ρ hε hy).le
      have hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • (-y) ∈ C := by
        intro ζ hζ
        rw [hCdef, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_neg]
        nlinarith [norm_nonneg ζ, norm_nonneg y]
      obtain ⟨-, hmean⟩ := hφ.2 z (-y) (fun ζ hζ => hz (hdisc ζ hζ))
      refine hmean.trans (le_of_eq (circleAverage_congr_sphere fun ζ hζ => ?_))
      have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
      have h := hdisc ζ hζ'
      rw [smul_neg, ← sub_eq_add_neg] at h ⊢
      rw [indicator_of_mem h]

lemma molli_le_polyMax (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) : molli ρ ε φ z ≤ polyMax φ z ε := by
  obtain ⟨-, hi⟩ := phiC hU hφ (isCompact_closedBall z ε) hz
  rw [molli_eq_C ρ hε (subset_refl _)]
  calc _ ≤ ∫ y, ρ.scaled ε y * polyMax φ z ε := by
        refine integral_mono (integrable_kC ρ hε hi z) ((integrable_scaled ρ hε).mul_const _)
          fun y => ?_
        by_cases hy : ρ.scaled ε y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
        have hmem := mem_ball_sub ρ hε hy z
        rw [indicator_of_mem hmem]
        exact (hφ.1.mono hz).bddAbove_of_isCompact (isCompact_closedBall z ε) |>.elim
          fun _ _ => le_csSup ((hφ.1.mono hz).bddAbove_of_isCompact (isCompact_closedBall z ε))
            (mem_image_of_mem φ hmem)
    _ = polyMax φ z ε := by rw [integral_mul_const, integral_scaled ρ hε, one_mul]

lemma molli_contDiffAt (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) : ContDiffAt ℝ ∞ (molli ρ ε φ) z := by
  obtain ⟨δ, hδ, hδU⟩ := exists_thick hU hε.le hz
  obtain ⟨-, hi⟩ := phiC hU hφ (isCompact_closedBall z (ε + δ)) hδU
  have hg := (scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [molli_eq_C ρ hε (C := closedBall z (ε + δ)) (closedBall_subset_closedBall' (by linarith)),
    convolution_def]
  rfl

lemma molli_submean (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z w : Fin D → ℂ} (hd : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ shrink U ε) :
    molli ρ ε φ z ≤ circleAverage (fun ζ : ℂ => molli ρ ε φ (z + ζ • w)) 0 1 := by
  set C : Set (Fin D → ℂ) :=
    (fun q : ℂ × (Fin D → ℂ) => z + q.1 • w + q.2) '' (closedBall 0 1 ×ˢ closedBall 0 ε) with hCdef
  have hC : IsCompact C :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hball : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → closedBall (z + ζ • w) ε ⊆ C := by
    intro ζ hζ x hx
    refine ⟨(ζ, x - (z + ζ • w)), ⟨by simpa using hζ, ?_⟩, by simp⟩
    rw [mem_closedBall, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact hx
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨ζ, v⟩, ⟨hζ, hv⟩, rfl⟩
    refine hd ζ (by simpa using hζ) ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    simpa using hv
  obtain ⟨hm, hi⟩ := phiC hU hφ hC hCU
  have hP : Continuous (Function.uncurry fun (ζ : ℂ) (y : Fin D → ℂ) => z + ζ • w - y) :=
    (continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd
  have hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (fun y : Fin D → ℂ => z + ζ • w - y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => z + ζ • w - y) := fun ζ _ =>
    ⟨Measure.measurePreserving_sub_left volume _, (Homeomorph.subLeft _).measurableEmbedding⟩
  obtain ⟨hFint, hF⟩ := circle_fubini hm hi (scaled_contDiff ρ ε).continuous
    (scaled_hasCompactSupport ρ hε) hP hPm
  have hcirc : ∀ ζ ∈ sphere (0 : ℂ) |1|,
      (∫ y, ρ.scaled ε y * C.indicator φ (z + ζ • w - y)) = molli ρ ε φ (z + ζ • w) := by
    intro ζ hζ
    have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
    rw [molli_eq_C ρ hε (hball ζ hζ')]
  rw [circleAverage_congr_sphere hcirc] at hF
  have h0 : closedBall z ε ⊆ C := by simpa using hball 0 (by simp)
  rw [← hF, molli_eq_C ρ hε h0]
  refine integral_mono (integrable_kC ρ hε hi z) hFint fun y => ?_
  by_cases hy : ρ.scaled ε y = 0
  · simp [hy]
  refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
  have hyε := (norm_lt_of_scaled_ne_zero ρ hε hy).le
  have hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z - y + ζ • w ∈ C := by
    intro ζ hζ
    refine hball ζ hζ ?_
    rw [mem_closedBall, dist_eq_norm, show z - y + ζ • w - (z + ζ • w) = -y by abel, norm_neg]
    exact hyε
  obtain ⟨-, hmean⟩ := hφ.2 (z - y) w (fun ζ hζ => hCU (hin ζ hζ))
  have h00 : z - y ∈ C := by simpa using hin 0 (by simp)
  rw [indicator_of_mem h00]
  refine hmean.trans (le_of_eq (circleAverage_congr_sphere fun ζ hζ => ?_))
  have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
  show φ (z - y + ζ • w) = C.indicator φ (z + ζ • w - y)
  rw [show z + ζ • w - y = z - y + ζ • w by abel, indicator_of_mem (hin ζ hζ')]

lemma mollify_main (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε) :
    IsOpen (shrink U ε) ∧ ContDiffOn ℝ ∞ (molli ρ ε φ) (shrink U ε) ∧
      IsPsh (shrink U ε) (molli ρ ε φ) ∧
      ∀ z ∈ shrink U ε, φ z ≤ molli ρ ε φ z ∧ molli ρ ε φ z ≤ polyMax φ z ε := by
  have hcont : ContinuousOn (molli ρ ε φ) (shrink U ε) := fun z hz =>
    (molli_contDiffAt ρ hU hφ hε hz).continuousAt.continuousWithinAt
  refine ⟨isOpen_shrink hU hε, fun z hz => (molli_contDiffAt ρ hU hφ hε hz).contDiffWithinAt,
    ⟨hcont.upperSemicontinuousOn, fun z w hd => ⟨?_, molli_submean ρ hU hφ hε hd⟩⟩,
    fun z hz => ⟨le_molli ρ hU hφ hε hz, molli_le_polyMax ρ hU hφ hε hz⟩⟩
  refine ContinuousOn.circleIntegrable' ?_
  refine hcont.comp (by fun_prop : Continuous fun ζ : ℂ => z + ζ • w).continuousOn fun ζ hζ => ?_
  exact hd ζ (by simp at hζ; linarith)

end Moll

end

end ReciprocityTheory.AnForm.A

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh IsPosPot IsSection logNormSec mInt
  MIntegrable maMeasure maMeasure_thm logNormIntegrable mIntegrableCont)

noncomputable section

theorem continuousAt_of_charts {e : ℕ} {X : Type} [TopologicalSpace X] {E : Type}
    [TopologicalSpace E] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) (g : X → E)
    (hg : ∀ j, ContinuousOn (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  set c := A.chart j
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hmem : c y ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hj, by
    show c.symm (c y) ∈ U
    rw [c.left_inv hj]
    exact hy⟩
  have h1 : ContinuousAt (g ∘ c.symm) (c y) := (hg j).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((g ∘ c.symm) ∘ c) y := h1.comp (c.continuousAt hj)
  refine h2.congr ?_
  filter_upwards [c.open_source.mem_nhds hj] with z hz
  simp [Function.comp, c.left_inv hz]

theorem continuous_secNorm {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous (secNorm L s) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hsc : ContinuousAt (s x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (s x₀)
    (fun j => (hs.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hφc : ContinuousAt (L.φ x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (L.φ x₀)
    (fun j => (hL.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hf : ContinuousAt (fun y => ‖s x₀ y‖ * Real.exp (-L.φ x₀ y)) x₀ :=
    hsc.norm.mul (Real.continuous_exp.continuousAt.comp hφc.neg)
  refine hf.congr ?_
  filter_upwards [(L.isOpen_U x₀).mem_nhds (L.mem_U x₀)] with y hy
  exact hs.2 x₀ y y ⟨hy, L.mem_U y⟩

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (hP : IsPosPot A P) : IsPsh A P := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (hP x j y hy w hw).le

theorem greenEp_nonneg {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (x : W) : 0 ≤ greenEp L s ε x := by
  unfold greenEp
  apply Real.log_nonneg
  have : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  linarith

theorem greenEp_le_one {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : W) : greenEp L s ε x ≤ greenEp L s 1 x := by
  unfold greenEp
  have h0 : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  apply Real.log_le_log (by linarith)
  have : ε / secNorm L s x ^ 2 ≤ 1 / secNorm L s x ^ 2 :=
    div_le_div_of_nonneg_right hε1 (sq_nonneg _)
  linarith

theorem greenEp_one_eq {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) (x : W) :
    greenEp L s 1 x = Real.log (secNorm L s x ^ 2 + 1) - 2 * logNormSec L s x := by
  have hl : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp
  rw [hl]
  by_cases hN : secNorm L s x = 0
  · simp [hN]
  · have h2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hN
    have h3 : secNorm L s x ^ 2 + 1 ≠ 0 := by positivity
    rw [show 1 + 1 / secNorm L s x ^ 2 = (secNorm L s x ^ 2 + 1) / secNorm L s x ^ 2 by
      field_simp, Real.log_div h3 h2, Real.log_pow]
    push_cast
    ring

theorem greenEp_tendsto_zero {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ)
    (x : W) : Tendsto (fun ε => greenEp L s ε x) (𝓝[>] 0) (𝓝 0) := by
  unfold greenEp
  set c := secNorm L s x ^ 2
  have hc : ContinuousAt (fun ε : ℝ => 1 + ε / c) 0 :=
    (continuous_const.add (continuous_id.div_const c)).continuousAt
  have hlog : ContinuousAt (fun ε : ℝ => Real.log (1 + ε / c)) 0 := hc.log (by simp)
  have ht := hlog.tendsto
  simp only [zero_div, add_zero, Real.log_one] at ht
  exact tendsto_nhdsWithin_of_tendsto_nhds ht

theorem GreenMassZero.proof : GreenMassZero.Statement := by
  intro D W _ _ _ S η hη
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set Φ : Fin (D + 1) → LocPot W := fun _ => S.Om.pot with hΦdef
  have hΦ : ∀ i, IsPotential S.A (Φ i) := fun _ => S.Om.isPot
  have hΦpsh : ∀ i, IsPsh S.A (Φ i) := fun _ => isPsh_of_isPosPot S.A _ S.Om.pos
  obtain ⟨hfin, hμ⟩ := maMeasure_thm S.A Φ hΦ hΦpsh
  set μ := maMeasure S.A Φ
  have hN : Continuous (secNorm S.L S.s) := continuous_secNorm S.A S.L S.s S.L_pot S.s_sec
  have hmeas : ∀ ε, Measurable (greenEp S.L S.s ε) := fun ε =>
    ((hN.measurable.pow_const 2).const_div ε |>.const_add 1).log

  have hlogN : Integrable (logNormSec S.L S.s) μ := by
    have hm : Measurable (logNormSec S.L S.s) := hN.measurable.log
    exact ((hμ _ hm).1).1 (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc Φ hΦ)
  have hh : Integrable (fun x => Real.log (secNorm S.L S.s x ^ 2 + 1)) μ := by
    have hc : Continuous fun x => Real.log (secNorm S.L S.s x ^ 2 + 1) :=
      ((hN.pow 2).add continuous_const).log fun x =>
        (by positivity : (0 : ℝ) < secNorm S.L S.s x ^ 2 + 1).ne'
    exact ((hμ _ hc.measurable).1).1 (mIntegrableCont S.A Φ hΦ _ hc)
  have hG1 : Integrable (greenEp S.L S.s 1) μ := by
    have : greenEp S.L S.s 1 = fun x =>
        Real.log (secNorm S.L S.s x ^ 2 + 1) - 2 * logNormSec S.L S.s x :=
      funext (greenEp_one_eq S.L S.s)
    rw [this]
    exact hh.sub (hlogN.const_mul 2)
  have hnorm : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x, ‖greenEp S.L S.s ε x‖ ≤ greenEp S.L S.s 1 x :=
    fun ε hε hε1 x => by
      rw [Real.norm_of_nonneg (greenEp_nonneg S.L S.s hε.le x)]
      exact greenEp_le_one S.L S.s hε.le hε1 x

  have hJ : ∀ ε, 0 < ε → ε ≤ 1 → ∀ t, S.J 0 ε t = ∫ x, greenEp S.L S.s ε x ∂μ := by
    intro ε hε hε1 t
    have hmix : mixedForms S.Om.pot (S.T t) 0 = Φ := by
      funext i
      simp [mixedForms, hΦdef]
    have hint : Integrable (greenEp S.L S.s ε) μ :=
      hG1.mono' (hmeas ε).aestronglyMeasurable (ae_of_all _ (hnorm ε hε hε1))
    have hmi : MIntegrable S.A Φ (greenEp S.L S.s ε) := ((hμ _ (hmeas ε)).1).2 hint
    show mInt S.A (mixedForms S.Om.pot (S.T t) 0) (greenEp S.L S.s ε) = _
    rw [hmix]
    exact (hμ _ (hmeas ε)).2 hmi

  have hT : Tendsto (fun ε => ∫ x, greenEp S.L S.s ε x ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε x => greenEp S.L S.s ε x) (f := fun _ => (0 : ℝ)) (greenEp S.L S.s 1)
      (Eventually.of_forall fun ε => (hmeas ε).aestronglyMeasurable)
      (eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε => ae_of_all _ (hnorm ε hε.1 hε.2))
      hG1 (ae_of_all _ fun x => greenEp_tendsto_zero S.L S.s x)
    simpa using this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ x, greenEp S.L S.s ε x ∂μ < η := (tendsto_order.1 hT).2 η hη
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min (u / 2) 1, lt_min (by linarith) one_pos, fun ε hε hεle t => ?_⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
  have hεu : ε < u := lt_of_le_of_lt (hεle.trans (min_le_left _ _)) (by linarith)
  rw [hJ ε hε hε1 t]
  exact (hsub ⟨hε, hεu⟩).le

end

end GroundTheory.Heights₂.Heights.AnalyticLimit

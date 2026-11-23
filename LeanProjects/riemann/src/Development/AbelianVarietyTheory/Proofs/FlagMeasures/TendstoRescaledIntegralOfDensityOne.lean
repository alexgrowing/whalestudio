import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.VagueRescale

theorem integral_le_of_small_balls {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] (κ : ℝ) (hκ : 0 ≤ κ)
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (h : ∀ x ∈ U, ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : ∀ x, 0 ≤ f x) (hU : ∀ x ∉ U, f x = 0) :
    ∫ x, f x ∂μ ≤ κ * ∫ x, f x ∂ν := by
  have hcν : ∀ A, (κ.toNNReal • ν) A = ENNReal.ofReal κ * ν A := fun A => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]; rfl

  have hsub : ∀ s ⊆ U, μ s ≤ (κ.toNNReal • ν) s := by
    intro s hs
    refine (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le (κ.toNNReal • ν)
      (Measure.AbsolutelyContinuous.refl μ) s fun x hx => ?_
    have hfr := (Besicovitch.tendsto_filterAt μ x).frequently
      (p := fun a => μ a ≤ ENNReal.ofReal κ * ν a) (h x (hs hx)).frequently
    exact hfr.mono fun a ha => ha.trans_eq (hcν a).symm
  have hle : μ.restrict U ≤ κ.toNNReal • ν.restrict U := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, ← Measure.smul_apply]
    exact hsub _ Set.inter_subset_right
  calc ∫ x, f x ∂μ = ∫ x, f x ∂(μ.restrict U) := (setIntegral_eq_integral_of_forall_compl_eq_zero hU).symm
    _ ≤ ∫ x, f x ∂(κ.toNNReal • ν.restrict U) :=
        integral_mono_measure hle (Filter.Eventually.of_forall h0) (hf.integrable_of_hasCompactSupport hc)
    _ = κ * ∫ x, f x ∂ν := by
        rw [integral_smul_nnreal_measure, setIntegral_eq_integral_of_forall_compl_eq_zero hU,
          NNReal.smul_def, Real.coe_toNNReal _ hκ, smul_eq_mul]

private theorem rescaled_integral_comparable_of_nonneg_compactSupport {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ν] (κ δ : ℝ) (hκ : 1 < κ)
    (hball : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (h0 : ∀ x, 0 ≤ φ x) (R r : ℝ) (hR : ∀ x : EuclideanSpace ℝ (Fin d), R ≤ ‖x‖ → φ x = 0)
    (hr : 0 < r) (hrR : r * R < δ) :
    (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν ≤ κ * ∫ x, φ x ∧
      ∫ x, φ x ≤ κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => r⁻¹ • x) :=
    (continuous_const_smul _).measurable
  have hJ : ∫ x, φ x ∂(ν.map (fun x => r⁻¹ • x)) = ∫ x, φ (r⁻¹ • x) ∂ν :=
    integral_map hmeas.aemeasurable hφ.aestronglyMeasurable
  have hrd : 0 < r ^ d := pow_pos hr d

  have hpre : ∀ (y : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 ≤ s →
      (ν.map (fun x => r⁻¹ • x)) (Metric.closedBall y s) = ν (Metric.closedBall (r • y) (r * s)) := by
    intro y s hs
    rw [Measure.map_apply hmeas Metric.isClosed_closedBall.measurableSet, Set.preimage_smul_inv₀ hr.ne',
      smul_closedBall _ _ hs, Real.norm_of_nonneg hr.le]
  have hvol : ∀ (y : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 ≤ s →
      volume (Metric.closedBall (r • y) (r * s)) =
        ENNReal.ofReal (r ^ d) * volume (Metric.closedBall y s) := by
    intro y s hs
    rw [Measure.addHaar_closedBall' _ _ (mul_nonneg hr.le hs), Measure.addHaar_closedBall' _ _ hs,
      finrank_euclideanSpace_fin, mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le _), mul_assoc]
  have hcv : ∀ A, ((r ^ d).toNNReal • volume : Measure (EuclideanSpace ℝ (Fin d))) A =
      ENNReal.ofReal (r ^ d) * volume A := fun A => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]; rfl
  have hscale : Filter.Tendsto (fun s : ℝ => r * s) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_const_mul r).tendsto (0 : ℝ))
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hr hs
  set U : Set (EuclideanSpace ℝ (Fin d)) := {y | r * ‖y‖ < δ} with hU
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin d), ‖r • y‖ = r * ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
  have hvan : ∀ y ∉ U, φ y = 0 := by
    intro y hy
    simp only [hU, Set.mem_setOf_eq, not_lt] at hy
    refine hR y ?_
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt hr]
  have hnear : ∀ y ∈ U, ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (ν (Metric.closedBall (r • y) (r * s)) ≤
          ENNReal.ofReal κ * volume (Metric.closedBall (r • y) (r * s)) ∧
        volume (Metric.closedBall (r • y) (r * s)) ≤
          ENNReal.ofReal κ * ν (Metric.closedBall (r • y) (r * s))) ∧ 0 < s := by
    intro y hy
    have hy' : ‖r • y‖ < δ := by rw [hnorm]; exact hy
    filter_upwards [hscale.eventually (hball _ hy'), self_mem_nhdsWithin] with s hs hs0
    exact ⟨hs, hs0⟩
  have A1 := integral_le_of_small_balls (ν.map (fun x => r⁻¹ • x)) ((r ^ d).toNNReal • volume) κ
    (by linarith) U (fun y hy => (hnear y hy).mono fun s hs => by
      rw [hpre y s hs.2.le, hcv, ← hvol y s hs.2.le]; exact hs.1.1) φ hφ hc h0 hvan
  have A2 := integral_le_of_small_balls ((r ^ d).toNNReal • volume) (ν.map (fun x => r⁻¹ • x)) κ
    (by linarith) U (fun y hy => (hnear y hy).mono fun s hs => by
      rw [hpre y s hs.2.le, hcv, ← hvol y s hs.2.le]; exact hs.1.2) φ hφ hc h0 hvan
  have hvolint : ∫ x, φ x ∂((r ^ d).toNNReal • volume) = r ^ d * ∫ x, φ x := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ hrd.le, smul_eq_mul]
  rw [hJ, hvolint] at A1 A2
  constructor
  · rw [inv_mul_le_iff₀ hrd]
    linarith
  · rw [show κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) = (κ * ∫ x, φ (r⁻¹ • x) ∂ν) / r ^ d by
      field_simp, le_div_iff₀ hrd]
    linarith

theorem tendsto_of_nonneg {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (h : ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (h0 : ∀ x, 0 ≤ φ x) :
    Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, φ x)) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), R ≤ ‖x‖ → φ x = 0 := by
    obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R₀ + 1, fun x hx => ?_⟩
    by_contra hne
    have hx' := hR₀ (subset_tsupport φ (Function.mem_support.2 hne))
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    linarith
  have hL0 : 0 ≤ ∫ x, φ x := integral_nonneg h0
  have key : ∀ κ : ℝ, 1 < κ → ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν ≤ κ * ∫ x, φ x ∧
        ∫ x, φ x ≤ κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) := by
    intro κ hκ
    obtain ⟨δ, hδ, hball⟩ := h κ hκ
    have hlin : Filter.Tendsto (fun r : ℝ => r * R) (nhds 0) (nhds 0) := by
      have := ((continuous_mul_const R).tendsto (0 : ℝ))
      rwa [zero_mul] at this
    filter_upwards [(hlin.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds hδ),
      self_mem_nhdsWithin] with r hrR hr
    exact rescaled_integral_comparable_of_nonneg_compactSupport ν κ δ hκ hball φ hφ hc h0 R r hR hr hrR
  rw [Metric.tendsto_nhds]
  intro ε hε
  set L := ∫ x, φ x with hLdef
  set η : ℝ := min 1 (ε / (2 * (L + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η * (2 * (L + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  filter_upwards [key (1 + η) (by linarith)] with r hr
  obtain ⟨hu, hl⟩ := hr
  set I := (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν
  have h6 : 0 ≤ η * L := mul_nonneg hη.le hL0
  have h3 : η * I ≤ η * ((1 + η) * L) := mul_le_mul_of_nonneg_left hu hη.le
  have h4 : η * (η * L) ≤ 1 * (η * L) := mul_le_mul_of_nonneg_right hη1 h6
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end GlobalTheory.VagueRescale

namespace GlobalTheory

theorem tendsto_rescaled_integral_of_density_one :
    ∀ (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ν →
    (∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r)) →
    ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, Continuous φ → HasCompactSupport φ →
    Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, φ x)) := by
  intro d ν hν h φ hφ hc
  have hsplit : ∀ t : ℝ, max t 0 - max (-t) 0 = t := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (by linarith)]; ring
    · rw [max_eq_right ht, max_eq_left (by linarith)]; ring
  have hp : Continuous (fun x => max (φ x) 0) := hφ.max continuous_const
  have hm : Continuous (fun x => max (-φ x) 0) := hφ.neg.max continuous_const
  have hpc : HasCompactSupport (fun x => max (φ x) 0) :=
    hc.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hmc : HasCompactSupport (fun x => max (-φ x) 0) :=
    hc.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have Tp := VagueRescale.tendsto_of_nonneg ν h _ hp hpc (fun x => le_max_right _ _)
  have Tm := VagueRescale.tendsto_of_nonneg ν h _ hm hmc (fun x => le_max_right _ _)
  have hint : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Continuous g → HasCompactSupport g →
      ∀ r : ℝ, Integrable (fun x => g (r⁻¹ • x)) ν := by
    intro g hg hgc r
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
    exact Integrable.of_bound (hg.comp (continuous_const_smul _)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => hC _)
  have heq : (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) = fun r =>
      (r ^ d)⁻¹ * ∫ x, max (φ (r⁻¹ • x)) 0 ∂ν - (r ^ d)⁻¹ * ∫ x, max (-φ (r⁻¹ • x)) 0 ∂ν := by
    funext r
    rw [← mul_sub, ← integral_sub (hint _ hp hpc r) (hint _ hm hmc r)]
    simp only [hsplit]
  have hvol : ∫ x, φ x = (∫ x, max (φ x) 0) - ∫ x, max (-φ x) 0 := by
    rw [← integral_sub (hp.integrable_of_hasCompactSupport hpc) (hm.integrable_of_hasCompactSupport hmc)]
    simp only [hsplit]
  rw [heq, hvol]
  exact Tp.sub Tm

end GlobalTheory

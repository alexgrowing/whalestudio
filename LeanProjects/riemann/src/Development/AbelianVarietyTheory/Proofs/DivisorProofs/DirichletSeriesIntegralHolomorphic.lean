import Mathlib
open MeasureTheory Filter Topology Metric

namespace GlobalTheory.TsumCpowHol

lemma abs_log_le_rpow_add (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    |Real.log c| ≤ (c ^ δ + c ^ (-δ)) / δ := by
  have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc δ)
  have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc (-δ))
  rw [Real.log_rpow hc] at h1 h2
  have h3 := Real.rpow_pos_of_pos hc δ
  have h4 := Real.rpow_pos_of_pos hc (-δ)
  rw [le_div_iff₀ hδ]
  rcases abs_cases (Real.log c) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith

lemma rpow_le_rpow_add_rpow (c lo hi σ : ℝ) (hc : 0 < c) (h1 : lo ≤ σ) (h2 : σ ≤ hi) :
    c ^ σ ≤ c ^ lo + c ^ hi := by
  rcases le_or_gt 1 c with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    have := Real.rpow_nonneg hc.le lo
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hc h.le h1
    have := Real.rpow_nonneg hc.le hi
    linarith

lemma norm_cpow_mul_log_le (c : ℝ) (hc : 0 < c) (s : ℂ) (δ lo hi : ℝ) (hδ : 0 < δ)
    (hlo : lo ≤ s.re - δ) (hhi : s.re + δ ≤ hi) :
    ‖(c : ℂ) ^ s * Complex.log c‖ ≤ 2 / δ * (c ^ lo + c ^ hi) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc, ← Complex.ofReal_log hc.le,
    Complex.norm_real, Real.norm_eq_abs]
  have hl := abs_log_le_rpow_add c δ hc hδ
  have hp := Real.rpow_pos_of_pos hc s.re
  have e1 := rpow_le_rpow_add_rpow c lo hi (s.re + δ) hc (by linarith) hhi
  have e2 := rpow_le_rpow_add_rpow c lo hi (s.re + -δ) hc (by linarith) (by linarith)
  calc c ^ s.re * |Real.log c| ≤ c ^ s.re * ((c ^ δ + c ^ (-δ)) / δ) :=
        mul_le_mul_of_nonneg_left hl hp.le
    _ = (c ^ (s.re + δ) + c ^ (s.re + -δ)) / δ := by
        rw [Real.rpow_add hc, Real.rpow_add hc]; ring
    _ ≤ ((c ^ lo + c ^ hi) + (c ^ lo + c ^ hi)) / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        linarith
    _ = 2 / δ * (c ^ lo + c ^ hi) := by ring

lemma aestronglyMeasurable_tsum_of_ae_summable {α ι : Type} [MeasurableSpace α] {μ : Measure α}
    [Countable ι] (g : ι → α → ℂ) (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    (hs : ∀ᵐ x ∂μ, Summable (fun i => g i x)) :
    AEStronglyMeasurable (fun x => ∑' i, g i x) μ :=
  aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
    (f := fun F x => ∑ i ∈ F, g i x)
    (fun F => Finset.aestronglyMeasurable_fun_sum F (fun i _ => hg i))
    (hs.mono fun x hx => hx.hasSum)

theorem tsum_cpow_integrable_and_differentiableOn :
    ∀ {α ι : Type} [MeasurableSpace α] (μ : Measure α) (φ : ι → α → ℝ) (a : ℝ), (∀ i, Measurable (φ i)) →
    (∀ i x, 0 < φ i x) → (∀ s : ℝ, a < s → ∫⁻ x, ∑' i, ENNReal.ofReal (φ i x ^ s) ∂μ < ⊤) →
    (∀ s : ℂ, a < s.re → Integrable (fun x => ∑' i, (φ i x : ℂ) ^ s) μ) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∫ x, ∑' i, (φ i x : ℂ) ^ s ∂μ) {s | a < s.re} := by
  intro α ι _ μ φ a hφm hφp hfin
  by_cases hμ : μ = 0
  · subst hμ
    refine ⟨fun s _ => integrable_zero_measure, ?_⟩
    simp only [integral_zero_measure]
    exact differentiableOn_const 0
  have hcount : Countable ι := by
    by_contra hc
    have hall : ∀ x, ∑' i, ENNReal.ofReal (φ i x ^ (a + 1)) = ⊤ := by
      intro x
      by_contra hne
      apply hc
      have hcs := Summable.countable_support_ennreal hne
      have hsupp : Function.support (fun i => ENNReal.ofReal (φ i x ^ (a + 1))) = Set.univ := by
        ext i
        simp [Real.rpow_pos_of_pos (hφp i x)]
      rw [hsupp] at hcs
      exact Set.countable_univ_iff.mp hcs
    have h := hfin (a + 1) (by linarith)
    simp only [hall, lintegral_const, ENNReal.top_mul (Measure.measure_univ_ne_zero.mpr hμ)] at h
    exact lt_irrefl _ h
  have hEm : ∀ t : ℝ, Measurable (fun x => ∑' i, ENNReal.ofReal (φ i x ^ t)) := fun t =>
    Measurable.ennreal_tsum (fun i => ((hφm i).pow_const t).ennreal_ofReal)
  have htoReal : ∀ (t : ℝ) (x : α),
      (fun i => (ENNReal.ofReal (φ i x ^ t)).toReal) = fun i => φ i x ^ t := fun t x =>
    funext fun i => ENNReal.toReal_ofReal (Real.rpow_nonneg (hφp i x).le t)
  have hsum : ∀ t : ℝ, a < t → ∀ᵐ x ∂μ, Summable (fun i => φ i x ^ t) := by
    intro t ht
    filter_upwards [ae_lt_top (hEm t) (hfin t ht).ne] with x hx
    have h := ENNReal.summable_toReal hx.ne
    rwa [htoReal] at h
  have hreal : ∀ t : ℝ, a < t → Integrable (fun x => ∑' i, φ i x ^ t) μ := by
    intro t ht
    have h := integrable_toReal_of_lintegral_ne_top (hEm t).aemeasurable (hfin t ht).ne
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only
    rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top), htoReal]
  have hterm : ∀ (s : ℂ) (i : ι), AEStronglyMeasurable (fun x => (φ i x : ℂ) ^ s) μ := fun s i =>
    ((Complex.measurable_ofReal.comp (hφm i)).pow_const s).aestronglyMeasurable
  have hnorm : ∀ (s : ℂ) (i : ι) (x : α), ‖(φ i x : ℂ) ^ s‖ = φ i x ^ s.re := fun s i x =>
    Complex.norm_cpow_eq_rpow_re_of_pos (hφp i x) s
  have hint : ∀ s : ℂ, a < s.re → Integrable (fun x => ∑' i, (φ i x : ℂ) ^ s) μ := by
    intro s hs
    have hsn : ∀ᵐ x ∂μ, Summable (fun i => ‖(φ i x : ℂ) ^ s‖) := by
      filter_upwards [hsum s.re hs] with x hx
      simpa only [hnorm] using hx
    refine (hreal s.re hs).mono'
      (aestronglyMeasurable_tsum_of_ae_summable _ (fun i => hterm s i)
        (hsn.mono fun x hx => hx.of_norm)) ?_
    filter_upwards [hsn] with x hx
    refine (norm_tsum_le_tsum_norm hx).trans (le_of_eq ?_)
    simp only [hnorm]
  refine ⟨hint, ?_⟩
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  intro s₀ hs₀
  apply DifferentiableAt.differentiableWithinAt
  simp only [Set.mem_setOf_eq] at hs₀
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (s₀.re - a) / 4 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨lo, hlodef⟩ : ∃ lo : ℝ, lo = s₀.re - 2 * δ := ⟨_, rfl⟩
  obtain ⟨hi, hhidef⟩ : ∃ hi : ℝ, hi = s₀.re + 2 * δ := ⟨_, rfl⟩
  have hlo : a < lo := by rw [hlodef, hδdef]; linarith
  have hhi : a < hi := by rw [hhidef]; linarith
  have hball : ∀ s ∈ ball s₀ δ, lo ≤ s.re - δ ∧ s.re + δ ≤ hi := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    have h := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at h
    have h2 := abs_le.mp (h.trans hs.le)
    constructor <;> linarith [h2.1, h2.2]
  have hderiv_term : ∀ (i : ι) (x : α) (s : ℂ), HasDerivAt (fun s : ℂ => (φ i x : ℂ) ^ s)
      ((φ i x : ℂ) ^ s * Complex.log (φ i x)) s := fun i x s =>
    (Complex.hasStrictDerivAt_const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hφp i x).ne'))).hasDerivAt
  have hbnd : ∀ (i : ι) (x : α), ∀ s ∈ ball s₀ δ,
      ‖(φ i x : ℂ) ^ s * Complex.log (φ i x)‖ ≤ 2 / δ * (φ i x ^ lo + φ i x ^ hi) :=
    fun i x s hs => norm_cpow_mul_log_le _ (hφp i x) s δ lo hi hδ (hball s hs).1 (hball s hs).2
  have hgood := (hsum lo hlo).and (hsum hi hhi)
  have hu : ∀ x, Summable (fun i => φ i x ^ lo) → Summable (fun i => φ i x ^ hi) →
      Summable (fun i => 2 / δ * (φ i x ^ lo + φ i x ^ hi)) := fun x h1 h2 =>
    (h1.add h2).mul_left _
  have hs₀b : s₀ ∈ ball s₀ δ := mem_ball_self hδ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s x => ∑' i, (φ i x : ℂ) ^ s)
    (F' := fun s x => ∑' i, (φ i x : ℂ) ^ s * Complex.log (φ i x)) (x₀ := s₀)
    (bound := fun x => 2 / δ * (∑' i, φ i x ^ lo + ∑' i, φ i x ^ hi))
    (ball_mem_nhds s₀ hδ)
    (Filter.eventually_of_mem (hopen.mem_nhds hs₀) fun s hs => (hint s hs).aestronglyMeasurable)
    (hint s₀ hs₀)
    (aestronglyMeasurable_tsum_of_ae_summable _
      (fun i => (hterm s₀ i).mul
        (Complex.measurable_log.comp (Complex.measurable_ofReal.comp (hφm i))).aestronglyMeasurable)
      (by
        filter_upwards [hgood] with x hx
        exact Summable.of_norm_bounded (hu x hx.1 hx.2) (fun i => hbnd i x s₀ hs₀b)))
    (by
      filter_upwards [hgood] with x hx
      intro s hs
      have hsn : Summable (fun i => ‖(φ i x : ℂ) ^ s * Complex.log (φ i x)‖) :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hbnd i x s hs) (hu x hx.1 hx.2)
      refine (norm_tsum_le_tsum_norm hsn).trans
        ((Summable.tsum_le_tsum (fun i => hbnd i x s hs) hsn (hu x hx.1 hx.2)).trans (le_of_eq ?_))
      rw [tsum_mul_left, Summable.tsum_add hx.1 hx.2])
    (((hreal lo hlo).add (hreal hi hhi)).const_mul (2 / δ))
    (by
      filter_upwards [hgood] with x hx
      intro s hs
      refine hasDerivAt_tsum_of_isPreconnected (hu x hx.1 hx.2) isOpen_ball
        (convex_ball s₀ δ).isPreconnected (fun i s' _ => hderiv_term i x s')
        (fun i s' hs' => hbnd i x s' hs') hs₀b ?_ hs
      refine Summable.of_norm_bounded (hx.1.add hx.2) (fun i => ?_)
      rw [hnorm]
      exact rpow_le_rpow_add_rpow _ _ _ _ (hφp i x) (by rw [hlodef]; linarith)
        (by rw [hhidef]; linarith))
  exact key.2.differentiableAt

end GlobalTheory.TsumCpowHol

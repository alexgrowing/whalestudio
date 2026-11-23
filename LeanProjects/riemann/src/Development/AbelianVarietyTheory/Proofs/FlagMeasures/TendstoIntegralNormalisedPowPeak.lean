import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH

open MeasureTheory Matrix Filter Topology

namespace GlobalTheory

theorem tendsto_integral_normalised_pow_peak :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  intro X _ _ _ _ μ hμ K x₀ f hK hKc hx₀ hpos hf hf1 hf01 hsep E _ _ _ F hF
  have hKae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hKc
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμK : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hKae
  have hFm : AEStronglyMeasurable F μ := by
    have h := hF.aestronglyMeasurable_of_isCompact (μ := μ) hK hKm
    rwa [hμK] at h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x₀ hx₀)

  have hfm_int : ∀ m : ℕ, Integrable (fun x => f x ^ m) μ := by
    intro m
    refine Integrable.of_bound (hf.pow m).aestronglyMeasurable 1 ?_
    filter_upwards [hKae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf01 x hx).1 m)]
    exact pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2

  have hlow : ∀ η : ℝ, 0 ≤ η → ∀ m : ℕ,
      η ^ m * μ.real {x | η < f x} ≤ ∫ y, f y ^ m ∂μ := by
    intro η hη m
    have hWm : MeasurableSet {x | η < f x} := measurableSet_lt measurable_const hf.measurable
    have h := integral_indicator_const (μ := μ) (η ^ m) hWm
    rw [smul_eq_mul] at h
    rw [mul_comm, ← h]
    refine integral_mono_ae ((integrable_const (η ^ m)).indicator hWm) (hfm_int m) ?_
    filter_upwards [hKae] with x hx
    by_cases hxW : x ∈ {x | η < f x}
    · rw [Set.indicator_apply, if_pos hxW]
      exact pow_le_pow_left₀ hη (le_of_lt hxW) m
    · rw [Set.indicator_apply, if_neg hxW]
      exact pow_nonneg (hf01 x hx).1 m
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨u, hu_open, hx₀u, hu⟩ :=
    mem_nhdsWithin.mp ((hF x₀ hx₀) (Metric.ball_mem_nhds (F x₀) (half_pos hε)))
  obtain ⟨δ, hδ1, hδ⟩ := hsep u (hu_open.mem_nhds hx₀u)
  obtain ⟨d, hd0, hd1, hδd⟩ : ∃ d : ℝ, 0 ≤ d ∧ d < 1 ∧ δ ≤ d :=
    ⟨max δ 0, le_max_right _ _, max_lt hδ1 one_pos, le_max_left _ _⟩
  obtain ⟨η, hη0, hdη, hη1⟩ : ∃ η : ℝ, 0 < η ∧ d < η ∧ η < 1 :=
    ⟨(d + 1) / 2, by linarith, by linarith, by linarith⟩
  have hWpos : 0 < μ {x | η < f x} :=
    hpos _ (isOpen_lt continuous_const hf) (by show η < f x₀; rw [hf1]; exact hη1)
  have hW : 0 < μ.real {x | η < f x} := ENNReal.toReal_pos hWpos.ne' (measure_ne_top μ _)
  have hr : Tendsto (fun m : ℕ => (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x})
      atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd0 hη0.le)
      ((div_lt_one hη0).mpr hdη)).const_mul (2 * C + 1)).div_const (μ.real {x | η < f x})
    simpa using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hr (Iio_mem_nhds (half_pos hε)))
  refine ⟨N, fun m hm => ?_⟩
  have hIpos : 0 < ∫ y, f y ^ m ∂μ :=
    lt_of_lt_of_le (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  set c : X → ℂ := fun x => ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) with hc
  have hc_cont : Continuous c :=
    Complex.continuous_ofReal.comp ((hf.pow m).div_const _)
  have hcnorm : ∀ x ∈ K, ‖c x‖ = f x ^ m / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hc, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le)]
  have hcle : ∀ x ∈ K, ‖c x‖ ≤ 1 / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hcnorm x hx]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2) hIpos.le
  have hc_int : Integrable c μ := by
    refine Integrable.of_bound hc_cont.aestronglyMeasurable (1 / ∫ y, f y ^ m ∂μ) ?_
    filter_upwards [hKae] with x hx
    exact hcle x hx
  have hcF_int : Integrable (fun x => c x • F x) μ := by
    refine Integrable.of_bound (hc_cont.aestronglyMeasurable.smul hFm)
      (1 / (∫ y, f y ^ m ∂μ) * C) ?_
    filter_upwards [hKae] with x hx
    rw [norm_smul]
    exact mul_le_mul (hcle x hx) (hC x hx) (norm_nonneg _) (by positivity)

  have hint1 : ∫ x, c x ∂μ = 1 := by
    show ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_div, div_self hIpos.ne', Complex.ofReal_one]
  have hkey : (∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) - F x₀
      = ∫ x, c x • (F x - F x₀) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hcF_int (hc_int.smul_const (F x₀)), integral_smul_const, hint1, one_smul]
  set B : ℝ := (2 * C + 1) * d ^ m / ∫ y, f y ^ m ∂μ with hB
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg (by linarith) (pow_nonneg hd0 m)) hIpos.le
  have hbound : ∀ᵐ x ∂μ, ‖c x • (F x - F x₀)‖
      ≤ (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B := by
    filter_upwards [hKae] with x hx
    have h0 : 0 ≤ f x ^ m / ∫ y, f y ^ m ∂μ :=
      div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le
    rw [norm_smul, hcnorm x hx]
    by_cases hxu : x ∈ u
    · have hlt : ‖F x - F x₀‖ < ε / 2 := by
        have h := hu ⟨hxu, hx⟩
        simpa [dist_eq_norm] using h
      have := mul_le_mul_of_nonneg_left hlt.le h0
      linarith
    · have hfx : f x ≤ d := le_trans (hδ x hx hxu) hδd
      have hpow : f x ^ m ≤ d ^ m := pow_le_pow_left₀ (hf01 x hx).1 hfx m
      have hFd : ‖F x - F x₀‖ ≤ 2 * C + 1 := by
        have := norm_sub_le (F x) (F x₀)
        linarith [hC x hx, hC x₀ hx₀]
      have h1 : f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖ ≤ B := by
        calc f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖
            = (‖F x - F x₀‖ * f x ^ m) / ∫ y, f y ^ m ∂μ := by ring
          _ ≤ ((2 * C + 1) * d ^ m) / ∫ y, f y ^ m ∂μ :=
            div_le_div_of_nonneg_right
              (mul_le_mul hFd hpow (pow_nonneg (hf01 x hx).1 m) (by linarith)) hIpos.le
      have h2 : 0 ≤ f x ^ m / (∫ y, f y ^ m ∂μ) * (ε / 2) := mul_nonneg h0 (by linarith)
      linarith
  have hBle : B ≤ (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x} := by
    rw [hB, div_pow, mul_div_assoc', div_div]
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (pow_nonneg hd0 m))
      (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  have hBlt : B < ε / 2 := lt_of_le_of_lt hBle (hN m hm)
  have hg_int : Integrable (fun x => (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) μ :=
    (((hfm_int m).div_const _).mul_const _).add (integrable_const _)
  rw [dist_eq_norm, hkey]
  calc ‖∫ x, c x • (F x - F x₀) ∂μ‖
      ≤ ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) ∂μ :=
        norm_integral_le_of_norm_le hg_int hbound
    _ = ε / 2 + B := by
        rw [integral_add (((hfm_int m).div_const _).mul_const _) (integrable_const _),
          integral_mul_const, integral_div, div_self hIpos.ne', integral_const]
        simp
    _ < ε := by linarith

end GlobalTheory

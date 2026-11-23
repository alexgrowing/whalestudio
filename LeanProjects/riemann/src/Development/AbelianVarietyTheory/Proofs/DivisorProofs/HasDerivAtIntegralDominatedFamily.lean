import Mathlib
open MeasureTheory

namespace GlobalTheory

open Set Filter Topology

theorem enorm_sub_le_lintegral_of_hasDerivAt_complex (f f' : ℝ → ℂ)
    (h : ∀ s, HasDerivAt f (f' s) s) {a b : ℝ} (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ r in Ioc a b, ‖f' r‖ₑ := by
  have hm : StronglyMeasurable f' := by
    have : f' = deriv f := funext fun s => (h s).deriv.symm
    rw [this]
    exact stronglyMeasurable_deriv f
  by_cases hi : IntegrableOn f' (Ioc a b)
  · have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) (fun s _ => h s)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hi)
    rw [← this, intervalIntegral.integral_of_le hab]
    exact enorm_integral_le_lintegral_enorm _
  · have : ¬ HasFiniteIntegral f' (volume.restrict (Ioc a b)) := fun hf =>
      hi ⟨hm.aestronglyMeasurable, hf⟩
    rw [hasFiniteIntegral_iff_enorm, not_lt] at this
    exact le_top.trans this

theorem exists_conull_stronglyMeasurable_uncurry {α : Type} [MeasurableSpace α] (μ : Measure α)
    (F : ℝ → α → ℂ) (hc : ∀ x, Continuous fun r => F r x)
    (hm : ∀ s, AEStronglyMeasurable (F s) μ) :
    ∃ N : Set α, (∀ᵐ x ∂μ, x ∈ N) ∧
      StronglyMeasurable (Function.uncurry fun s x => N.indicator (F s) x) := by
  have h1 : ∀ᵐ x ∂μ, ∀ q : ℚ, F q x = (hm q).mk (F q) x :=
    ae_all_iff.2 fun q => (hm q).ae_eq_mk
  obtain ⟨M, hM, hMm, hM0⟩ := exists_measurable_superset_of_null (ae_iff.1 h1)
  refine ⟨Mᶜ, ?_, ?_⟩
  · exact compl_mem_ae_iff.2 hM0
  have hcont : ∀ x, Continuous fun s => Mᶜ.indicator (F s) x := by
    intro x
    by_cases hx : x ∈ Mᶜ
    · simpa only [indicator_of_mem hx] using hc x
    · simpa only [indicator_of_notMem hx] using continuous_const
  have hq : ∀ q : ℚ, StronglyMeasurable (Mᶜ.indicator (F q)) := by
    intro q
    have : Mᶜ.indicator (F q) = Mᶜ.indicator ((hm q).mk (F q)) := by
      funext x
      by_cases hx : x ∈ Mᶜ
      · rw [indicator_of_mem hx, indicator_of_mem hx]
        by_contra hne
        exact hx (hM fun hall => hne (hall q))
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]
    rw [this]
    exact (hm q).stronglyMeasurable_mk.indicator hMm.compl
  refine stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont ?_
  intro s
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1
    ((Rat.denseRange_cast (𝕜 := ℝ)) s)
  choose q hq' using hu
  refine stronglyMeasurable_of_tendsto (u := atTop) (f := fun n => Mᶜ.indicator (F (q n)))
    (fun n => hq _) ?_
  rw [tendsto_pi_nhds]
  intro x
  have := ((hcont x).tendsto s).comp hlim
  refine this.congr fun n => ?_
  simp only [Function.comp, hq']

theorem stronglyMeasurable_uncurry_of_hasDerivAt {α : Type} [MeasurableSpace α]
    (H H' : ℝ → α → ℂ) (h : ∀ x s, HasDerivAt (fun r => H r x) (H' s x) s)
    (hm : StronglyMeasurable (Function.uncurry H)) :
    StronglyMeasurable (Function.uncurry H') := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun n => (Nat.one_div_pos_of_nat (n := n)).ne'
  refine stronglyMeasurable_of_tendsto (u := atTop)
    (f := fun (n : ℕ) (p : ℝ × α) => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
      (H (p.1 + (1 : ℝ) / ((n : ℝ) + 1)) p.2 - H p.1 p.2)) (fun n => ?_) ?_
  · have h1 := hm.comp_measurable (g := fun p : ℝ × α => (p.1 + (1 : ℝ) / ((n : ℝ) + 1), p.2))
      (by fun_prop)
    exact (h1.sub hm).const_smul (((1 : ℝ) / ((n : ℝ) + 1))⁻¹)
  · rw [tendsto_pi_nhds]
    rintro ⟨s, x⟩
    exact (hasDerivAt_iff_tendsto_slope_zero.1 (h x s)).comp ht

theorem lintegral_enorm_sub_le_of_hasDerivAt_of_le {α : Type} [MeasurableSpace α] (μ : Measure α)
    (F F' : ℝ → α → ℂ) (h : ∀ x s, HasDerivAt (fun r => F r x) (F' s x) s)
    (hi : ∀ s, Integrable (F s) μ) {a b : ℝ} (hab : a ≤ b) (C : ENNReal)
    (hC : ∀ s ∈ Icc a b, ∫⁻ x, ‖F' s x‖ₑ ∂μ ≤ C) :
    ∫⁻ x, ‖F b x - F a x‖ₑ ∂μ ≤ C * ENNReal.ofReal (b - a) := by
  obtain ⟨N, hN, hNm⟩ := exists_conull_stronglyMeasurable_uncurry μ F
    (fun x => continuous_iff_continuousAt.2 fun s => (h x s).continuousAt)
    (fun s => (hi s).aestronglyMeasurable)
  have hd : ∀ x s, HasDerivAt (fun r => N.indicator (F r) x) (N.indicator (F' s) x) s := by
    intro x s
    by_cases hx : x ∈ N
    · simpa only [indicator_of_mem hx] using h x s
    · simpa only [indicator_of_notMem hx] using hasDerivAt_const s (0 : ℂ)
  have hm' := stronglyMeasurable_uncurry_of_hasDerivAt _ (fun s x => N.indicator (F' s) x) hd hNm
  obtain ⟨S, hS, hS0, hSf⟩ :=
    ((hi b).sub (hi a)).aefinStronglyMeasurable.exists_set_sigmaFinite
  have e1 : ∫⁻ x, ‖F b x - F a x‖ₑ ∂μ = ∫⁻ x in S, ‖F b x - F a x‖ₑ ∂μ := by
    rw [← lintegral_add_compl _ hS]
    have : ∫⁻ x in Sᶜ, ‖F b x - F a x‖ₑ ∂μ = 0 := by
      rw [← lintegral_zero]
      refine lintegral_congr_ae ?_
      filter_upwards [hS0] with x hx
      simp only [Pi.sub_apply, Pi.zero_apply] at hx
      simp [hx]
    rw [this, add_zero]
  rw [e1]
  calc ∫⁻ x in S, ‖F b x - F a x‖ₑ ∂μ
      ≤ ∫⁻ x in S, (∫⁻ r in Ioc a b, ‖N.indicator (F' r) x‖ₑ) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hN] with x hx
        simpa only [indicator_of_mem hx] using
          enorm_sub_le_lintegral_of_hasDerivAt_complex _ _ (h x) hab
    _ = ∫⁻ r in Ioc a b, (∫⁻ x in S, ‖N.indicator (F' r) x‖ₑ ∂μ) := by
        symm
        exact lintegral_lintegral_swap (f := fun r x => ‖N.indicator (F' r) x‖ₑ)
          hm'.enorm.aemeasurable
    _ ≤ ∫⁻ _ in Ioc a b, C := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
        refine le_trans ?_ (hC r (Ioc_subset_Icc_self hr))
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun x => ?_)
        by_cases hx : x ∈ N
        · simp [indicator_of_mem hx]
        · simp [indicator_of_notMem hx]
    _ = C * ENNReal.ofReal (b - a) := by simp

theorem integral_norm_sub_le_of_hasDerivAt {α : Type} [MeasurableSpace α] (μ : Measure α)
    (F F' : ℝ → α → ℂ) (h : ∀ x s, HasDerivAt (fun r => F r x) (F' s x) s)
    (hi : ∀ s, Integrable (F s) μ) (hi' : ∀ s, Integrable (F' s) μ) (a b C : ℝ)
    (hC : ∀ s ∈ uIcc a b, ∫ x, ‖F' s x‖ ∂μ ≤ C) :
    ∫ x, ‖F b x - F a x‖ ∂μ ≤ C * |b - a| := by
  wlog hab : a ≤ b generalizing a b
  · have := this b a (by rwa [uIcc_comm]) (le_of_not_ge hab)
    rw [abs_sub_comm]
    simpa only [norm_sub_rev (F b _)] using this
  have hC0 : 0 ≤ C := le_trans (integral_nonneg fun x => norm_nonneg _) (hC a left_mem_uIcc)
  have := lintegral_enorm_sub_le_of_hasDerivAt_of_le μ F F' h hi hab (ENNReal.ofReal C)
    (fun s hs => by
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hi' s)]
      exact ENNReal.ofReal_le_ofReal (hC s (by rwa [uIcc_of_le hab])))
  rw [← ofReal_integral_norm_eq_lintegral_enorm (f := fun x => F b x - F a x) ((hi b).sub (hi a)),
    ← ENNReal.ofReal_mul hC0] at this
  rw [abs_of_nonneg (sub_nonneg.2 hab)]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (sub_nonneg.2 hab))).1 this

theorem hasDerivAt_integral_of_integral_bounds {α : Type} [MeasurableSpace α] (μ : Measure α)
    (F F₁ F₂ : ℝ → α → ℂ) (B : ℝ)
    (h1 : ∀ x s, HasDerivAt (fun r => F r x) (F₁ s x) s)
    (h2 : ∀ x s, HasDerivAt (fun r => F₁ r x) (F₂ s x) s)
    (i0 : ∀ s, Integrable (F s) μ) (i1 : ∀ s, Integrable (F₁ s) μ)
    (i2 : ∀ s, Integrable (F₂ s) μ)
    (_b1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ x, ‖F₁ s x‖ ∂μ ≤ B)
    (b2 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ x, ‖F₂ s x‖ ∂μ ≤ B) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F₁ 0 x ∂μ) 0 := by
  have hB : 0 ≤ B := le_trans (integral_nonneg fun x => norm_nonneg _) (b2 0 (by simp))
  have hsub : ∀ t ∈ Icc (-1 : ℝ) 1, uIcc 0 t ⊆ Icc (-1 : ℝ) 1 := fun t ht =>
    uIcc_subset_Icc (by simp) ht
  have A : ∀ s ∈ Icc (-1 : ℝ) 1, ∫ x, ‖F₁ s x - F₁ 0 x‖ ∂μ ≤ B * |s| := fun s hs => by
    simpa using integral_norm_sub_le_of_hasDerivAt μ F₁ F₂ h2 i1 i2 0 s B
      fun r hr => b2 r (hsub s hs hr)
  have Bd : ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖(∫ x, F t x ∂μ) - (∫ x, F 0 x ∂μ) - t • ∫ x, F₁ 0 x ∂μ‖ ≤ B * |t| * |t| := by
    intro t ht
    have := integral_norm_sub_le_of_hasDerivAt μ (fun s x => F s x - s • F₁ 0 x)
      (fun s x => F₁ s x - F₁ 0 x)
      (fun x s => by simpa using (h1 x s).fun_sub ((hasDerivAt_id' s).smul_const (F₁ 0 x)))
      (fun s => (i0 s).sub ((i1 0).smul s)) (fun s => (i1 s).sub (i1 0)) 0 t (B * |t|)
      (fun r hr => (A r (hsub t ht hr)).trans (mul_le_mul_of_nonneg_left
        (by simpa using abs_sub_left_of_mem_uIcc hr) hB))
    rw [← integral_smul, ← integral_sub (i0 t) (i0 0),
      ← integral_sub (f := fun x => F t x - F 0 x) (g := fun x => t • F₁ 0 x)
        ((i0 t).sub (i0 0)) ((i1 0).smul t)]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [sub_zero] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    funext x
    congr 1
    rw [zero_smul]
    ring
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun t : ℝ => t ^ 2) ?_
    (Asymptotics.isLittleO_pow_id (by norm_num))
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
    with t ht
  refine (Bd t ht).trans (le_of_eq ?_)
  rw [norm_pow, Real.norm_eq_abs]
  ring

end GlobalTheory

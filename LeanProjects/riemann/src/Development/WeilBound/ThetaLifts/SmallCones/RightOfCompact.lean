import Mathlib

open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise

namespace PositivityTheory.ThKCT.Unf

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem right_of_compact [CompactSpace G] (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have h := congrArg (fun m : Measure G => m univ) e
  simp only [Measure.smul_apply] at h
  rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, preimage_univ, ENNReal.smul_def, smul_eq_mul] at h
  have h1 : (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj (isOpen_univ.measure_ne_zero μ univ_nonempty) (measure_ne_top μ _)).1 (by rw [← h, one_mul])
  rw [e, ENNReal.coe_eq_one.1 h1, one_smul]

variable (ν : Measure G) [ν.IsHaarMeasure] (m : Measure G) [SFinite m] {P : Set G} {K : Subgroup G}

omit [T2Space G] in
theorem conv_eq (hP : ∀ p ∈ P, m.map (p * ·) = m) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) {f b : G → ℝ≥0∞}
    (hf : Measurable f) (hb : Measurable b) (hbK : ∀ g, ∀ k ∈ K, b (g * k) = b g) :
    ∫⁻ g, b g * ∫⁻ x, f (x * g) ∂m ∂ν = (∫⁻ x, b x⁻¹ ∂m) * ∫⁻ g, f g ∂ν := by
  have c : ∀ g, ∫⁻ x, b (x⁻¹ * g) ∂m = ∫⁻ x, b x⁻¹ ∂m := fun g => by
    obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
    conv_lhs => rw [← hP p hp]
    rw [lintegral_map (by fun_prop) (measurable_const_mul p)]
    simp [mul_assoc, hbK _ k hk]
  calc _ = ∫⁻ g, ∫⁻ x, b g * f (x * g) ∂m ∂ν := by
        refine lintegral_congr fun g => (lintegral_const_mul _ (by fun_prop)).symm
    _ = ∫⁻ x, ∫⁻ g, b g * f (x * g) ∂ν ∂m := lintegral_lintegral_swap (Measurable.aemeasurable (by fun_prop))
    _ = ∫⁻ x, ∫⁻ g, b (x⁻¹ * g) * f g ∂ν ∂m := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_mul_left_eq_self _ x⁻¹]
        simp
    _ = ∫⁻ g, ∫⁻ x, b (x⁻¹ * g) * f g ∂m ∂ν := (lintegral_lintegral_swap (Measurable.aemeasurable (by fun_prop))).symm
    _ = _ := by
        rw [← lintegral_const_mul _ hf]
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (by fun_prop), c]

omit [SFinite m] in
theorem cont_M [IsFiniteMeasureOnCompacts m] {f : G → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) (h0 : 0 ≤ f) :
    Continuous fun g => ∫⁻ x, ENNReal.ofReal (f (x * g)) ∂m := by
  haveI : IsFiniteMeasureOnCompacts m.inv := ⟨fun C hC => by
    rw [Measure.inv_apply]; exact hC.inv.measure_lt_top⟩
  have h1 := continuous_integral_apply_inv_mul (μ := m.inv) hf hs
  have e : ∀ g, ∫⁻ x, ENNReal.ofReal (f (x * g)) ∂m = ENNReal.ofReal (∫ y, f (y⁻¹ * g) ∂m.inv) := fun g => by
    rw [Measure.inv, integral_map measurable_inv.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp only [inv_inv]
    exact (ofReal_integral_eq_lintegral_ofReal (f := fun x => f (x * g)) (Continuous.integrable_of_hasCompactSupport
      (by fun_prop) (hs.comp_homeomorph (Homeomorph.mulRight g))) (ae_of_all _ fun x => h0 (x * g))).symm
  simp only [e]
  exact ENNReal.continuous_ofReal.comp h1

theorem cross_le [IsFiniteMeasureOnCompacts m] (hP : ∀ p ∈ P, m.map (p * ·) = m) (hK : ∀ k ∈ K, m.map (· * k) = m)
    (hKc : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) {f f₀ : G → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) (h0 : 0 ≤ f) (hf₀ : Continuous f₀) (hs₀ : HasCompactSupport f₀) (h0₀ : 0 ≤ f₀) :
    (∫⁻ g, ENNReal.ofReal (f g) ∂ν) * ∫⁻ g, ENNReal.ofReal (f₀ g) ∂m ≤
      (∫⁻ g, ENNReal.ofReal (f₀ g) ∂ν) * ∫⁻ g, ENNReal.ofReal (f g) ∂m := by
  by_contra hlt
  rw [not_le] at hlt
  have fin : ∀ {φ : G → ℝ}, Continuous φ → HasCompactSupport φ → ∫⁻ g, ENNReal.ofReal (φ g) ∂ν ≠ ⊤ := fun h1 h2 =>
    (h1.integrable_of_hasCompactSupport h2).lintegral_lt_top.ne
  set A := ∫⁻ g, ENNReal.ofReal (f₀ g) ∂ν with hA
  set B := ∫⁻ g, ENNReal.ofReal (f g) ∂ν with hB
  let u : G → ℝ≥0∞ := fun g => A * ∫⁻ x, ENNReal.ofReal (f (x * g)) ∂m
  let v : G → ℝ≥0∞ := fun g => B * ∫⁻ x, ENNReal.ofReal (f₀ (x * g)) ∂m
  have hu : Continuous u := (ENNReal.continuous_const_mul (fin hf₀ hs₀)).comp (cont_M m hf hs h0)
  have hv : Continuous v := (ENNReal.continuous_const_mul (fin hf hs)).comp (cont_M m hf₀ hs₀ h0₀)
  have inv : ∀ {φ : G → ℝ}, Continuous φ → ∀ k ∈ K, ∫⁻ x, ENNReal.ofReal (φ (x * k)) ∂m = ∫⁻ x, ENNReal.ofReal (φ x) ∂m :=
    fun h1 k hk => by
      conv_rhs => rw [← hK k hk]
      rw [lintegral_map (by fun_prop) (measurable_mul_const k)]
  obtain ⟨V, hV, hVK⟩ := compact_open_separated_mul_left hKc (isOpen_lt hu hv) fun k hk => by
    simpa only [u, v, mem_setOf_eq, inv hf k hk, inv hf₀ k hk] using hlt
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  set W := interior (V ∩ C) * (K : Set G) with hW
  have hWo : IsOpen W := isOpen_interior.mul_right
  have hWK : ∀ g, ∀ k ∈ K, g * k ∈ W ↔ g ∈ W := fun g k hk => by
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), by simp only at e ⊢; rw [← mul_assoc, e, mul_inv_cancel_right]⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, (mul_assoc _ _ _).symm⟩
  have hb : Measurable (W.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hWo.measurableSet
  have hbK : ∀ g, ∀ k ∈ K, W.indicator (1 : G → ℝ≥0∞) (g * k) = W.indicator 1 g := fun g k hk => by
    by_cases h : g ∈ W <;> simp [h, hWK g k hk]
  have key : ∀ {φ : G → ℝ}, Continuous φ → ∫⁻ g in W, ∫⁻ x, ENNReal.ofReal (φ (x * g)) ∂m ∂ν =
      (∫⁻ x, W.indicator 1 x⁻¹ ∂m) * ∫⁻ g, ENNReal.ofReal (φ g) ∂ν := fun {φ} h1 => by
    rw [← conv_eq ν m hP hPK (f := fun g => ENNReal.ofReal (φ g)) (by fun_prop) hb hbK, ← lintegral_indicator hWo.measurableSet]
    refine lintegral_congr fun g => ?_
    by_cases h : g ∈ W <;> simp [h]
  have hfin : ∫⁻ x, W.indicator 1 x⁻¹ ∂m ≠ ⊤ := by
    have : ∫⁻ x, W.indicator 1 x⁻¹ ∂m = m W⁻¹ := by
      rw [← lintegral_indicator_one hWo.inv.measurableSet]; rfl
    rw [this]
    exact ((measure_mono (inv_subset_inv.2 (mul_subset_mul_right (interior_subset.trans inter_subset_right)))).trans_lt
      (hC.mul hKc).inv.measure_lt_top).ne
  have e1 : ∫⁻ g in W, u g ∂ν = A * ((∫⁻ x, W.indicator 1 x⁻¹ ∂m) * B) := by
    rw [lintegral_const_mul _ (cont_M m hf hs h0).measurable, key hf]
  have e2 : ∫⁻ g in W, v g ∂ν = B * ((∫⁻ x, W.indicator 1 x⁻¹ ∂m) * A) := by
    rw [lintegral_const_mul _ (cont_M m hf₀ hs₀ h0₀).measurable, key hf₀]
  have h3 := setLIntegral_strict_mono (μ := ν) (f := u) (g := v) hWo.measurableSet
    (hWo.measure_ne_zero ν ⟨1 * 1, mul_mem_mul (mem_interior_iff_mem_nhds.2 (Filter.inter_mem hV hC1)) K.one_mem⟩)
    hv.measurable (by rw [e1]; exact ENNReal.mul_ne_top (fin hf₀ hs₀) (ENNReal.mul_ne_top hfin (fin hf hs)))
    (ae_of_all _ fun x hx => hVK (mul_subset_mul_right (interior_subset.trans inter_subset_left) hx))
  rw [e1, e2] at h3
  exact h3.ne (by ring)

theorem eq_smul [IsFiniteMeasureOnCompacts m] (hP : ∀ p ∈ P, m.map (p * ·) = m) (hK : ∀ k ∈ K, m.map (· * k) = m)
    (hKc : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ m = c • ν := by
  obtain ⟨⟨f₀, hf₀⟩, hs₀, h0₀, h1⟩ := exists_continuous_nonneg_pos (1 : G)
  have fin : ∀ (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {φ : G → ℝ}, Continuous φ → HasCompactSupport φ →
      ∫⁻ g, ENNReal.ofReal (φ g) ∂μ ≠ ⊤ := fun μ _ _ h1 h2 => (h1.integrable_of_hasCompactSupport h2).lintegral_lt_top.ne
  set A := ∫⁻ g, ENNReal.ofReal (f₀ g) ∂ν with hA
  have hA0 : A ≠ 0 := fun h => by
    have := (lintegral_eq_zero_iff (by fun_prop)).1 h
    have h2 := (Continuous.ae_eq_iff_eq ν (ENNReal.continuous_ofReal.comp hf₀) continuous_zero).1 this
    exact h1 (le_antisymm (ENNReal.ofReal_eq_zero.1 (congrFun h2 1)) (h0₀ 1))
  have hc : (∫⁻ g, ENNReal.ofReal (f₀ g) ∂m) / A ≠ ⊤ := ENNReal.div_ne_top (fin m hf₀ hs₀) hA0
  refine ⟨_, hc, ?_⟩
  lift (∫⁻ g, ENNReal.ofReal (f₀ g) ∂m) / A to ℝ≥0 using hc with c hc'
  rw [← ENNReal.smul_def]
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  have hf : Continuous fun x => (f x : ℝ) := by fun_prop
  have hs : HasCompactSupport fun x => (f x : ℝ) := f.hasCompactSupport.comp_left (g := fun x : ℝ≥0 => (x : ℝ)) rfl
  have h0 : 0 ≤ fun x => (f x : ℝ) := fun x => (f x).2
  have e := le_antisymm (cross_le ν m hP hK hKc hPK hf hs h0 hf₀ hs₀ h0₀) (cross_le ν m hP hK hKc hPK hf₀ hs₀ h0₀ hf hs h0)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable, ENNReal.smul_def, lintegral_smul_measure, hc',
    smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, mul_comm (∫⁻ g, ENNReal.ofReal (f₀ g) ∂m)]
  erw [e]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 (fin ν hf₀ hs₀), one_mul]

end PositivityTheory.ThKCT.Unf

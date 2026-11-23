import Mathlib

open MeasureTheory Set

private lemma integrable_weight {a : ℝ} (ha : -1 < a) {r : ℕ} (hr : a + 1 < r) :
    Integrable fun y : ℝ => ((1 + |y|) ^ r)⁻¹ * |y| ^ a := by
  set f : ℝ → ℝ := fun x => ((1 + x) ^ r)⁻¹ * x ^ a with hf
  have hmeas : Measurable f := by
    rw [hf]; fun_prop
  have h : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
    refine IntegrableOn.union ?_ ?_
    · have h1 : IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 1) := by
        have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) ha
        rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
      refine Integrable.mono' h1 hmeas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
      have hq : ((1 + x) ^ r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
      rw [Real.norm_of_nonneg (by rw [hf]; positivity)]
      calc f x ≤ 1 * x ^ a := mul_le_mul_of_nonneg_right hq hp
        _ = x ^ a := one_mul _
    · have h1 : IntegrableOn (fun x : ℝ => x ^ (a - r)) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
      refine Integrable.mono' h1 hmeas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1 : ℝ) < x := hx
      have hx0 : 0 < x := lt_trans one_pos hx1
      have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
      have hq : ((1 + x) ^ r)⁻¹ ≤ (x ^ r)⁻¹ := by
        gcongr
        linarith
      rw [Real.norm_of_nonneg (by rw [hf]; positivity), Real.rpow_sub hx0, Real.rpow_natCast,
        div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right hq hp
  have hG : Integrable ((Ioi (0 : ℝ)).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioi).2 h
  have hsum := hG.add hG.comp_neg
  refine hsum.congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with y hy
  have hy0 : y ≠ 0 := hy
  rcases lt_or_gt_of_ne hy0 with h0 | h0
  · have h1 : y ∉ Ioi (0 : ℝ) := by simp [h0.le]
    have h2 : -y ∈ Ioi (0 : ℝ) := by simpa using h0
    simp only [Pi.add_apply, indicator_of_notMem h1, indicator_of_mem h2, zero_add, abs_of_neg h0,
      hf]
  · have h1 : y ∈ Ioi (0 : ℝ) := h0
    have h2 : -y ∉ Ioi (0 : ℝ) := by simp [h0.le]
    simp only [Pi.add_apply, indicator_of_mem h1, indicator_of_notMem h2, add_zero, abs_of_pos h0,
      hf]

private lemma continuousOn_weight (k : ℕ) (z : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ z) ({0}ᶜ : Set ℝ) := by
  refine ContinuousOn.mul (by fun_prop) ?_
  intro y hy
  have hy0 : 0 < |y| := abs_pos.2 hy
  have h1 : ((|y| : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hy0
  have h2 : ContinuousAt (fun y : ℝ => ((|y| : ℝ) : ℂ)) y := by fun_prop
  exact (ContinuousAt.comp (f := fun y : ℝ => ((|y| : ℝ) : ℂ)) (g := fun w : ℂ => w ^ z)
    (continuousAt_cpow_const h1) h2).continuousWithinAt

theorem UpperTheory.integrable_and_continuous_mellinIntegral_of_rapidDecay :
    ∀ (W : ℝ → ℝ → ℂ) (c : ℝ → ℂ) (k : ℕ) (s : ℂ),
        ContinuousOn (fun p : ℝ × ℝ => W p.1 p.2) (({0}ᶜ : Set ℝ) ×ˢ Set.univ) →
        ContinuousOn c ({0}ᶜ : Set ℝ) → (∀ y, ‖c y‖ = 1) →
        (∀ r : ℕ, ∃ B : ℝ, ∀ y t, y ≠ 0 → ‖W y t‖ ≤ B * ((1 + |y|) ^ r)⁻¹) →
        1 - (k : ℝ) < s.re →
        (∀ t, MeasureTheory.Integrable fun y : ℝ => W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) ∧
        Continuous fun t => ∫ y : ℝ, W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2) := by
  intro W c k s hW hc hc1 hdec hs
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = k + s.re - 2 := ⟨_, rfl⟩
  have ha : -1 < a := by rw [hadef]; linarith
  obtain ⟨r, hr⟩ := exists_nat_gt (a + 1)
  obtain ⟨B, hB⟩ := hdec r
  have hae : ∀ᵐ y : ℝ, y ∈ ({0}ᶜ : Set ℝ) := compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))
  have hint : Integrable fun y : ℝ => |B| * (((1 + |y|) ^ r)⁻¹ * |y| ^ a) :=
    (integrable_weight ha hr).const_mul _
  have hnorm : ∀ t, ∀ᵐ y : ℝ,
      ‖W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)‖
        ≤ |B| * (((1 + |y|) ^ r)⁻¹ * |y| ^ a) := by
    intro t
    filter_upwards [hae] with y hy
    have hy0 : 0 < |y| := abs_pos.2 hy
    have hw : ‖(y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)‖ = |y| ^ a := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hy0, hadef, ← Real.rpow_natCast,
        ← Real.rpow_add hy0]
      congr 1
      simp only [Complex.sub_re, Complex.re_ofNat]
      ring
    have hp : 0 ≤ |y| ^ a := Real.rpow_nonneg hy0.le _
    have hinv : 0 ≤ ((1 + |y|) ^ r)⁻¹ := by positivity
    rw [mul_assoc, norm_mul, norm_mul, hc1, mul_one, hw]
    calc ‖W y t‖ * |y| ^ a ≤ (B * ((1 + |y|) ^ r)⁻¹) * |y| ^ a :=
          mul_le_mul_of_nonneg_right (hB y t hy) hp
      _ ≤ (|B| * ((1 + |y|) ^ r)⁻¹) * |y| ^ a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) hinv) hp
      _ = |B| * (((1 + |y|) ^ r)⁻¹ * |y| ^ a) := by ring
  have hmeas : ∀ t, AEStronglyMeasurable
      (fun y : ℝ => W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) volume := by
    intro t
    have h1 : ContinuousOn (fun y : ℝ => W y t) ({0}ᶜ : Set ℝ) :=
      ContinuousOn.comp (g := fun p : ℝ × ℝ => W p.1 p.2) (f := fun y : ℝ => (y, t)) hW
        (by fun_prop) (fun y hy => ⟨hy, trivial⟩)
    have h2 : ContinuousOn
        (fun y : ℝ => W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) ({0}ᶜ : Set ℝ) := by
      refine ((h1.mul hc).mul (continuousOn_weight k (s - 2))).congr ?_
      intro y _
      simp only [Pi.mul_apply, mul_assoc]
    have h3 := h2.aestronglyMeasurable (μ := volume) isOpen_compl_singleton.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h3
  refine ⟨fun t => Integrable.mono' hint (hmeas t) (hnorm t), ?_⟩
  refine continuous_of_dominated hmeas hnorm hint ?_
  filter_upwards [hae] with y hy
  have h1 : Continuous fun t : ℝ => W y t :=
    hW.comp_continuous (f := fun t : ℝ => (y, t)) (by fun_prop) (fun t => ⟨hy, trivial⟩)
  exact ((h1.mul continuous_const).mul continuous_const).mul continuous_const

import Mathlib
open MeasureTheory

namespace GlobalTheory.FoldIntegral

theorem integral_integral_eq_pos_sub_neg {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (h : Y × Z → ℝ) (hh : Measurable h)
    (hfin : ∫⁻ y, ∫⁻ s, ‖h (y, s)‖ₑ ∂m ∂ν < ⊤) :
    ∫ y, ∫ s, h (y, s) ∂m ∂ν =
      (∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν).toReal -
        (∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν).toReal := by
  have hN : Measurable fun y => ∫⁻ s, ‖h (y, s)‖ₑ ∂m := hh.enorm.lintegral_prod_right'
  have hp : Measurable fun y => ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m :=
    hh.ennreal_ofReal.lintegral_prod_right'
  have hn : Measurable fun y => ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m :=
    hh.neg.ennreal_ofReal.lintegral_prod_right'
  have bp : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => Real.ofReal_le_enorm _) hfin
  have bn : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s =>
      (Real.ofReal_le_enorm _).trans (enorm_neg _).le) hfin
  rw [← integral_toReal hp.aemeasurable (ae_lt_top hp bp.ne),
    ← integral_toReal hn.aemeasurable (ae_lt_top hn bn.ne),
    ← integral_sub (integrable_toReal_of_lintegral_ne_top hp.aemeasurable bp.ne)
      (integrable_toReal_of_lintegral_ne_top hn.aemeasurable bn.ne)]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    ⟨(hh.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩

theorem clm_integral_integral {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (H : Y × Z → ℂ) (hH : Measurable H)
    (hfin : ∫⁻ y, ∫⁻ s, ‖H (y, s)‖ₑ ∂m ∂ν < ⊤) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, ∫ s, H (y, s) ∂m ∂ν) = ∫ y, ∫ s, L (H (y, s)) ∂m ∂ν := by
  have hN : Measurable fun y => ∫⁻ s, ‖H (y, s)‖ₑ ∂m := hH.enorm.lintegral_prod_right'
  have hI : Integrable (fun y => ∫ s, H (y, s) ∂m) ν :=
    ⟨hH.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
      lt_of_le_of_lt (lintegral_mono fun y => enorm_integral_le_lintegral_enorm _) hfin⟩
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact (L.integral_comp_comm
    ⟨(hH.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩).symm

theorem fold : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  intro α Y Z _ _ _ μ Fs ν m S hS Φ hΦ c hc P hQ G hG hP hfin
  haveI : IsFiniteMeasure (m.restrict S) := ⟨by simpa using hS⟩
  have hint : IntegrableOn G Fs μ := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hQ _ hG.enorm (hP (fun z => ‖z‖ₑ) (by simp))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨hint, ?_⟩
  have hH : Measurable fun p : Y × Z => G (Φ p.1 p.2) := hG.comp hΦ
  have key : ∀ L : ℂ →L[ℝ] ℝ, (∀ z, ‖L z‖ ≤ ‖z‖) →
      L (∫ x in Fs, G x ∂μ) = c * L (∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν) := by
    intro L hL
    have hLm : Measurable L := L.continuous.measurable
    have h1 := clm_integral_integral ν (m.restrict S) _ hH hfin L
    have h2 := integral_integral_eq_pos_sub_neg ν (m.restrict S)
      (fun p : Y × Z => L (G (Φ p.1 p.2))) (hLm.comp hH)
      (lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hL _)) hfin)
    have h3 := hQ (fun x => ENNReal.ofReal (L (G x))) (hLm.comp hG).ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (L z)) (by simp))
    have h4 := hQ (fun x => ENNReal.ofReal (-L (G x))) (hLm.comp hG).neg.ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (-L z)) (by simp))
    simp only at h1 h2
    rw [h1, h2, ← L.integral_comp_comm hint,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp hint), h3, h4,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, mul_sub]
  apply Complex.ext
  · have := key Complex.reCLM (fun z => by simpa using Complex.abs_re_le_norm z)
    simpa using this
  · have := key Complex.imCLM (fun z => by simpa using Complex.abs_im_le_norm z)
    simpa using this

end GlobalTheory.FoldIntegral

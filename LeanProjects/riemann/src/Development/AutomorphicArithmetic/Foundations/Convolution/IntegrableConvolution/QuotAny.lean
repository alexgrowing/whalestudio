import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.L1

section QuotAnyAux

variable {X T : Type} [Group X] [MeasurableSpace X] [MeasurableMul₂ X] [Group T] [MeasurableSpace T]
  [MeasurableInv T]

private theorem lint_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {F : X → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ t x, F (i t * x) = F x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) :
    ∫⁻ x, F x * ρ x ∂μ = ∫⁻ x, F x * ρ' x ∂μ := by
  have hmul : Measurable fun p : T × X => i p.1 * p.2 := (hi.comp measurable_fst).mul measurable_snd
  have e1 : ∫⁻ x, F x * ρ x ∂μ = ∫⁻ t, ∫⁻ x, F x * ρ x * ρ' (i t * x) ∂μ ∂ν := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun x => ?_
      rw [lintegral_const_mul, hρ'1 x, mul_one]
      exact hρ'.comp (hi.mul_const x)
    · exact (((hF.comp measurable_snd).mul (hρ.comp measurable_snd)).mul (hρ'.comp hmul)).aemeasurable
  have e2 : ∀ t : T, ∫⁻ x, F x * ρ x * ρ' (i t * x) ∂μ = ∫⁻ x, F x * ρ' x * ρ (i t⁻¹ * x) ∂μ := by
    intro t
    rw [← lintegral_mul_left_eq_self (fun x => F x * ρ x * ρ' (i t * x)) (i t)⁻¹]
    refine lintegral_congr fun x => ?_
    simp only [mul_inv_cancel_left]
    rw [← map_inv, hFi]
    ring
  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun x => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun t : T => ρ (i t * x)), hρ1 x, mul_one]
    · exact hρ.comp ((hi.comp measurable_inv).mul_const x)

  · have hm : Measurable fun p : X × T => i p.2⁻¹ * p.1 :=
      (hi.comp (measurable_snd.inv)).mul measurable_fst
    exact (((hF.comp measurable_fst).mul (hρ'.comp measurable_fst)).mul (hρ.comp hm)).aemeasurable

end QuotAnyAux

section QuotAnyReal

variable {X : Type} [MeasurableSpace X]

private theorem nn_int {μ : Measure X} {g : X → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x)
    {ρ : X → ℝ≥0∞} (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, g x * (ρ x).toReal ∂μ = (∫⁻ x, ‖g x‖ₑ * ρ x ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => mul_nonneg (h0 x) ENNReal.toReal_nonneg)
    (hg.mul hρ.ennreal_toReal).aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  have hae := ae_lt_top (hg.enorm.mul hρ) hfin.ne
  filter_upwards [hae] with x hx
  rw [ENNReal.ofReal_mul (h0 x), ← Real.enorm_of_nonneg (h0 x)]
  by_cases h : ρ x = ⊤
  · have hz : ‖g x‖ₑ = 0 := by
      by_contra hne
      simp only [Pi.mul_apply] at hx
      rw [h, ENNReal.mul_top hne] at hx
      exact lt_irrefl _ hx
    simp [hz]
  · rw [ENNReal.ofReal_toReal h]

private theorem int_of {μ : Measure X} {g : X → ℝ} (hg : Measurable g) {ρ : X → ℝ≥0∞}
    (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    Integrable (fun x => g x * (ρ x).toReal) μ := by
  refine ⟨(hg.mul hρ.ennreal_toReal).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  rw [enorm_mul, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  gcongr
  exact ENNReal.ofReal_toReal_le

end QuotAnyReal

section QuotAnyMain

variable {X T : Type} [Group X] [MeasurableSpace X] [MeasurableMul₂ X] [Group T] [MeasurableSpace T]
  [MeasurableInv T]

private theorem real_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {g : X → ℝ} (hg : Measurable g)
    (hgi : ∀ t x, g (i t * x) = g x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, g x * (ρ x).toReal ∂μ = ∫ x, g x * (ρ' x).toReal ∂μ := by
  have hpm : Measurable fun x => max (g x) 0 := hg.max measurable_const
  have hnm : Measurable fun x => max (-g x) 0 := hg.neg.max measurable_const
  have hpi : ∀ t x, max (g (i t * x)) 0 = max (g x) 0 := fun t x => by rw [hgi]
  have hni : ∀ t x, max (-g (i t * x)) 0 = max (-g x) 0 := fun t x => by rw [hgi]
  have hple : ∀ x, ‖max (g x) 0‖ₑ ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hnle : ∀ x, ‖max (-g x) 0‖ₑ ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _))
  have hfin' : ∫⁻ x, ‖g x‖ₑ * ρ' x ∂μ < ⊤ := by
    rw [← lint_eq hi hg.enorm (fun t x => by rw [hgi]) hρ hρ1 hρ' hρ'1]
    exact hfin
  have split : ∀ r : X → ℝ≥0∞, Measurable r → ∫⁻ x, ‖g x‖ₑ * r x ∂μ < ⊤ →
      ∫ x, g x * (r x).toReal ∂μ =
        (∫⁻ x, ‖max (g x) 0‖ₑ * r x ∂μ).toReal - (∫⁻ x, ‖max (-g x) 0‖ₑ * r x ∂μ).toReal := by
    intro r hr hf
    have fp : ∫⁻ x, ‖max (g x) 0‖ₑ * r x ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun x => by gcongr; exact hple x) hf
    have fn : ∫⁻ x, ‖max (-g x) 0‖ₑ * r x ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun x => by gcongr; exact hnle x) hf
    rw [← nn_int hpm (fun x => le_max_right _ _) hr fp, ← nn_int hnm (fun x => le_max_right _ _) hr fn,
      ← integral_sub (int_of hpm hr fp) (int_of hnm hr fn)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show g x * (r x).toReal = max (g x) 0 * (r x).toReal - max (-g x) 0 * (r x).toReal
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  rw [split ρ hρ hfin, split ρ' hρ' hfin',
    lint_eq hi hpm.enorm (fun t x => by rw [hpi]) hρ hρ1 hρ' hρ'1,
    lint_eq hi hnm.enorm (fun t x => by rw [hni]) hρ hρ1 hρ' hρ'1]

private theorem cpx_int {μ : Measure X} {Φ : X → ℂ} (hΦ : Measurable Φ) {ρ : X → ℝ≥0∞}
    (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) :
    Integrable (fun x => Φ x * ((ρ x).toReal : ℂ)) μ := by
  have h := int_of (μ := μ) (g := fun x => ‖Φ x‖) hΦ.norm hρ (by simpa [enorm_norm] using hfin)
  refine h.mono (hΦ.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp [abs_of_nonneg ENNReal.toReal_nonneg]

private theorem cpx_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {Φ : X → ℂ} (hΦ : Measurable Φ)
    (hΦi : ∀ t x, Φ (i t * x) = Φ x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) (hfin : ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, Φ x * ((ρ x).toReal : ℂ) ∂μ = ∫ x, Φ x * ((ρ' x).toReal : ℂ) ∂μ := by
  have hfin' : ∫⁻ x, ‖Φ x‖ₑ * ρ' x ∂μ < ⊤ := by
    rw [← lint_eq hi hΦ.enorm (fun t x => by rw [hΦi]) hρ hρ1 hρ' hρ'1]
    exact hfin
  have h1 := cpx_int hΦ hρ hfin
  have h2 := cpx_int hΦ hρ' hfin'
  have bre : ∫⁻ x, ‖(Φ x).re‖ₑ * ρ x ∂μ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun x => by
      gcongr
      exact enorm_le_iff_norm_le.2 (Complex.abs_re_le_norm _)) hfin
  have bim : ∫⁻ x, ‖(Φ x).im‖ₑ * ρ x ∂μ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun x => by
      gcongr
      exact enorm_le_iff_norm_le.2 (Complex.abs_im_le_norm _)) hfin
  apply Complex.ext
  · have a := Complex.reCLM.integral_comp_comm h1
    have b := Complex.reCLM.integral_comp_comm h2
    simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at a b
    rw [← a, ← b]
    exact real_eq hi (Complex.measurable_re.comp hΦ) (fun t x => by simp [hΦi]) hρ hρ1 hρ' hρ'1 bre
  · have a := Complex.imCLM.integral_comp_comm h1
    have b := Complex.imCLM.integral_comp_comm h2
    simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at a b
    rw [← a, ← b]
    exact real_eq hi (Complex.measurable_im.comp hΦ) (fun t x => by simp [hΦi]) hρ hρ1 hρ' hρ'1 bim

end QuotAnyMain

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.quotAny :
    UpperTheory.ConvolutionTheory.L1.QuotAny := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi Φ ρ hΦ hinv hρ hfin
  have hex : ∃ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id i ν ρ := ⟨ρ, hρ⟩
  rw [PositivityTheory.Rg.Tf.Geo.quotInt, dif_pos hex]
  have hc := hex.choose_spec
  exact (UpperTheory.ConvolutionTheory.L1.cpx_eq hi hΦ hinv hρ.1 hρ.2 hc.1 hc.2 hfin).symm

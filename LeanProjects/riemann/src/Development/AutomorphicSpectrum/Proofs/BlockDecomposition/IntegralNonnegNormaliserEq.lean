import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotNorm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
  {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]

theorem ae_lt_top_of_normaliser {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  set E : Set G := {g | ρ g = ∞} with hEdef
  have hE : MeasurableSet E := hρ.1 (measurableSet_singleton ∞)
  have hind : Measurable (E.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hE
  have hzero : ∀ g : G, ∫⁻ h : H, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μH = 0 := by
    intro g
    have hm : Measurable fun h : H => ρ ((h : G) * g) :=
      hρ.1.comp (measurable_subtype_coe.mul_const g)
    have hfin : ∀ᵐ h : H ∂μH, ρ ((h : G) * g) < ∞ :=
      ae_lt_top hm (by rw [hρ.2 g]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hfin] with h hh
    simp [hEdef, Set.indicator, hh.ne]
  have key : ∫⁻ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG ∂μH = 0 := by
    rw [lintegral_lintegral_swap]
    · simp [hzero]
    · exact (hind.comp hmulH).aemeasurable
  have h2 : ∀ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG = μG E := fun h => by
    rw [lintegral_mul_left_eq_self (E.indicator (1 : G → ℝ≥0∞)) (h : G),
      lintegral_indicator_one hE]
  simp only [h2, lintegral_const] at key
  have hne : μH Set.univ ≠ 0 := by
    intro h0
    have h1 := hρ.2 1
    rw [Measure.measure_univ_eq_zero.1 h0] at h1
    simp at h1
  have hE0 : μG E = 0 := (mul_eq_zero.1 key).resolve_right hne
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE0] with g hg
  exact lt_top_iff_ne_top.2 hg

theorem integral_nonneg_normaliser_eq {f : G → ℝ} (hf : Measurable f) (hf0 : ∀ g, 0 ≤ f g)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫ g, f g * (σ g).toReal ∂μG = (∫⁻ g, ENNReal.ofReal (f g) * σ g ∂μG).toReal := by
    intro σ hσ
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun g => mul_nonneg (hf0 g) ENNReal.toReal_nonneg)
      (hf.mul hσ.1.ennreal_toReal).aestronglyMeasurable]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [ENNReal.ofReal_mul (hf0 g), ENNReal.ofReal_toReal hg.ne]
  rw [aux hρ, aux hρ', lintegral_normaliser_eq (F := fun g => ENNReal.ofReal (f g))
    hf.ennreal_ofReal (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integrable_normaliser_iff {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG ↔
      Integrable (fun g => F g * ((ρ' g).toReal : ℂ)) μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫⁻ g, ‖F g * ((σ g).toReal : ℂ)‖ₑ ∂μG = ∫⁻ g, ‖F g‖ₑ * σ g ∂μG := by
    intro σ hσ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((σ g).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hg.ne]
  have hm : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      AEStronglyMeasurable (fun g => F g * ((σ g).toReal : ℂ)) μG := fun hσ =>
    (hF.mul (Complex.measurable_ofReal.comp hσ.1.ennreal_toReal)).aestronglyMeasurable
  have heq := lintegral_normaliser_eq (μG := μG) (F := fun g => ‖F g‖ₑ) hF.enorm
    (fun h hh g => by simp only [hFH h hh g]) hρ hρ'
  simp only [Integrable, hm hρ, hm hρ', true_and, hasFiniteIntegral_iff_enorm, aux hρ, aux hρ', heq]

theorem integral_real_normaliser_eq {f : G → ℝ} (hf : Measurable f)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ')
    (hi : Integrable (fun g => f g * (ρ g).toReal) μG)
    (hi' : Integrable (fun g => f g * (ρ' g).toReal) μG) :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have part : ∀ {σ : G → ℝ≥0∞} {u : G → ℝ}, IsQuotNormaliser H μH σ → Measurable u →
      (∀ g, |u g| ≤ |f g|) → Integrable (fun g => f g * (σ g).toReal) μG →
      Integrable (fun g => u g * (σ g).toReal) μG := by
    intro σ u hσ hu hle h
    refine h.mono (hu.mul hσ.1.ennreal_toReal).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle g) (abs_nonneg _)
  have hp : Measurable fun g => max (f g) 0 := hf.max measurable_const
  have hn : Measurable fun g => max (-f g) 0 := hf.neg.max measurable_const
  have hpl : ∀ g, |max (f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnl : ∀ g, |max (-f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have dec : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      Integrable (fun g => f g * (σ g).toReal) μG →
      ∫ g, f g * (σ g).toReal ∂μG =
        ∫ g, max (f g) 0 * (σ g).toReal ∂μG - ∫ g, max (-f g) 0 * (σ g).toReal ∂μG := by
    intro σ hσ h
    rw [← integral_sub (part hσ hp hpl h) (part hσ hn hnl h)]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have : f g = max (f g) 0 - max (-f g) 0 := (max_zero_sub_max_neg_zero_eq_self (f g)).symm
    simp only
    rw [← sub_mul, ← this]
  rw [dec hρ hi, dec hρ' hi',
    integral_nonneg_normaliser_eq hp (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ',
    integral_nonneg_normaliser_eq hn (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integral_normaliser_eq_of {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μG := by
  have hiff := integrable_normaliser_iff (μG := μG) hF hFH hρ hρ'
  by_cases hi : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG
  · have hi' := hiff.1 hi
    have ere : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).re * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.reCLM.integrable_comp h
      have h2 := Complex.reCLM.integral_comp_comm h
      simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    have eim : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).im * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).im = ∫ g, (F g).im * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.imCLM.integrable_comp h
      have h2 := Complex.imCLM.integral_comp_comm h
      simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    apply Complex.ext
    · rw [(ere hi).2, (ere hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_re.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (ere hi).1 (ere hi').1
    · rw [(eim hi).2, (eim hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_im.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (eim hi).1 (eim hi').1
  · rw [integral_undef hi, integral_undef (fun h => hi (hiff.2 h))]

theorem quotIntegral_eq {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotIntegral μG H μH F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG := by
  have hex : ∃ ρ, IsQuotNormaliser H μH ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dif_pos hex]
  exact integral_normaliser_eq_of hF hFH hex.choose_spec hρ

theorem integral_normaliser_eq : PositivityTheory.Rg.BcB.D4.NormEq := by
  intro G _ _ _ _ _ _ _ μ _ H μH _ _ F ρ₁ ρ₂ hF hFH hρ₁ hρ₂
  exact integral_normaliser_eq_of (μG := μ) hF hFH hρ₁ hρ₂

end GlobalTheory.CompanionTheory.QuotNorm

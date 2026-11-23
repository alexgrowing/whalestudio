import Mathlib

open MeasureTheory

namespace GlobalTheory

theorem abs_integral_sub_const_mul_le_of_split :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (M : Set X) (K : X → ℝ) (nr fr : X → ENNReal) (c a b e : ℝ), MeasurableSet M → Integrable K μ → (∀ x, 0 ≤ K x) → Measurable nr → 0 ≤ c → 0 ≤ a → 0 ≤ b → 0 ≤ e → (∀ x ∈ M, ENNReal.ofReal |K x - c| ≤ nr x + fr x) → ∫⁻ x in M, nr x ∂μ ≤ ENNReal.ofReal a → ∫⁻ x in M, fr x ∂μ ≤ ENNReal.ofReal b → ∫⁻ x in Mᶜ, ENNReal.ofReal (K x) ∂μ ≤ ENNReal.ofReal e → |∫ x, K x ∂μ - c * (μ Set.univ).toReal| ≤ a + b + c * (μ Mᶜ).toReal + e := by
  intro X _ μ _ M K nr fr c a b e hM hK hK0 hnr hc ha hb he hpt hna hfb hce
  have hsplit : ∫ x, K x ∂μ = ∫ x in M, K x ∂μ + ∫ x in Mᶜ, K x ∂μ :=
    (integral_add_compl hM hK).symm
  have hmeas : (μ Set.univ).toReal = (μ M).toReal + (μ Mᶜ).toReal := by
    rw [← measure_add_measure_compl hM,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hintM : ∫ x in M, (K x - c) ∂μ = ∫ x in M, K x ∂μ - c * (μ M).toReal := by
    rw [integral_sub hK.integrableOn (integrable_const c), setIntegral_const, smul_eq_mul,
      measureReal_def, mul_comm]

  have h1 : |∫ x in M, (K x - c) ∂μ| ≤ a + b := by
    have hle : ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ENNReal.ofReal (a + b) := by
      calc ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ∫⁻ x in M, (nr x + fr x) ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hM] with x hx
            simpa [Real.norm_eq_abs] using hpt x hx
        _ = ∫⁻ x in M, nr x ∂μ + ∫⁻ x in M, fr x ∂μ := lintegral_add_left hnr _
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add hna hfb
        _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
    have hn := norm_integral_le_lintegral_norm (μ := μ.restrict M) (fun x => K x - c)
    rw [Real.norm_eq_abs] at hn
    exact hn.trans (ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hb) hle)

  have h2 : ∫ x in Mᶜ, K x ∂μ ≤ e := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hK0)
      hK.integrableOn.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal he hce
  have h3 : 0 ≤ ∫ x in Mᶜ, K x ∂μ := integral_nonneg fun x => hK0 x
  have h4 : 0 ≤ c * (μ Mᶜ).toReal := mul_nonneg hc ENNReal.toReal_nonneg
  have key : ∫ x, K x ∂μ - c * (μ Set.univ).toReal =
      ∫ x in M, (K x - c) ∂μ + (∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal) := by
    rw [hsplit, hmeas, hintM]; ring
  rw [key]
  calc _ ≤ |∫ x in M, (K x - c) ∂μ| + |∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal| := abs_add_le _ _
    _ ≤ (a + b) + (c * (μ Mᶜ).toReal + e) := by
        gcongr
        rw [abs_le]; constructor <;> linarith
    _ = a + b + c * (μ Mᶜ).toReal + e := by ring

end GlobalTheory

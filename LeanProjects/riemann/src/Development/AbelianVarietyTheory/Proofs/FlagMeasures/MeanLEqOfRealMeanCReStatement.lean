import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanLEqOfRealMeanCRe
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanL_tsum_ofReal_eq_ofReal_re_meanC : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (ι : Type) [Countable ι] (f : ι → G → ℝ), (∀ i, Measurable (f i)) → (∀ i h, 0 ≤ f i h) → μ 𝓕 < ⊤ → ∫⁻ h in 𝓕, ∑' i, ‖((f i h : ℝ) : ℂ)‖ₑ ∂μ < ⊤ → meanL μ 𝓕 (fun h => ∑' i, ENNReal.ofReal (f i h)) = ENNReal.ofReal (meanC μ 𝓕 (fun h => ∑' i, ((f i h : ℝ) : ℂ))).re := by
  first | exact @GlobalTheory.meanL_eq_ofReal_meanC_re | exact GlobalTheory.meanL_eq_ofReal_meanC_re | (intros; apply GlobalTheory.meanL_eq_ofReal_meanC_re <;> assumption)

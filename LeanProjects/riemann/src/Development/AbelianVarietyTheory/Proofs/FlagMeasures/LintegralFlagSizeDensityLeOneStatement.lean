import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagSizeDensityLeOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagSizeDensity_le_one : ∀ (n f a : ℕ) (j : Fin a → ℕ), 1 ≤ f → (∀ i, 1 ≤ j i) → 2 * ∑ i, j i + 1 ≤ n → ∫⁻ τ in simplexH a, ENNReal.ofReal (dens n f j τ) ≤ 1 := by
  first | exact @GlobalTheory.DensityIntegral.lintegral_dens_le_one | exact GlobalTheory.DensityIntegral.lintegral_dens_le_one | (intros; apply GlobalTheory.DensityIntegral.lintegral_dens_le_one <;> assumption)

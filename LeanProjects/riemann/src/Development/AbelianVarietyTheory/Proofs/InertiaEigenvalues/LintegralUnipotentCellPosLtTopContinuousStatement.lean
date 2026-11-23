import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CellDec
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 E))) (𝓕 : Set (GA E n)), IsFundamentalDomain (NE E n) 𝓕 μ → ∀ B : ℝ → GA E n → ℝ, Continuous (Function.uncurry B) → (∀ x g, 0 ≤ B x g) → (∀ x, 0 < B x 1) → (∀ x, ∀ u ∈ NA E n, ∀ g, B x (u * g) = B x g) → (∃ K : Set (GA E n), IsCompact K ∧ ∀ x g, g ∈ C0 E n S → B x g ≠ 0 → ∃ u ∈ NA E n, u * g ∈ K) → (∀ x, 0 < ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ ∧ ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ < ⊤) ∧ Continuous fun x => (∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ).toReal := by
  first | exact @GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | exact GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | (intros; apply GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous <;> assumption)

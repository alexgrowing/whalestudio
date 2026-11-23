import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | exact GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | (intros; apply GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero <;> assumption)

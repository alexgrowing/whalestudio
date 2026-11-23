import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransform
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unipotentColumnWhittakerTransform : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_colT_good | exact GlobalTheory.CuspGeneric.continuous_colT_good | (intros; apply GlobalTheory.CuspGeneric.continuous_colT_good <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandValuesShift
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_values_shift : ∀ (n : ℕ) (χ : Fin n → ℂ), (∀ (t : ℂ) (k : ℕ), gelfVal (fun a => χ a + t) k = ∑ j ∈ range (k + 1), (k.choose j : ℂ) * t ^ (k - j) * gelfVal χ j) ∧ gelfVal χ 0 = n ∧ ∀ (s : Equiv.Perm (Fin n)) (k : ℕ), gelfVal (χ ∘ s) k = gelfVal χ k := by
  first | exact @GlobalTheory.GelfValSym.gelfVal_shift_symm | exact GlobalTheory.GelfValSym.gelfVal_shift_symm | (intros; apply GlobalTheory.GelfValSym.gelfVal_shift_symm <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraParameterDescent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_parameter_descent : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsParU lam → ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ IsParS (fun a => lam a - (m : ℝ) / n) ∧ (IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsHCU ε lam π) := by
  first | exact @GlobalTheory.SUtoU.extension_main | exact GlobalTheory.SUtoU.extension_main | (intros; apply GlobalTheory.SUtoU.extension_main <;> assumption)

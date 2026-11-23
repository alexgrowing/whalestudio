import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandOperatorExtension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f ∧ ∀ (k : ℕ) (z : ℂ), ‖z‖ = 1 → ∀ g ∈ SUset ε, gelf ε k f (z • g) = z ^ m * (((m : ℂ) / n) ^ (k + 1) * n * f' g + ∑ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) * gelfS ε j f' g) := by
  first | exact @GlobalTheory.GelfCentral.gelf_central | exact GlobalTheory.GelfCentral.gelf_central | (intros; apply GlobalTheory.GelfCentral.gelf_central <;> assumption)

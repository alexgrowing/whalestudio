import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfinitesimalCharacterExtension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → ∀ χ : Fin n → ℂ, HasInfCharS ε χ π' → HasInfChar ε (fun a => χ a + (m : ℂ) / n) π := by
  first | exact @GlobalTheory.infChar_of_ext | exact GlobalTheory.infChar_of_ext | (intros; apply GlobalTheory.infChar_of_ext <;> assumption)

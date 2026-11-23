import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationOfSpecialUnitary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_of_special_unitary : ∀ (n : ℕ), 1 ≤ n → ∀ ε : Fin n → Bool, ClassS ε → ClassF ε := by
  first | exact @GlobalTheory.SUtoU.classF_of_classS | exact GlobalTheory.SUtoU.classF_of_classS | (intros; apply GlobalTheory.SUtoU.classF_of_classS <;> assumption)

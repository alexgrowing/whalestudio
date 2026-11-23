import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationUnitaryOfFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_unitary_of_full : ∀ n : ℕ, (∀ ε : Fin n → Bool, ClassF ε) → ClassU n := by
  first | exact @GlobalTheory.DSSU.classU_of_classF | exact GlobalTheory.DSSU.classU_of_classF | (intros; apply GlobalTheory.DSSU.classU_of_classF <;> assumption)

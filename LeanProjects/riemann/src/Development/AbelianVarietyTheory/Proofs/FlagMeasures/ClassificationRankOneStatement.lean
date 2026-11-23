import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationRankOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_rank_one : (∀ ε : Fin 1 → Bool, ClassS ε) ∧ ClassU 0 := by
  first | exact @GlobalTheory.DSSU.Triv.classS_one_classU_zero | exact GlobalTheory.DSSU.Triv.classS_one_classU_zero | (intros; apply GlobalTheory.DSSU.Triv.classS_one_classU_zero <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_tensorInj | exact GlobalTheory.MemLoc.regular_of_tensorInj | (intros; apply GlobalTheory.MemLoc.regular_of_tensorInj <;> assumption)

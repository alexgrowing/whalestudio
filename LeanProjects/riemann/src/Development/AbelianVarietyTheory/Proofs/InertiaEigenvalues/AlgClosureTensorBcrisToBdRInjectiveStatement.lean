import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective : ∀ (l : ℕ) [Fact l.Prime] (c : Core l), c.TensorInj := by
  first | exact @GlobalTheory.MemLoc.TensorInj.tensorInj | exact GlobalTheory.MemLoc.TensorInj.tensorInj | (intros; apply GlobalTheory.MemLoc.TensorInj.tensorInj <;> assumption)

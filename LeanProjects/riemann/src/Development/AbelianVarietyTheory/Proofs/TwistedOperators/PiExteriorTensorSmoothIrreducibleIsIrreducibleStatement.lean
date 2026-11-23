import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k)), (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).IsIrreducible := by
  first | exact @GlobalTheory.ExtTensorIrr.piTensor_isIrreducible | exact GlobalTheory.ExtTensorIrr.piTensor_isIrreducible | (intros; apply GlobalTheory.ExtTensorIrr.piTensor_isIrreducible <;> assumption)

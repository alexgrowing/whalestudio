import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquiv
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_jacquet_functor_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), Nonempty ((GlobalTheory.SmGL.relJac f (GlobalTheory.SmGL.piTensor ρ)).Equiv (GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.jac (f i) (ρ i))) := by
  first | exact @GlobalTheory.RelJacTensor.relJac_piTensor_equiv | exact GlobalTheory.RelJacTensor.relJac_piTensor_equiv | (intros; apply GlobalTheory.RelJacTensor.relJac_piTensor_equiv <;> assumption)

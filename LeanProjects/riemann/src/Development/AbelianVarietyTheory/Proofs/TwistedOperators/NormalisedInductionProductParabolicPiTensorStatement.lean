import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_induction_product_parabolic_piTensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (Z : α → Type) [∀ i, AddCommGroup (Z i)] [∀ i, Module ℂ (Z i)] (σ : ∀ i, Representation ℂ (GlobalTheory.SmGL.Levi k (c i)) (Z i)), (∀ i, GlobalTheory.PRep.IsSmooth (σ i)) → Nonempty ((GlobalTheory.SmGL.relInd f (GlobalTheory.SmGL.piTensor σ)).Equiv (GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.parInd (f i) (σ i))) := by
  first | exact @GlobalTheory.SmGL.IndTensor.relInd_piTensor | exact GlobalTheory.SmGL.IndTensor.relInd_piTensor | (intros; apply GlobalTheory.SmGL.IndTensor.relInd_piTensor <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_action_factor_through_tensor_character : ∀ (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O] [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X] [Module k X] (σX : O →+* Module.End k X), (∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) → ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  first | (exact @GlobalTheory.tensor_action_factors) | (exact GlobalTheory.tensor_action_factors) | (intros; apply GlobalTheory.tensor_action_factors  <;> assumption)

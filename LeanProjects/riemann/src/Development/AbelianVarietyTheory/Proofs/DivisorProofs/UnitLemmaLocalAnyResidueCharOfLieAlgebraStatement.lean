import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaLocalAnyResidueCharOfLieAlgebra
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_local_anyResidueChar_of_lieAlgebra : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any | exact GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any | (intros; apply GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any <;> assumption)

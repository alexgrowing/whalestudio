import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgebraProductIdentity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involutive_algebra_product_identity : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → (∃ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A), e * e = e ∧ e + (B₁.prod B₂).σ e = 1) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.Swap.identity_of_swap | exact GlobalTheory.UnitLemma.Swap.identity_of_swap | (intros; apply GlobalTheory.UnitLemma.Swap.identity_of_swap <;> assumption)

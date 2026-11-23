import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgIdentityProdOfUnitResultant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involutiveAlg_identity_prod_of_unit_resultant : ∀ (K : UQ) (B₁ B₂ C₁ C₂ : InvAlg K), ((B₁.P * B₂.P) * (C₁.P * C₂.P)).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsIntegral K.O C₁.g → IsIntegral K.O C₂.g → val K.O (resultant (B₁.P * B₂.P) (C₁.P * C₂.P)) = 0 → InvAlg.Identity B₁ B₂ → InvAlg.Identity C₁ C₂ → InvAlg.Identity (B₁.prod C₁) (B₂.prod C₂) := by
  first | exact @GlobalTheory.UnitLemma.ProdId.identity_prod | exact GlobalTheory.UnitLemma.ProdId.identity_prod | (intros; apply GlobalTheory.UnitLemma.ProdId.identity_prod <;> assumption)

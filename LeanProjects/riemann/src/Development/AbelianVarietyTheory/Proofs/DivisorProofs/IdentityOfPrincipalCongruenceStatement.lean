import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityOfPrincipalCongruence
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invAlg_identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a → ∀ B₁ B₂ : InvAlg K, (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 → (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | exact GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | (intros; apply GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence <;> assumption)

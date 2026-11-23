import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropFTopHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
open GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_pi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  first | (exact @GlobalTheory.EtC.GmStep.laurentPi_bijective) | (exact GlobalTheory.EtC.GmStep.laurentPi_bijective) | (intros; apply GlobalTheory.EtC.GmStep.laurentPi_bijective  <;> assumption)

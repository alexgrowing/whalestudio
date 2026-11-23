import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosurePiOfEtale
import Mathlib
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_pi_of_etale : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  first | (exact @GlobalTheory.PiClosure.etale_integralClosure_pi) | (exact GlobalTheory.PiClosure.etale_integralClosure_pi) | (intros; apply GlobalTheory.PiClosure.etale_integralClosure_pi  <;> assumption)

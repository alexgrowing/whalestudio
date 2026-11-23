import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLiftOfRingAutomorphism
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_lift_of_ring_automorphism : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (γ : O ≃+* O), ∃ Γ : PreTilt O p ≃+* PreTilt O p, (∀ x, (Γ x).untilt = γ x.untilt) ∧ ∀ a : Ainf p O, WittVector.fontaineTheta O p (WittVector.map (Γ : PreTilt O p →+* PreTilt O p) a) = γ (WittVector.fontaineTheta O p a) := by
  first | exact @GlobalTheory.DetInv.ringEquiv_tilt_theta | exact GlobalTheory.DetInv.ringEquiv_tilt_theta | (intros; apply GlobalTheory.DetInv.ringEquiv_tilt_theta <;> assumption)

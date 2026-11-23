import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_quasiLogarithm_along_pdThickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (g : MvPowerSeries (Fin d) C) (w : Fin d → B), QL (fun i => map θ (μ i)) ⊤ g → (∀ i, lin g i = algebraMap O C (θ (w i))) → ∃ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f ∧ map Θ f = g ∧ ∀ i, lin f i = algebraMap B Q (w i) := by
  first | exact @GlobalTheory.QLog.KLift.lift_quasiLog | exact GlobalTheory.QLog.KLift.lift_quasiLog | (intros; apply GlobalTheory.QLog.KLift.lift_quasiLog <;> assumption)

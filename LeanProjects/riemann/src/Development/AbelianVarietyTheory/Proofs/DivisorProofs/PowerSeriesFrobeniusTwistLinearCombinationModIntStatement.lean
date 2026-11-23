import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModInt
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B), (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) → ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  first | exact @GlobalTheory.FrobStep.frob_comb_step | exact GlobalTheory.FrobStep.frob_comb_step | (intros; apply GlobalTheory.FrobStep.frob_comb_step <;> assumption)

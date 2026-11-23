import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIff
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_power_unramified_iff : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R) (P : Ideal R), P.IsMaximal → (p : R) ∈ P → (P.map w.toOw).IsMaximal → (∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) → (∃ a b : ℕ, 0 < b ∧ (differentIdeal ℤ R).map w.toOw ^ b = Ideal.span {(p : w.Ow) ^ a}) ∧ (w.IsUnramified ↔ (differentIdeal ℤ R).map w.toOw = ⊤) := by
  first | exact @GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff | exact GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff | (intros; apply GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff <;> assumption)

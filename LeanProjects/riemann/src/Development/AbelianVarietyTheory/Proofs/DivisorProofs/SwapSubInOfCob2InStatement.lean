import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSubInOfCob2In
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_sub_in_of_cob2_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N J : Ideal B), N ≤ J → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) Q, (IsLaw μ ∨ DIn N c) → constantCoeff c = 0 → (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → In N (swap c - c) → ∃ g : MvPowerSeries (Fin d) Q, constantCoeff g = 0 ∧ lin g = 0 ∧ (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α g = algebraMap B Q b) ∧ In N (c - cob1 (up Q μ) g) := by
  first | exact @GlobalTheory.symmetric_cocycle_is_coboundary_mod | exact GlobalTheory.symmetric_cocycle_is_coboundary_mod | (intros; apply GlobalTheory.symmetric_cocycle_is_coboundary_mod <;> assumption)

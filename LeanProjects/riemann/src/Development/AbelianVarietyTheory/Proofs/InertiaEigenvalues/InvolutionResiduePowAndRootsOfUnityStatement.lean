import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionResiduePowAndRootsOfUnity
import Mathlib
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_residue_pow_and_roots_of_unity : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ), Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) → (∃ x, residue S (τ x) ≠ residue S x) → (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  first | exact @GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | exact GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | (intros; apply GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots <;> assumption)

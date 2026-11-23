import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyOpen
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)), (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) → (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) → IsOpen U := by
  first | exact @GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure | exact GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure | (intros; apply GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure <;> assumption)

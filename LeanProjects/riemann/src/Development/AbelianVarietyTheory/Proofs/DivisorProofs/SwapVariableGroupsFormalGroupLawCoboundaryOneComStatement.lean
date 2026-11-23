import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapVariableGroupsFormalGroupLawCoboundaryOneCom
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swapVariableGroups_formalGroupLawCoboundaryOne_comm : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q, swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  first | exact @GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq | exact GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq | (intros; apply GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq <;> assumption)

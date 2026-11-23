import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEdgesMemOfCoboundaryTwoCoeffsInIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_edges_mem_of_coboundaryTwo_coeffsInIdeal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), constantCoeff c = 0 → In N (cob2 (up Q μ) c) → ∀ a : Fin d →₀ ℕ, (∃ b ∈ N, coeff (Finsupp.sumElim a 0) c = algebraMap B Q b) ∧ (∃ b ∈ N, coeff (Finsupp.sumElim 0 a) c = algebraMap B Q b) := by
  first | exact @GlobalTheory.CobEdges.coeff_edges_mem | exact GlobalTheory.CobEdges.coeff_edges_mem | (intros; apply GlobalTheory.CobEdges.coeff_edges_mem <;> assumption)

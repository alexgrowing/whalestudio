import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariant_derivation_monomial : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (α : Fin d →₀ ℕ), constantCoeff ((invDer μ u)^[α.degree] (monomial α (1 : R))) = (α.degree.factorial : R) * ∏ i, u i ^ α i := by
  first | exact @GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial | exact GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial | (intros; apply GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial <;> assumption)

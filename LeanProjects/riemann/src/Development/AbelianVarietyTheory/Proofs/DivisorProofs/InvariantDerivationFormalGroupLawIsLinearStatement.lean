import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinear
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ u : Fin d → R, (∀ F G : MvPowerSeries (Fin d) R, invDer μ u (F + G) = invDer μ u F + invDer μ u G) ∧ (∀ (a : R) (F : MvPowerSeries (Fin d) R), invDer μ u (a • F) = a • invDer μ u F) ∧ ∀ a : R, invDer μ u (C a) = 0 := by
  first | exact @GlobalTheory.LawDer.Linear.invDer_linear | exact GlobalTheory.LawDer.Linear.invDer_linear | (intros; apply GlobalTheory.LawDer.Linear.invDer_linear <;> assumption)

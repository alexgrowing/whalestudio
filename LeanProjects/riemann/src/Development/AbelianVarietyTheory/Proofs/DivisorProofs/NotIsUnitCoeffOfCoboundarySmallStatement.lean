import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitCoeffOfCoboundarySmall
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ t : MvPowerSeries (Fin d) O, (∀ i, ¬IsUnit (lin t i)) → (∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t))) → ∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t) := by
  first | exact @GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small | exact GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small | (intros; apply GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small <;> assumption)

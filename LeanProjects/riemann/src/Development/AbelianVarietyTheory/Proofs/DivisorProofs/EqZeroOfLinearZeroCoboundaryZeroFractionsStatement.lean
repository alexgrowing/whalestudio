import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractions
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ R : MvPowerSeries (Fin d) E, lin R = 0 → cob1 (up E μ) R = 0 → R = 0 := by
  first | exact @GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions | exact GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions | (intros; apply GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions <;> assumption)

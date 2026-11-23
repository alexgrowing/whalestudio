import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapPowerSeriesFamilyToFractions_formalGroupLawNatMultiple : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  first | exact @GlobalTheory.QLog.up_nmul | exact GlobalTheory.QLog.up_nmul | (intros; apply GlobalTheory.QLog.up_nmul <;> assumption)

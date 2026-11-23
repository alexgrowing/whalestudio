import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentEqZeroOfFormalGroupLawCoboundaryOneEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C), constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  first | exact @GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | exact GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero <;> assumption)

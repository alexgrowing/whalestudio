import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTate
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f l → ∀ t : G.Tate, c.HasPeriod (RingHom.id O) t f (l (hodgeTate G t)) := by
  first | exact @GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | exact GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | (intros; apply GlobalTheory.QLogPeriod.hasPeriod_hodgeTate <;> assumption)

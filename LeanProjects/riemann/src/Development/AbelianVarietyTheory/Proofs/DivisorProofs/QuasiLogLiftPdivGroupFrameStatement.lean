import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogLiftPdivGroupFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_log_lift_pdiv_group_frame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f → QL μ' ⊤ (frob p F.s f) ∧ (In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) → QL μ' (Ideal.span {(p : F.B)}) (frob p F.s f)) := by
  first | exact @GlobalTheory.QLog.ql_frob | exact GlobalTheory.QLog.ql_frob | (intros; apply GlobalTheory.QLog.ql_frob <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvNormOpEqNrm
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ev_normOp_eq_nrm_ev_succ : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m), IsAdicComplete (Ideal.span {(p : R)}) R → ∀ h : PowerSeries R, ev R p m (normOp p h) = nrm p m hm (ev R p (m + 1) h) := by
  first | exact @GlobalTheory.Col.ev_normOp_eq_nrm | exact GlobalTheory.Col.ev_normOp_eq_nrm | (intros; apply GlobalTheory.Col.ev_normOp_eq_nrm <;> assumption)

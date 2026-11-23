import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedShift_fixed_ratio_const_domain : ∀ {B G : Type} [CommRing B] [IsDomain B] [CharZero B] (σ : G → B ≃+* B) (τ : G → B),
  (∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g) →
  ∀ p q : Polynomial B, q ≠ 0 →
  (∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) = (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) →
  ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  first | exact @GlobalTheory.InvRatFun.fixed_ratio_const | exact GlobalTheory.InvRatFun.fixed_ratio_const | (intros; apply GlobalTheory.InvRatFun.fixed_ratio_const <;> assumption)

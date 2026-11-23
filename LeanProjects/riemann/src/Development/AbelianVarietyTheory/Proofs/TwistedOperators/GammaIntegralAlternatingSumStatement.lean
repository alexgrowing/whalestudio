import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GammaIntegralAlternatingSum
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_integral_alternating_sum : ∀ (k : ℕ) (P R : Finset (SV k)) (Y : A0 k), IsPar P → R ⊆ P → Integrable (fun H : aMQ (aP P) R => gamP P R Y H) ∧ ∀ l ∈ generic k, ∫ H : aMQ (aP P) R, eL l H * gamP P R Y H = ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsHat P S l * eps S R l * eL l (pr S Y - pr R Y) := by
  first | exact @GlobalTheory.Chamber.integrable_gamma_and_integral_exp_mul | exact GlobalTheory.Chamber.integrable_gamma_and_integral_exp_mul | (intros; apply GlobalTheory.Chamber.integrable_gamma_and_integral_exp_mul <;> assumption)

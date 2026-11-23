import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExponentialGammaIntegralFormula
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_gamma_integral_formula : ∀ (k : ℕ) (P R : Finset (SV k)) (Y : A0 k), IsPar P → R ⊆ P → ∃ m : A0 k, ∀ t : ℝ, 0 < t → ∀ l : A0 k, Integrable (fun H : aMQ (aP P) R => eLC l (t • m) H * gamP P R Y H) ∧ ∫ H : aMQ (aP P) R, eLC l (t • m) H * gamP P R Y H = ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsOfC (P \ S) (wt S) l (t • m) * epsOfC (S \ R) (rt S) l (t • m) * eLC l (t • m) (pr S Y - pr R Y) := by
  first | exact @GlobalTheory.Chamber.DampedCone.damped | exact GlobalTheory.Chamber.DampedCone.damped | (intros; apply GlobalTheory.Chamber.DampedCone.damped <;> assumption)

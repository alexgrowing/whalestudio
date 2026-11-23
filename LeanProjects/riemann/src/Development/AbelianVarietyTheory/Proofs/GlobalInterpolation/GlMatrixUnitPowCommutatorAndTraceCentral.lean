import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CommPowEntry
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem glRel_pow_comm : ∀ (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlRel E → ∀ k : ℕ, (∀ a b c d, E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else 0) - (if d = a then (E ^ k) c b else 0)) ∧ ∀ a b, E a b * (E ^ k).trace = (E ^ k).trace * E a b := by
  first
  | exact @_root_.GlobalTheory.CommutatorPowerEntry.main
  | exact _root_.GlobalTheory.CommutatorPowerEntry.main
  | (apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutatorPowerEntry.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutatorPowerEntry.main ..)

end GlobalTheory.Alc

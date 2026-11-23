import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylEqBotOfNotAntitone
import Mathlib
import Formalism.GradedWeylDivisibility.StatementA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_eq_bot_of_not_antitone' : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ), ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  first | exact @GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone | exact GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone | (intros; apply GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone <;> assumption)

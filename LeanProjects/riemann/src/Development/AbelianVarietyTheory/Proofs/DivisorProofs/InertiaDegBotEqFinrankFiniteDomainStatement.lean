import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaDegBotEqFinrankFiniteDomain
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaDeg_bot_eq_finrank_finite_domain : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by
  first | exact @GlobalTheory.inertiaDeg_bot_eq_finrank | exact GlobalTheory.inertiaDeg_bot_eq_finrank | (intros; apply GlobalTheory.inertiaDeg_bot_eq_finrank <;> assumption)

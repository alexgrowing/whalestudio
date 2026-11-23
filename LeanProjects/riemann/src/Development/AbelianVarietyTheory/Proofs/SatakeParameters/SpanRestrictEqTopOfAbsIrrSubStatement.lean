import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), AbsIrrSub ρ W → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub <;> assumption)

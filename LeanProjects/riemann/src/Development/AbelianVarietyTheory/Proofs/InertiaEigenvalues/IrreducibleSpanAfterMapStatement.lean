import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_span_after_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), W ≠ ⊥ → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  first | exact @GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top | exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top | (intros; apply GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top <;> assumption)

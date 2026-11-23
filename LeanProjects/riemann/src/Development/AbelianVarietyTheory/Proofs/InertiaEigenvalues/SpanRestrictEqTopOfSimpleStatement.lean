import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRestrictEqTopOfSimple
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_restrict_eq_top_of_simple : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V), AbsIrrDistinct ρ → ∀ (W : Submodule k V) (hW : Stable ρ W), W ≠ ⊥ → (∀ U : Submodule k V, U ≤ W → Stable ρ U → U = ⊥ ∨ U = W) → Submodule.span k (Set.range fun g => (ρ g).restrict (hW g)) = ⊤ := by
  first | exact @GlobalTheory.Proof.span_restrict_eq_top_of_simple.span_restrict_eq_top_of_irreducible | exact GlobalTheory.Proof.span_restrict_eq_top_of_simple.span_restrict_eq_top_of_irreducible | (intros; apply GlobalTheory.Proof.span_restrict_eq_top_of_simple.span_restrict_eq_top_of_irreducible <;> assumption)

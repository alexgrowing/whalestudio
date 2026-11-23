import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismIndecomposableNilpotentOrBijective
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective : ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) → ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  first | exact @GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | exact GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | (intros; apply GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorClosedImmersionOfLocallyOnSource
import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source : ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z), (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) → ∃ z : Y ⟶ A, z ≫ a = g := by
  first | exact @GlobalTheory.exists_factor_closedImmersion_of_locally | exact GlobalTheory.exists_factor_closedImmersion_of_locally | (intros; apply GlobalTheory.exists_factor_closedImmersion_of_locally <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionLiftUnits
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_function_lift_units : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (U V : Type) [CommGroup U] [CommGroup V] (e : U →* V), Function.Injective e → ∀ a : X → V, (∀ x y w : X, ∃ u : U, a (x + y + w) * a x * a y * a w = e u * (a (x + y) * a (x + w) * a (y + w))) → (∀ x : X, ∃ u : U, a (-x) = e u * a x) → ∃ c : X → V, (∀ x y w : X, c (x + y + w) * c x * c y * c w = c (x + y) * c (x + w) * c (y + w)) ∧ (∀ x : X, c (-x) = c x) ∧ ∀ x : X, ∃ u : U, c x * a x = e u := by
  first | exact @GlobalTheory.exists_even_cube_correction | exact GlobalTheory.exists_even_cube_correction | (intros; apply GlobalTheory.exists_even_cube_correction <;> assumption)

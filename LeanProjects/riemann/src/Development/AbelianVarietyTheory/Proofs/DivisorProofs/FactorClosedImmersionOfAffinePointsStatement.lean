import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePoints
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_affine_points : ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X), (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) → ∃ z : T ⟶ Z, z ≫ i = g := by
  first | (exact @GlobalTheory.factor_closedImmersion_of_affine_points) | (exact GlobalTheory.factor_closedImmersion_of_affine_points) | (intros; apply GlobalTheory.factor_closedImmersion_of_affine_points <;> assumption)

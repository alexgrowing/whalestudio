import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAffineOpenUnits
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_affine_open_units : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))), Flat s →
    ∀ (W : M.Opens), IsAffineOpen W → Module.Flat ℤ Γ(M, W) ∧ IsUnit ((N : ℤ) : Γ(M, W)) := by
  first | exact @GlobalTheory.flat_and_isUnit_sections_of_flat_over_away | exact GlobalTheory.flat_and_isUnit_sections_of_flat_over_away | (intros; apply GlobalTheory.flat_and_isUnit_sections_of_flat_over_away <;> assumption)

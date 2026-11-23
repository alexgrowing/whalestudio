import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] (g : Sp Ω ⟶ Sp R), (∀ w, g w = closedPoint R) → ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  first | exact @GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | exact GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | (intros; apply GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint <;> assumption)

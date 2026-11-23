import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists : ∀ (K : Type) [Field K] (X : Over (Sp K)) [GrpObj X], IsAbelianScheme X → ∃ g : ℕ, SmoothOfRelativeDimension g X.hom := by
  first | (exact @GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme) | (exact GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme) | (intros; apply GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme  <;> assumption)

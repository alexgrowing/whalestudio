import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dimension_of_dominant_flat_cover : ∀ (k : Type) [CommRing k] (Y Z : Scheme.{0}) [IsIntegral Y] [IsIntegral Z] (p : Y ⟶ Sp k) (q : Z ⟶ Sp k) (D : ℕ), IsArithVar p D → IsProjOver q → Flat (q ≫ spMap (Int.castRingHom k)) → ∀ g : Z ⟶ Y, g ≫ p = q → g (genericPoint Z) = genericPoint Y → g.residueDegree (genericPoint Z) ≠ 0 → topologicalKrullDim Z = (D + 1 : ℕ) := by
  first | exact @GlobalTheory.DimCover.topologicalKrullDim_eq | exact GlobalTheory.DimCover.topologicalKrullDim_eq | (intros; apply GlobalTheory.DimCover.topologicalKrullDim_eq <;> assumption)

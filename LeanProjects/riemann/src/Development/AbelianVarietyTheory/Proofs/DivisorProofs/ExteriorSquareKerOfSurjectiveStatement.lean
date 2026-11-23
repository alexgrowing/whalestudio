import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_ιMulti_of_exteriorSquare_map_eq_zero : ∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Surjective p → Function.Exact i p → ∀ t : ⋀[R]^2 M, exteriorPower.map 2 p t = 0 → ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W), t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  first | exact @GlobalTheory.exteriorSquare_ker_of_surjective | exact GlobalTheory.exteriorSquare_ker_of_surjective | (intros; apply GlobalTheory.exteriorSquare_ker_of_surjective <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTwoDiagonalAdditiveEqZeroProjective
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPowerTwo_diagonal_additive_eq_zero_projective : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (t : ⋀[R]^2 M), exteriorPower.map 2 (LinearMap.inl R M M + LinearMap.inr R M M) t = exteriorPower.map 2 (LinearMap.inl R M M) t + exteriorPower.map 2 (LinearMap.inr R M M) t → t = 0 := by
  first | exact @GlobalTheory.WedgeDiag.eq_zero_of_diag_additive | exact GlobalTheory.WedgeDiag.eq_zero_of_diag_additive | (intros; apply GlobalTheory.WedgeDiag.eq_zero_of_diag_additive <;> assumption)

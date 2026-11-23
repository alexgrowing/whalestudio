import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalBijectiveCoefficientsPull1Bijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_bijective_coefficients_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R) (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b)) (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b), (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  first | exact @GlobalTheory.Obs.BC.natCoef_pull1_bijective | exact GlobalTheory.Obs.BC.natCoef_pull1_bijective | (intros; apply GlobalTheory.Obs.BC.natCoef_pull1_bijective <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamHypercohomologyCupAnticomm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeRhamHypercohomologyCup_anticomm : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  first | exact @GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | exact GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | (intros; apply GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap <;> assumption)

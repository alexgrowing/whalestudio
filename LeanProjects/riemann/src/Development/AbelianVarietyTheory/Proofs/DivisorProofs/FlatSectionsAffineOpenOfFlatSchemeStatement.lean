import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatScheme
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme : ∀ (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R'), Flat s' → ∀ U : X'.affineOpens, Module.Flat R' (Sec s' U.1) := by
  first | exact @GlobalTheory.CechDR.flat_sec | exact GlobalTheory.CechDR.flat_sec | (intros; apply GlobalTheory.CechDR.flat_sec <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  first | exact @GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | exact GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | (intros; apply GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait <;> assumption)

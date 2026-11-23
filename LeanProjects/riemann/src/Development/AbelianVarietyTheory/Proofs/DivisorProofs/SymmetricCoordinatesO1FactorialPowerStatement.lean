import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCoordinatesO1FactorialPower
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_coordinates_O1_factorial_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  first | exact @GlobalTheory.UMin.CrdSym.lbIso_symTup | exact GlobalTheory.UMin.CrdSym.lbIso_symTup | (intros; apply GlobalTheory.UMin.CrdSym.lbIso_symTup <;> assumption)

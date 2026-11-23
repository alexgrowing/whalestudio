import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOverProjectiveSpaceProjectiveAmpleTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_over_projectiveSpace_projective_ample_twist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (n k : ℕ) (Z : Scheme.{0}) (p : Z ⟶ PSpace o n), 1 ≤ k → IsFinite p → IsProjOver (p ≫ PSpace.str o n) ∧ (lbPow ((ProjSpace.O1 o n).pull p) k).IsLB ∧ IsAmpleLB (lbPow ((ProjSpace.O1 o n).pull p) k) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ Z), LBIso ((lbPow ((ProjSpace.O1 o n).pull p) k).pull h) (lbPow ((ProjSpace.O1 o n).pull (h ≫ p)) k) := by
  first | exact @GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB | exact GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB | (intros; apply GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantLevelSquareNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstant_levelSquare_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (c : Fin N → K), Odd m → 3 ≤ m → (m : K) ≠ 0 → PolFib G L g x → HasTh G L ρ m x c → ∃ a, c a ≠ 0 := by
  first | exact @GlobalTheory.UMin.ThNe.th_ne_zero | exact GlobalTheory.UMin.ThNe.th_ne_zero | (intros; apply GlobalTheory.UMin.ThNe.th_ne_zero <;> assumption)

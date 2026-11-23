import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L'.IsLB → ρ'.IsGen → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (m m' N N' : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S') (c : Fin N → K) (c' : Fin N' → K), HasTh₂ A L' ρ' m m' x c c' ↔ HasTh₂ G L ρ m m' (x ≫ f) c c' := by
  first | exact @GlobalTheory.UMin.ThMove.hasTh₂_move | exact GlobalTheory.UMin.ThMove.hasTh₂_move | (intros; apply GlobalTheory.UMin.ThMove.hasTh₂_move <;> assumption)

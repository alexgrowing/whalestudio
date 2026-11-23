import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplication
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_origin_germ_of_multiplication : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  first | exact @GlobalTheory.ThetaGerm.germ_origin | exact GlobalTheory.ThetaGerm.germ_origin | (intros; apply GlobalTheory.ThetaGerm.germ_origin <;> assumption)

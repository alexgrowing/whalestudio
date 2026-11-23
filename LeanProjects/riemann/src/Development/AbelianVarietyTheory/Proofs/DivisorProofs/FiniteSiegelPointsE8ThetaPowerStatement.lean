import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSiegelPointsE8ThetaPower
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_siegelPoints_e8ThetaPower : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)), Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} := by
  first | exact @GlobalTheory.SharpFiniteTh.finite_sharpOver | exact GlobalTheory.SharpFiniteTh.finite_sharpOver | (intros; apply GlobalTheory.SharpFiniteTh.finite_sharpOver <;> assumption)

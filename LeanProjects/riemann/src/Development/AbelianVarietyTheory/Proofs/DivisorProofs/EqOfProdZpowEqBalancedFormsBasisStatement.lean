import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowEqBalancedFormsBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_prod_zpow_eq_balancedForms_basis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms H.bar X)) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ X) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ X) a b) → x = y := by
  first | exact @GlobalTheory.BalMono.eq_of_prod_zpow_eq | exact GlobalTheory.BalMono.eq_of_prod_zpow_eq | (intros; apply GlobalTheory.BalMono.eq_of_prod_zpow_eq <;> assumption)

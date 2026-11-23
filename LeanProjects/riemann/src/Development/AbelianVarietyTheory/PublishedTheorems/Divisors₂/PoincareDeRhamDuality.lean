import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def PoincareDeRhamDuality : Prop :=
  ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A →
    IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, GlobalTheory.AbDual.IsDual A B P →
    ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
      LinearMap.IsPerfPair φ ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0

end GlobalTheory.Published

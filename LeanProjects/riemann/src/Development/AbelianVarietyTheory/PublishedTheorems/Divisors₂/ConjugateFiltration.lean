import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def ConjugateFiltration : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (hA : (p : Γ(A.left, ⊤)) = 0) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)
        (spMap (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)) (GlobalTheory.VB.frob A.left p hA)),
      (∀ x ∈ PrimitiveSubmodule A, m.pull x = 0) ∧
      (∃ N : Submodule R (primDR A), IsCompl (Submodule.span R (Set.range m.pull)) N) ∧
      (∀ P : PrimeSpectrum R, Module.rankAtStalk (Submodule.span R (Set.range m.pull)) P = g) ∧
      ∀ (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      ∀ (hB : (p : Γ(B.left, ⊤)) = 0) (n : GrpMor (dp0 R) (𝟙 _) B (dp0 R) (𝟙 _) B (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)
          (spMap (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)) (GlobalTheory.VB.frob B.left p hB)) (P : LB (A ⊗ B).left),
        GlobalTheory.AbDual.IsDual A B P →
      ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
        ∀ (x : HdR A) (y : HdR B), (∀ c, x (m.pull c) = 0) → (∀ c, y (n.pull c) = 0) → φ x y = 0

end GlobalTheory.Published

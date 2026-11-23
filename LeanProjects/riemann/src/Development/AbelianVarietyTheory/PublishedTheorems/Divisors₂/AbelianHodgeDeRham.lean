import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianHodgeDeRham : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    (Module.Finite R (HH1 A.hom) ∧ Module.Projective R (HH1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HH1 A.hom) p = 2 * g) ∧
    (∃ e : ⋀[R]^2 (HH1 A.hom) ≃ₗ[R] HH2 A.hom, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHH A.hom a b) ∧
    (Module.Finite R (GlobForm A.hom) ∧ Module.Projective R (GlobForm A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (GlobForm A.hom) p = g) ∧
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
    (ClosedForm A.hom = ⊤ ∧ Function.Injective (clForm A.hom) ∧ Function.Surjective (toHO1 A.hom)) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
      (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))),
      (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, IsPull1 h.w c (e (1 ⊗ₜ c))) ∧
      (∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, IsPullForm h.w c (e (1 ⊗ₜ c))) ∧
      ∃ e : R' ⊗[R] HO1 A.hom ≃ₗ[R'] HO1 s', ∀ c, IsPullO h.w c (e (1 ⊗ₜ c))

end GlobalTheory.Published

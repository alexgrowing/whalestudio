import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace FubiniStudyChowHeightFormula₂.Hdr

def IsVB (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M

def IsVBRank (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  IsVB R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n

def IsSubbundle {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (F : Submodule R M) (n : ℕ) : Prop :=
  IsVBRank R F n ∧ IsVB R (M ⧸ F)

abbrev Hodge1 {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) : Submodule R (HH1 s) :=
  LinearMap.range (clForm s)

def AbelianDeRhamPage : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    (∃ e : ⋀[R]^2 (HH1 A.hom) ≃ₗ[R] HH2 A.hom, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHH A.hom a b) ∧
    IsVBRank R (HH1 A.hom) (2 * g) ∧
    (ClosedForm A.hom = ⊤ ∧ Function.Injective (clForm A.hom) ∧ IsSubbundle (Hodge1 A.hom) g) ∧
    (Function.Exact (Hodge1 A.hom).subtype (toHO1 A.hom) ∧ Function.Surjective (toHO1 A.hom)) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
      (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))),
      (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, IsPull1 h.w c (e (1 ⊗ₜ c))) ∧
      (∃ e : R' ⊗[R] Hodge1 A.hom ≃ₗ[R'] Hodge1 s', ∀ c : Hodge1 A.hom, IsPull1 h.w c.1 (e (1 ⊗ₜ c)).1) ∧
      ∃ e : R' ⊗[R] HO1 A.hom ≃ₗ[R'] HO1 s', ∀ c, IsPullO h.w c (e (1 ⊗ₜ c))

end FubiniStudyChowHeightFormula₂.Hdr

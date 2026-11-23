import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace AbelianDeRham

theorem bcMor {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)} [GrpObj A]
    {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' (algebraMap R R') (spMap (algebraMap R R')) φ :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) h

def Free : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    AllPrim (dp0 R) (𝟙 _) A ∧
    Module.Finite R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧ Module.Projective R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham (A.hom ≫ 𝟙 _)) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham (A.hom ≫ 𝟙 _)) ≃ₗ[R] SecondDeRham (A.hom ≫ 𝟙 _),
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b

def Hodge : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    LieExact A ∧ (∃ N : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N) ∧
    Module.Finite R (PrimitiveSubmodule A) ∧ Module.Projective R (PrimitiveSubmodule A) ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk (PrimitiveSubmodule A) p = g

def BaseChange : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) [GrpObj A']
      (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ),
      (bcMor h).IsBC ∧ PrimitiveSubmodule A' = Submodule.span R' ((bcMor h).pull '' (PrimitiveSubmodule A))

def Rigid : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left) (h : IsGrpPullback A₀ A (spMap π) i),
      Function.Bijective (liftMor κ h).pull

def Duality : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm R (HdR A),
      IsPolForm (dp0 R) (𝟙 _) A L ψ →
      (∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) ∧
      (ReciprocityTheory.ChartRestriction.G.Out.KTriv A L → LinearMap.IsPerfPair ψ)

end AbelianDeRham

def AbelianDeRham : Prop :=
  AbelianDeRham.Free ∧ AbelianDeRham.Hodge ∧ AbelianDeRham.BaseChange ∧ AbelianDeRham.Rigid ∧
    AbelianDeRham.Duality

namespace AbelianDeRham

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem Free.prim (H : Free) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Module.Finite R (primDR A) ∧ Module.Projective R (primDR A) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (primDR A) p = 2 * g := by
  obtain ⟨h0, h1, h2, h3, -⟩ := H R A g hA hg
  let e : primDR A ≃ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) := LinearEquiv.ofTop _ h0
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm,
    fun p ↦ by rw [Module.rankAtStalk_eq_of_equiv e, h3]⟩

theorem Rigid.crysToDR_bijective (H : Rigid) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {I : Ideal R} {κ : DividedPowers I} (hκ : IsNilDP κ)
    {R₀ : Type} [CommRing R₀] {π : R →+* R₀} (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) :
    Function.Bijective (crysToDR κ h) :=
  (LinearEquiv.ofBijective _ (H R A g hA hg I κ hκ R₀ π hπ hI A₀ i h)).dualMap.bijective

end AbelianDeRham

end GlobalTheory.Published

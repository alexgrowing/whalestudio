import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolQuasiInverse
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

def QuasiInverseR : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      ∀ g : ℕ, IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
      SmoothOfRelativeDimension g B.hom → IsDual A B P → IsDual B A (swap P) → Zarhin.IsPolarisation A B P l →
        ∃ (m : ℕ) (mu : B ⟶ A), 1 ≤ m ∧ IsMonHom mu ∧ l ≫ mu = 𝟙 A ^ m ∧ mu ≫ l = 𝟙 B ^ m

def PolFibreIsogAny : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      ∀ g : ℕ, IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
      SmoothOfRelativeDimension g B.hom → IsDual A B P → IsDual B A (swap P) → Zarhin.IsPolarisation A B P l →
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ Sp R),
        IsFinite ((Over.pullback s).map l).left ∧ Flat ((Over.pullback s).map l).left ∧
          Surjective ((Over.pullback s).map l).left

def KilledAny : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (F : Type) [CommRing F] [Algebra R F]
      (h : sp (R₀ := R) F ⟶ G), IsFinFlatSub G F h →
      ∃ n : ℕ, 0 < n ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (φ : F →ₐ[R] S), (spMap φ ≫ h) ^ n = 1

end PositivityTheory.PrwZar

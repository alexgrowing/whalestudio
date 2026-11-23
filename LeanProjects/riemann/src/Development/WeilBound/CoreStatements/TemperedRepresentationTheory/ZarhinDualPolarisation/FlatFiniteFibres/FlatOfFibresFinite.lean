import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.DualPolarisationOC
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.Tls2.Zar3.Ch1

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

def PolFibreIsog : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → IsDual B A (swap P) →
      Zarhin.IsPolarisation A B P l →
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ Sp R),
        IsFinite ((Over.pullback s).map l).left ∧ Flat ((Over.pullback s).map l).left ∧
          Surjective ((Over.pullback s).map l).left

def FiniteOfFibres : Prop :=
  ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (l : A ⟶ B),
    IsAbelianScheme A → IsAbelianScheme B → IsMonHom l →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ Sp R),
      IsFinite ((Over.pullback s).map l).left ∧ Surjective ((Over.pullback s).map l).left) →
    IsFinite l.left ∧ Surjective l.left

def FlatOfFibresFinite : Prop :=
  ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (f : X ⟶ Y),
    Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ Sp R), Flat ((Over.pullback s).map f).left) →
    Flat f.left

def KernelFinFlat : Prop :=
  ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (l : A ⟶ B),
    IsAbelianScheme A → IsAbelianScheme B → IsMonHom l → IsFinite l.left → Flat l.left →
    ∃ (F : Type) (_ : CommRing F) (_ : Algebra R F) (h : sp (R₀ := R) F ⟶ A), IsFinFlatSub A F h ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
        z ≫ l = 1 ↔ ∃ φ : F →ₐ[R] S, spMap φ ≫ h = z

def KilledCharZero : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (F : Type) [CommRing F] [Algebra R F]
      (h : sp (R₀ := R) F ⟶ G), IsFinFlatSub G F h →
      ∃ n : ℕ, 0 < n ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (φ : F →ₐ[R] S), (spMap φ ≫ h) ^ n = 1

def FactorThroughFF : Prop :=
  ∀ (R : Type) [CommRing R] (A B A' : Over (Sp R)) [GrpObj A] [GrpObj B] [GrpObj A'] (l : A ⟶ B) (f : A ⟶ A'),
    IsMonHom l → IsMonHom f → Flat l.left → Surjective l.left → QuasiCompact l.left →
    (∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A), z ≫ l = 1 → z ≫ f = 1) →
    ∃ g : B ⟶ A', IsMonHom g ∧ l ≫ g = f

def EpiOfFF : Prop :=
  ∀ (R : Type) [CommRing R] (A B A' : Over (Sp R)) (l : A ⟶ B),
    Flat l.left → Surjective l.left → QuasiCompact l.left → ∀ g₁ g₂ : B ⟶ A', l ≫ g₁ = l ≫ g₂ → g₁ = g₂

end PositivityTheory.Tls2.Zar3.Ch1

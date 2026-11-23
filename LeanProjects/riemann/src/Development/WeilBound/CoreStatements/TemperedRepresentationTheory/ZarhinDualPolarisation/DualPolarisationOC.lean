import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Tls2.Zar3

open GlobalTheory.CompanionTheory.Hypotheses₂

def ZarhinStatement0 : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left),
      IsAbelianScheme A → L.IsLB → Out.RelAmple A L →
      ∃ (P : Out.PolAV (Spec (CommRingCat.of R))) (i : A ⟶ P.A) (r : P.A ⟶ A),
        IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 A

def ZarhinSchemeOC : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → IsDual B A (swap P) →
      Zarhin.IsPolarisation A B P l →
        ∃ c : Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left, IsPrincipalPol (G4 (A ⊗ B)) c

def DualIsogenyOC : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → IsDual B A (swap P) →
      Zarhin.IsPolarisation A B P l →
        ∃ (n : ℕ) (l' : B ⟶ A), 0 < n ∧ IsMonHom l' ∧ l ≫ l' = 𝟙 A ^ n ∧ l' ≫ l = 𝟙 B ^ n

def DualPolarisationOC : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B) (l' : B ⟶ A) (n : ℕ),
      IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → IsDual B A (swap P) →
      Zarhin.IsPolarisation A B P l → 0 < n → IsMonHom l' → l ≫ l' = 𝟙 A ^ n → l' ≫ l = 𝟙 B ^ n →
        Zarhin.IsPolarisation B A (swap P) l'

def ZarhinMatrixOC : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B) (l' : B ⟶ A) (n : ℕ),
      IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → IsDual B A (swap P) →
      Zarhin.IsPolarisation A B P l → Zarhin.IsPolarisation B A (swap P) l' → 0 < n →
      l ≫ l' = 𝟙 A ^ n → l' ≫ l = 𝟙 B ^ n →
        ∃ c : Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left, IsPrincipalPol (G4 (A ⊗ B)) c

def SymmetricBundleOC : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
      ∀ c : Pic (A ⊗ A).left, IsPrincipalPol A c →
        ∃ (L : LB A.left) (hL : L.IsLB), Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧
          c = lam (cls L hL) (fst A A) (snd A A)

end PositivityTheory.Tls2.Zar3

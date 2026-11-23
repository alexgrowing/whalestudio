import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

def ZarhinSchemeBi : Prop :=
  ∀ (S : Scheme.{0}) [CompactSpace S] (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B) (g : ℕ),
    IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
      SmoothOfRelativeDimension g B.hom → IsDual A B P → IsDual B A (swap P) →
        GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.IsPolarisation A B P l →
          ∃ c : Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left, IsPrincipalPol (G4 (A ⊗ B)) c

def PolQuasiInverse : Prop :=
  ∀ (S : Scheme.{0}) [CompactSpace S] (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
    IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → IsDual B A (swap P) →
      GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.IsPolarisation A B P l →
        ∃ (m : ℕ) (mu : B ⟶ A), 1 ≤ m ∧ IsMonHom mu ∧ l ≫ mu = 𝟙 A ^ m ∧ mu ≫ l = 𝟙 B ^ m

def prj (G : Over S) : Fin 4 → (G4 G ⟶ G)
  | 0 => fst _ _
  | 1 => snd _ _ ≫ fst _ _
  | 2 => snd _ _ ≫ snd _ _ ≫ fst _ _
  | 3 => snd _ _ ≫ snd _ _ ≫ snd _ _

variable {A B : Over S} [GrpObj A] [GrpObj B]

def zcPair {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y : Over S} (u u' : Y ⟶ G4 (A ⊗ B)) : Pic Y.left :=
  (∑ i, 2 • evc hP (u ≫ prj _ i ≫ fst A B) (u' ≫ prj _ i ≫ fst A B ≫ lm)) +
  (∑ i, ∑ j, α i j • (evc hP (u ≫ prj _ i ≫ fst A B) (u' ≫ prj _ j ≫ snd A B) +
      evc hP (u' ≫ prj _ i ≫ fst A B) (u ≫ prj _ j ≫ snd A B))) +
  (∑ i, 2 • evc hP (u ≫ prj _ i ≫ snd A B ≫ mu) (u' ≫ prj _ i ≫ snd A B ≫ mu ≫ lm))

def zc {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) :
    Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left :=
  zcPair hP lm mu α (fst _ _) (snd _ _)

end PositivityTheory.PrwZar

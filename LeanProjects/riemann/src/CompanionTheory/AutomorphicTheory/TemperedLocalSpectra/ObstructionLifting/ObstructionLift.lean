import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris
  GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.ObstructionTrivialLocus

def KunnethO : Prop :=
  ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)), Flat X.hom → IsSeparated X.hom → QuasiCompact X.hom →
    IsSeparated Y.hom → QuasiCompact Y.hom →
    ∀ (n : ℕ) (a : Fin n → FirstDeRham (X.hom ≫ 𝟙 _)) (b : Fin n → FirstDeRham (Y.hom ≫ 𝟙 _)),
    (CoefMap.restrict (O (dp0 R) ((X ⊗ Y).hom ≫ 𝟙 _)) (IsTriv ((X ⊗ Y).hom ≫ 𝟙 _)).ι).pull2
      (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst X Y) (a k)) (pullOver (dp0 R) (𝟙 _) (snd X Y) (b k))) = 0 →
    ∀ y : FirstCohomStructureSheaf (Y.hom ≫ 𝟙 _) →ₗ[R] R, ∑ k, y (toH1O _ (b k)) • toH1O _ (a k) = 0

def ObstructionLift : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X), Flat s → IsSeparated s →
    ∀ h : IsPullback i s₀ s (spMap π),
    (∀ c₀ : GlobalTheory.CechDR.HO1 s₀, ∃ c : GlobalTheory.CechDR.HO1 s, GlobalTheory.CechDR.IsPullO h.w c c₀) →
    ∀ (m : IsMor (dp0 R) s κ (s₀ ≫ spMap π) (RingHom.id R) i) (L₀ : LB X₀), L₀.IsLB →
    ∀ z : SecondDeRham s, IsChern κ (s₀ ≫ spMap π) L₀ (m.pull2 z) →
    (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull2 z = 0 →
    ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀

def BirigLift : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀]
    (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left) (l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left) (g g' : ℕ),
    IsNilDP κ → Function.Surjective π → RingHom.ker π = I → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    ∀ (h : IsGrpPullback A₀ A (spMap π) i) (k : IsGrpPullback B₀ B (spMap π) j),
    l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i → l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j →
    ∀ P₀ : LB (A₀ ⊗ B₀).left, P₀.IsLB → Triv (ev P₀ (1 : B₀ ⟶ A₀) (𝟙 B₀)) → Triv (ev P₀ (𝟙 A₀) (1 : A₀ ⟶ B₀)) →
    ∀ φ₀ : Crys κ (spMap π) A₀ →ₗ[R] Crys κ (spMap π) B₀ →ₗ[R] R, IsCorrForm κ (spMap π) A₀ B₀ P₀ φ₀ →
    (∀ a ∈ liftFil κ h, ∀ b ∈ liftFil κ k, φ₀ a b = 0) →
    ∃ P : LB (A ⊗ B).left, P.IsLB ∧ Triv (ev P (1 : B ⟶ A) (𝟙 B)) ∧ Triv (ev P (𝟙 A) (1 : A ⟶ B)) ∧
      IsAdditive P ∧ IsAdditive (swap P) ∧ LBIso (P.pull l) P₀

def PolIsogeny : Prop :=
  ∀ (R : Type) [CommRing R] (A G : Over (Sp R)) [GrpObj A] [GrpObj G], IsAbelianScheme A → IsAbelianScheme G →
    ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ q : A ⟶ G, IsMonHom q → IsFinite q.left → Flat q.left →
    Surjective q.left → ∃ M : LB G.left, M.IsLB ∧ Out.RelAmple G M

def DualUsed : Prop := DualPol ∧ BirigLift

end CompanionTheory.ObstructionTrivialLocus

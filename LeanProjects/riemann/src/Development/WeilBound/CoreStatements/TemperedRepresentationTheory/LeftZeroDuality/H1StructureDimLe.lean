import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.ObstructionTrivialLocus

def H1StructureDimLe : Prop :=
  ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    Module.Finite k (GlobalTheory.CechDR.HO1 A.hom) ∧ Module.finrank k (GlobalTheory.CechDR.HO1 A.hom) ≤ g

def IsTrivLocus {S : Scheme.{0}} (A : Over S) {Y Z : Over S} (N : LB (A ⊗ Y).left) (i : Z ⟶ Y) : Prop :=
  IsClosedImmersion i.left ∧
    ∀ (T : Over S) (y : T ⟶ Y), Triv (ev N (fst A T) (snd A T ≫ y)) ↔ ∃ z : T ⟶ Z, z ≫ i = y

def TrivLocus : Prop :=
  ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → IsLocallyNoetherian Y.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∃ (Z : Over S) (i : Z ⟶ Y), IsTrivLocus A N i

def FewEquations : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ M : LB A.left, M.IsLB → ∀ I : Ideal R, I ≠ ⊤ →
    (∀ J : Ideal R, Triv (M.pull (pullback.fst A.hom (spMap (Ideal.Quotient.mk J)))) ↔ I ≤ J) →
    ∃ f : Fin g → R, Ideal.span (Set.range f) = I

def CIFlat : Prop :=
  ∀ (R C : Type) [CommRing R] [IsNoetherianRing R] [CommRing C] [Algebra R C] (g : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension g R C → ∀ f : Fin g → C,
    Algebra.QuasiFinite R (C ⧸ Ideal.span (Set.range f)) → Module.Flat R (C ⧸ Ideal.span (Set.range f))

def TrivLocusFlat : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A Y Z : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g Y.hom →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → ∀ i : Z ⟶ Y, IsTrivLocus A N i → LocallyQuasiFinite Z.hom → Flat Z.hom

def LeftFinite {S : Scheme.{0}} (A B : Over S) (P : LB (A ⊗ B).left) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
    Set.Finite {x : Over.mk t ⟶ A | Triv (ev P (fst (Over.mk t) B ≫ x) (snd (Over.mk t) B))}

def LeftZero {S : Scheme.{0}} (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left) : Prop :=
  ∀ (T : Over S) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1

def RightZero {S : Scheme.{0}} (A B : Over S) [GrpObj B] (P : LB (A ⊗ B).left) : Prop :=
  ∀ (T : Over S) (y : T ⟶ B), Triv (ev P (fst A T) (snd A T ≫ y)) → y = 1

structure PreDual {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) : Prop where
  isLB : P.IsLB
  add₁ : IsAdditive P
  add₂ : IsAdditive (swap P)
  right : RightZero A B P
  left : LeftFinite A B P

def PointSurj : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A →
    IsAbelianScheme B → ∀ P : LB (A ⊗ B).left, P.IsLB → IsAdditive P → IsAdditive (swap P) →
    Set.Finite {x : 𝟙_ (Over (Sp k)) ⟶ A | Triv (ev P (toUnit B ≫ x) (𝟙 B))} →
    ∀ M : LB (A ⊗ 𝟙_ (Over (Sp k))).left, M.IsLB → IsAdditive M →
    ∃ y : 𝟙_ (Over (Sp k)) ⟶ B, LBIso M (ev P (fst A _) (snd A _ ≫ y))

def UnivNoeth {S : Scheme.{0}} (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left) : Prop :=
  ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (t : Sp C ⟶ S) (M : LB (A ⊗ Over.mk t).left), M.IsLB →
    IsAdditive M → ∃ x : Over.mk t ⟶ B, LBIso M (ev P (fst A _) (snd A _ ≫ x))

def FinDual : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ),
    IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, PreDual A B P → IsDual A B P

def KFinite : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L →
    LeftFinite A A (abelian₂ A L)

def H90 : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), Flat f → LocallyOfFinitePresentation f → Surjective f →
    ∀ u : Γ(pullback f f, ⊤), IsUnit u →
    (∀ (W : Scheme.{0}) (a b c : W ⟶ X) (hab : a ≫ f = b ≫ f) (hbc : b ≫ f = c ≫ f),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u) →
    ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ t : Γ((f ⁻¹ᵁ U).toScheme, ⊤), IsUnit t ∧
      ∀ (W : Scheme.{0}) (a b : W ⟶ (f ⁻¹ᵁ U).toScheme) (hab : (a ≫ (f ⁻¹ᵁ U).ι) ≫ f = (b ≫ (f ⁻¹ᵁ U).ι) ≫ f),
        a.appTop t = (pullback.lift (a ≫ (f ⁻¹ᵁ U).ι) (b ≫ (f ⁻¹ᵁ U).ι) hab).appTop u * b.appTop t

def RigDescent : Prop :=
  ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    (∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → Triv (ev N (fst A X) (snd A X ≫ q)) → Triv N) ∧
    ∀ M : LB (A ⊗ X).left, M.IsLB → Triv (ev M (1 : X ⟶ A) (𝟙 X)) →
      (∀ (T : Over S) (x x' : T ⟶ X), x ≫ q = x' ≫ q →
        LBIso (ev M (fst A T) (snd A T ≫ x)) (ev M (fst A T) (snd A T ≫ x'))) →
      ∃ N : LB (A ⊗ Y).left, N.IsLB ∧ Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) ∧ LBIso M (ev N (fst A X) (snd A X ≫ q))

def KerOfPullInj : Prop :=
  ∀ (k : Type) [Field k] (A A' : Over (Sp k)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' →
    ∀ q : A ⟶ A', IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left →
    (∀ (T : Over (Sp k)) (N : LB (A' ⊗ T).left), N.IsLB → IsAdditive N →
      Triv (ev N (fst A T ≫ q) (snd A T)) → Triv N) →
    ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ q = 1 → x = 1

def Construct : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L →
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧
      SmoothOfRelativeDimension g B.hom ∧ PreDual A B P

def LeftZeroField : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A →
    IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, PreDual A B P → LeftZero A B P

def LeftZeroNoeth : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ),
    IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, PreDual A B P → LeftZero A B P

def PolModel : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L →
    ∃ (R₀ : Type) (_ : CommRing R₀) (σ : R₀ →+* R) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀) (φ : A.left ⟶ A₀.left)
      (L₀ : LB A₀.left), IsNoetherianRing R₀ ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom ∧
      IsGrpPullback A A₀ (spMap σ) φ ∧ L₀.IsLB ∧ Out.RelAmple A₀ L₀

def KTrivModel : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.KTriv A L →
    ∃ (R₀ : Type) (_ : CommRing R₀) (σ : R₀ →+* R) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀) (φ : A.left ⟶ A₀.left)
      (L₀ : LB A₀.left), IsNoetherianRing R₀ ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom ∧
      IsGrpPullback A A₀ (spMap σ) φ ∧ L₀.IsLB ∧ Out.KTriv A₀ L₀ ∧ LBIso L (L₀.pull φ)

def DualPol : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L →
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧
      SmoothOfRelativeDimension g B.hom ∧ IsDual A B P ∧ IsDual B A (swap P)

def KTrivDual : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.KTriv A L → IsDual A A (abelian₂ A L)

end PositivityTheory.ObstructionTrivialLocus
